open GT

@type t = 
(* Lambda part *)
| Var     of string
| Lam     of string * t
| App     of t * t

(* PCF part *)
| Binop   of string * t * t
| Unop    of string * t
| True
| False
| Const   of int
| If      of t * t * t
| Fix     of t

(* I.A. part *)
| Skip    
| New     of string * t
| Seq     of t * t
| Assn    of string * t
| Deref   of t

(* Concurrent part *)
| Par     of t * t
| Sema    of string * t
| Grab    of t
| Release of t with show

module Lexer =
  struct

    let keywords = [
      "def"; "new"; "in"; "semaphore"; "if"; "then"; "else"; "fi"; "fix"; "grab"; "release"; "true"; "false"; "skip"
    ]

    let r = Ostap.Matcher.Token.repr

    let is_keyword = 
      let module S = Set.Make (String) in
      let s = List.fold_left (fun s k -> S.add k s) S.empty keywords in
      (fun i -> S.mem i s)     

    ostap (
      ident  : x:IDENT =>{not (is_keyword (r x))}=> {r x};
      literal: x:LITERAL {int_of_string (r x)} 
    )

    class t s = 
      let skip = Ostap.Matcher.Skip.create [
                   Ostap.Matcher.Skip.whitespaces " \n\t\r"; 
                   Ostap.Matcher.Skip.nestedComment "(*" "*)";
                   Ostap.Matcher.Skip.lineComment "--"
                 ] 
      in

      let ident   = Re_str.regexp "[a-zA-Z_]\([a-zA-Z_0-9]\)*\\b" in 
      let literal = Re_str.regexp "-?[0-9]+" in
      object (self)
        inherit Ostap.Matcher.t s 
        method skip p coord = skip s p coord
        method getIDENT     = self#get "identifier" ident
        method getLITERAL   = self#get "literal"    literal         
      end

    exception Error of string

    let fromString p s =
      try
        Ostap.Combinators.unwrap (p (new t s)) (fun x -> Checked.Ok x) 
          (fun (Some err) ->
             let [loc, m :: _] = err#retrieve (`First 1) (`Desc) in
             let m =  match m with `Msg m -> m | `Comment (s, _) -> Ostap.Msg.make s [||] loc in
             Checked.Fail [m]
          )
      with Error m -> Checked.Fail [Ostap.Msg.phrase m]

  end

module Parser =
  struct

    let hparse s = 
      let ostap (
        ident: !(Lexer.ident);
        key[name]: @(name ^ "\\b" : name);
        def[env] : 
          -key["def"] -x:ident -"=" -e:apps[env] -key["in"] def[(x, `Def e)::env] 
        | apps[env];
        expr[env]: 
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (let l = 
	        List.map 
		  (fun s -> 
		     ostap(- $(s)), 
		     match s with 
                     | "||" -> fun x y -> Par (x, y) 
                     | ";"  -> fun x y -> Seq (x, y) 
                     | _    -> fun x y -> Binop (s, x, y)
                  ) 
	      in
              Array.map (fun (a, s) -> a, l s) 
              [|
                `Lefta, ["||"];
                `Lefta, [";"];                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     (primary apps env)
        );
	apps[env]: p:expr[env]+ {
	  let h::t = p in
	  List.fold_left (fun acc e -> App (acc, e)) h t
        };
        primary[expr][env]:
          -"(" expr[env] -")"
        | k:!(Lexer.literal) {Const k}
        | key["true" ] {True} 
        | key["false"] {False}
        | key["fix"] e:expr[env] {Fix e}
        | key["if"] c:expr[env] key["then"] e1:expr[env] key["else"] e2:expr[env] key["fi"] {If (c, e1, e2)} 
        | key["new"] n:ident key["in"] e:expr[env] {New (n, e)}
        | key["semaphore"] n:ident key["in"] e:expr[env] {Sema (n, e)}
        | key["grab"] e:expr[env] {Grab e}
        | key["release"] e:expr[env] {Release e}
        | key["skip"] {Skip}
        | "!" e:expr[env] {Deref e}        
        | n:ident s:(-":=" expr[env])? {
            try
              match s with
	      | None ->
                 (match List.assoc n env with
                  | `Def e -> e
                  | `Arg   -> Var n
                 )
	      | Some e -> Assn (n, e)
            with Not_found -> raise (Lexer.Error (Printf.sprintf "undefined identifier %s" n))
          }
        | "\\" ns:ident+ "." e:expr[List.map (fun n -> (n, `Arg)) ns @ env] {
            List.fold_right (fun n acc -> Lam (n, acc)) ns e
          }
      ) in
      def [] s

    let parse s = ostap (hparse -EOF) s
    
  end

let fromFile fname =
  Lexer.fromString Parser.parse (Ostap.Util.read fname)

let _ =
  match fromFile (Array.get Sys.argv 1) with
  | Checked.Ok ast -> 
      Printf.printf "%s\n" (show(t) ast)
  | Checked.Fail [m] -> 
      Printf.eprintf "Syntax error: %s\n" (Ostap.Msg.toString m)
