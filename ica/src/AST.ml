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
      "def"; "new"; "in"; "semaphore"; "if"; "then"; "else"; "fix"; "grab"; "release"; "true"; "false"
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
          -key["def"] -x:ident -"=" -e:expr[env] -key["in"] def[(x, `Def e)::env] 
        | expr[env];
        expr[env]: p:primary[env]+ {
          let t::ts = p in 
          List.fold_left (fun acc e -> App (acc, e)) t ts
        };
        primary[env]:
          -"(" expr[env] -")"
        | n:ident {
            try 
              match List.assoc n env with
              | `Def e -> e
              | `Arg   -> Var n
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
