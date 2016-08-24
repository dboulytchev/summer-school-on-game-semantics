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
| Assn    of t * t
| Deref   of t

(* Concurrent part *)
| Par     of t * t
| Sema    of string * t
| Grab    of t
| Release of t 

(* Runtime values *)
| DelLoc  of string * t
| DelSema of string * t with eq, show, html

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

      let ident   = Str.regexp "[a-zA-Z_]\([a-zA-Z_0-9]\)*\\b" in 
      let literal = Str.regexp "-?[0-9]+" in
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
	      | Some e -> Assn (Var n, e)
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

module Semantics =
  struct

    module Context =
      struct

	@type e =
	  | Hole
	  | App     of e * t
	  | BinopL  of string * e * t
	  | BinopR  of string * t * e
	  | Unop    of string * e
	  | If      of e * t * t
	  | Seq     of e * t
	  | AssnL   of e * t
	  | AssnR   of t * e
	  | Deref   of e
	  | ParL    of e * t
	  | ParR    of t * e
	  | Grab    of e
	  | Release of e
	  | DelLoc  of string * e
	  | DelSema of string * e with show

        @type path = N | L of path | R of path with show

        let rec getPath = function
	| Hole -> N
	
	| BinopL  (_, e, _)
	| BinopR  (_, _, e)
	| Unop    (_, e)
	| If      (e, _, _)
	| Seq     (e, _)
	| AssnL   (e, _)
	| AssnR   (_, e)
	| Deref    e
	| Grab     e
	| Release  e
	| DelLoc  (_, e)
	| App     (e, _)
	| DelSema (_, e) -> getPath e

	| ParL    (e, _) -> L (getPath e)
	| ParR    (_, e) -> R (getPath e)

      end

    let isValue = function
      | Var _ 
      | Lam _  
      | True
      | False
      | Const _
      | Skip     -> true
      | _        -> false 

    let rec getContexts = function
      | App     (Lam (x, b), y) as t -> [Context.Hole, t] 
      | App     (x         , y)      ->
         List.map (fun (c, t) -> Context.App (c, y), t) (getContexts x)

      | Binop   (s, x, y) as t when isValue x && isValue y -> [Context.Hole, t]
      | Binop   (s, x, y)      when isValue x              ->
          List.map (fun (c, t) -> Context.BinopR (s, x, c), t) (getContexts y)
      | Binop   (s, x, y)                                  ->
	  List.map (fun (c, t) -> Context.BinopL (s, c, y), t) (getContexts x)
                             
      | Unop    (s, x) as t when isValue x -> [Context.Hole, t]
      | Unop    (s, x)                     ->
         List.map (fun (c, t) -> Context.Unop (s, c), t) (getContexts x)

      | If      (x, y, z) as t when isValue x -> [Context.Hole, t]
      | If      (x, y, z)                     ->
         List.map (fun (c, t) -> Context.If (c, y, z), t) (getContexts x)

      | Seq     (Skip, y) as t -> [Context.Hole, t]
      | Seq     (x   , y)      ->
         List.map (fun (c, t) -> Context.Seq  (c, y), t)  (getContexts x)

      | Assn    (x, y) as t when isValue x && isValue y -> [Context.Hole, t]
      | Assn    (x, y) as t when isValue x              ->
         List.map (fun (c, t) -> Context.AssnR (x, c), t) (getContexts y)
      | Assn    (x, y)                                  ->
         List.map (fun (c, t) -> Context.AssnL (c, y), t) (getContexts x)

      | Deref    x as t when isValue x -> [Context.Hole, t]
      | Deref    x                     ->
         List.map (fun (c, t) -> Context.Deref c, t)        (getContexts x)

      | Par     (x, y) as t ->
	 let lContexts = fun () -> List.map (fun (c, t) -> Context.ParL (c, y), t) (getContexts x) in
         let rContexts = fun () -> List.map (fun (c, t) -> Context.ParR (x, c), t) (getContexts y) in
         (match isValue x, isValue y with
          | false, false -> lContexts () @ rContexts ()
          | _    , false -> rContexts ()
          | false, _     -> lContexts ()
          | _            -> [Context.Hole, t]
         )

      | Grab     x as t when isValue x -> [Context.Hole, t]
      | Grab     x                     ->
         List.map (fun (c, t) -> Context.Grab     c, t)      (getContexts x)

      | Release  x as t when isValue x -> [Context.Hole, t]
      | Release  x                     ->
         List.map (fun (c, t) -> Context.Release  c, t)      (getContexts x)

      | DelLoc  (s, x) as t when isValue x -> [Context.Hole, t]
      | DelLoc  (s, x)                     ->
         List.map (fun (c, t) -> Context.DelLoc  (s, c), t)  (getContexts x)

      | DelSema (s, x) as t when isValue x -> [Context.Hole, t]
      | DelSema (s, x)                     ->
         List.map (fun (c, t) -> Context.DelSema (s, c), t)  (getContexts x)

      | t -> [Context.Hole, t]

    let rec applyContext (c, t) =
      match c with
      | Context.Hole                 -> t
      | Context.App        (c, t'  ) -> App     (applyContext (c, t), t')
      | Context.BinopL  (s, c, t'  ) -> Binop   (s, applyContext (c, t), t')
      | Context.BinopR  (s, t', c  ) -> Binop   (s, t', applyContext (c, t))
      | Context.Unop    (s,     c  ) -> Unop    (s,     applyContext (c, t))
      | Context.If      (c, t', t'') -> If      (applyContext (c, t), t', t'')
      | Context.Seq     (c, t')      -> Seq     (applyContext (c, t), t')
      | Context.AssnL   (c, y)       -> Assn    (applyContext (c, t), y)
      | Context.AssnR   (x, c)       -> Assn    (x, applyContext (c, t))
      | Context.Deref       c        -> Deref   (applyContext (c, t))

      | Context.ParL    (c, t')      -> Par     (applyContext (c, t), t')
      | Context.ParR    (t', c)      -> Par     (t', applyContext (c, t))
      | Context.Grab     c           -> Grab    (applyContext (c, t))
      | Context.Release  c           -> Release (applyContext (c, t))

      | Context.DelLoc  (s, c)       -> DelLoc  (s, applyContext (c, t))
      | Context.DelSema (s, c)       -> DelSema (s, applyContext (c, t))

    let newCounter name =
      let i = ref 0 in
      fun () ->
        let i' = !i in
        incr i;
        Var (Printf.sprintf "%s%d" name i')

    let newLoc  = newCounter "loc"
    let newSema = newCounter "sema"
  
    let rec subst x m = function
      | Var      s        when s  = x -> m 
      | Lam     (s , t)   when s != x -> Lam     (s, subst x m t)
      | App     (t1, t2)              -> App     (subst x m t1, subst x m t2)

      | Binop   (s , t1, t2)          -> Binop   (s, subst x m t1, subst x m t2)
      | Unop    (s , t)               -> Unop    (s, subst x m t)
      | If      (t0, t1, t2)          -> If      (subst x m t0, subst x m t1, subst x m t2)
      | Fix      t                    -> Fix     (subst x m t)

      | New     (s , t )  when s != x -> New     (s, subst x m t) 
      | Seq     (t1, t2)              -> Seq     (subst x m t1, subst x m t2) 
      | Assn    (t1, t2)              -> Assn    (subst x m t1, subst x m t2)

      | Deref    t                    -> Deref   (subst x m t)
      
      | Par     (t1, t2)              -> Par     (subst x m t1, subst x m t2) 
      | Sema    (s , t)   when s != x -> Sema    (s, subst x m t)
      | Grab     t                    -> Grab    (subst x m t)
      | Release  t                    -> Release (subst x m t)

      | DelLoc  (s , t)               -> DelLoc  (s, subst x m t)
      | DelSema (s , t)               -> DelSema (s, subst x m t)

      | t -> t

    let contextStep (c, t) ((loc, sema) as state) =
      match t with
      | App     (Lam (x, t), m) -> (c, subst x m t), state 
(*
      | Binop   (s, x, y) when isValue x && isValue y -> (c, binop s x y), state 
      | Unop    (s, x) when is_value x -> (c, unop s x), state
*)  
      | If      (True , x, _)  -> (c, x), state
      | If      (False, _, y)  -> (c, y), state
      | Fix      t             -> (c, App (t, Fix t)), state      
      | Par     (Skip, Skip)   -> (c, Skip), state
      | Seq     (Skip, t)      -> (c, t), state
(*
      | New     (s, t)        -> 
      | Assn    (s, t)        -> ...
      | Deref    t            -> ...
      | Sema    (s, t)        -> ...
      | Grab     t            -> ...
      | Release  t            -> ...
      | DelLoc  (s, t)        -> ...
      | DelSema (s, t)        -> ... 
*)
      | _                     -> (c, t), state

  end

let _ =
  let fin = Sys.argv.(1) in
  let text = Ostap.Util.read fin in
  match fromFile fin with
  | Checked.Ok ast -> 
      let fout = open_out Sys.argv.(2) in
      Printf.fprintf fout "%s\n" (
        HTML.toHTML (
          HTML.html (
            HTML.seq [
              HTML.title (HTML.string @@ Printf.sprintf "Parsing tree for %s" fin);
              HTML.textarea ~attrs:"readonly rows=20 cols=100" @@ HTML.string text;
              HTML.br;
              HTML.body @@ html(t) ast
            ]
          )
	)
      );
      close_out fout
  | Checked.Fail [m] -> 
      Printf.eprintf "Syntax error: %s\n" (Ostap.Msg.toString m)
