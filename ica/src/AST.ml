open GT
open MiniKanren

@type 'typ atyp = TVar of int | Untyped | Nat | Bool | Fun of 'typ * 'typ with gmap, html, show

type typ  = typ atyp
type ltyp = ltyp atyp logic

let rec inj_typ t  = inj @@ gmap(atyp) inj_typ t
let rec prj_typ lt = gmap(atyp) prj_typ @@ (match destruct lt with `Var (n, _) -> TVar n | `Value v -> v)
;;

@type ('string, 'int, 't) at = 
  (* Lambda part *)
  | Var     of 'string
  | Lam     of 'string * 't
  | App     of 't * 't
	
  (* PCF part *)
  | Binop   of 'string * 't * 't
  | Unop    of 'string * 't
  | True
  | False
  | Const   of 'int
  | If      of 't * 't * 't
  | Fix     of 't
	
  (* I.A. part *)
  | Skip    
  | New     of 'string * 't
  | Seq     of 't * 't
  | Assn    of 't * 't
  | Deref   of 't
	
  (* Concurrent part *)
  | Par     of 't * 't
  | Sema    of 'string * 't
  | Grab    of 't
  | Release of 't 
	
  (* Runtime values *)
  | DelLoc  of 'string * 't
  | DelSema of 'string * 't with eq, show, html, gmap
  
type t   = (string, int, t) at
type lt  = (string logic, int logic, lt) at logic
type tt  = (string, int, typ * tt) at
type ltt = (string logic, int logic, (ltyp * ltt) logic) at logic
      
let rec inj_term t  = inj (gmap(at) inj inj inj_term t)
let rec prj_term lt = gmap(at) prj prj prj_term @@ prj lt

let id x = x
let rec inj_term_tterm : t -> tt = fun t ->
  gmap(at) id id
      (fun t -> (Untyped,
                 inj_term_tterm t)) t

let rec prj_tterm_term : tt -> t = fun t ->  
  gmap(at) id id
      (fun (_, t) -> prj_tterm_term t) t

let rec inj_tterm_ltt : tt -> ltt = fun tt ->
  inj @@ gmap(at) inj inj
             (fun (typ, tt) ->
               inj @@ (inj_typ typ, inj_tterm_ltt tt)) tt

let rec prj_ltt_tterm : ltt -> tt = fun ltt ->
  gmap(at) prj prj
      (fun lp -> (let ltyp, ltt = prj lp in
                  prj_typ ltyp, prj_ltt_tterm ltt))
      @@ prj ltt

module Typing =
  struct

    let (!) = inj

    let rec lookupo a g t =
      fresh (a' t' tl) 
        (g === !(a', t')%tl)
        (conde [
          (a' === a) &&& (t' === t);
          lookupo a tl t
         ])  

    let removo l n l' = List.filtero (neqo n) l l'

    let rec varo tterm vars =
      fresh (typ term)
            (tterm === !(typ, term))
            (conde [
                 fresh (name)
                       (term === !(Var name)) 
                       (vars === !< name);
                 fresh (name body tbody vbody)
                       (term === !(Lam (name, body)))
                       (removo vbody name vars) 
                       (varo tbody vbody);
                 fresh (f arg fvar avar)
                       (term === !(App (f, arg)))
                       (List.appendo fvar avar vars)
                       (varo f   fvar)
                       (varo arg avar);
                 fresh (int)
                       (term === !(Const int))
                       (vars === nil);
                 fresh (op x y xvars yvars)
                       (term === !(Binop (op, x, y)))
                       (List.appendo xvars yvars vars)
                       (varo x xvars)
                       (varo y yvars);
                 ((term === !True) ||| (term === !False)) &&& (vars === nil);
                 fresh (cond th el cvars tvars evars tevars)
                       (term === !(If (cond, th, el)))
                       (List.appendo tvars evars tevars)
                       (List.appendo cvars tevars vars)
                       (varo th   tvars)
                       (varo el   evars)
                       (varo cond cvars);
                 fresh (unfix)
                       (term === !(Fix unfix))
                       (varo unfix vars)
            ])

    let splito gamma term yes no =
      fresh (vars)
        (varo term vars)       
        (List.filtero 
           (fun p f ->
              fresh (name typ)
                 (p === !(name, typ))
                 (conde [
                   List.lookupo (eqo name) vars !(Some name) &&& (f === !true);
                   List.lookupo (eqo name) vars !None &&& (f === !false)
                 ]) 
           ) 
           gamma 
           yes
        )
	(List.filtero 
           (fun p f ->
              fresh (name typ)
                 (p === !(name, typ))
                 (conde [
                   List.lookupo (eqo name) vars !(Some name) &&& (f === !false);
                   List.lookupo (eqo name) vars !None &&& (f === !true)
                 ]) 
           ) 
           gamma 
           no
        )
 
    (* term'  --- term w/ untyped tags along the tree;
       term'' --- the properly annotated term'.
     *)
    let rec mako gamma term' term'' =
      fresh (term typ typ')
            (term'  === !(typ', term))
            (conde [
                 fresh (name)
                       (term   === !(Var name)) 
                       (lookupo name gamma typ)
                       (term'' === !(typ, term));

                 fresh (name body targ tbody_type tbody_term)
                       (term   === !(Lam (name, body)))
                       (mako (!(name, targ) % gamma)
                             body
                             !(tbody_type, tbody_term))
                       (term'' ===
                          !(!(Fun (targ, tbody_type)),
                            !(Lam (name, !(tbody_type, tbody_term)))));

                 fresh (f arg ftype fterm atype aterm fgamma agamma)
                       (term   === !(App (f, arg)))
	               (splito gamma f fgamma agamma)

                       (ftype  === !(Fun (atype, typ)))
                       (mako fgamma f   !(ftype, fterm))
                       (mako agamma arg !(atype, aterm))
                       (term'' === !(typ, !(App (!(ftype, fterm),
                                                 !(atype, aterm)))));

                 fresh (int)
                       (term   === !(Const int))
                       (term'' === !(!Nat, term));

                 fresh (op x y xt yt)
                       (term   === !(Binop (op, x, y)))
                       (List.lookupo (eqo op) (inj_list ["&&"; "!!"]) !(Some op))
                       (mako gamma x !(!Bool, xt))
                       (mako gamma y !(!Bool, yt))
                       (term'' === !(!Bool, !(Binop (op, !(!Bool, xt), !(!Bool, yt)))));

                 fresh (op x y xt yt)
                       (term   === !(Binop (op, x, y)))
                       (List.lookupo
                          (eqo op)
                          (inj_list ["=="; "!="; "<="; "<"; ">="; ">"]) !(Some op))
                       (mako gamma x !(!Nat, xt))
                       (mako gamma y !(!Nat, yt))
                       (term'' === !(!Bool, !(Binop (op, !(!Nat, xt), !(!Nat, yt)))));

                 fresh (op x y xt yt)
                       (term   === !(Binop (op, x, y)))
                       (List.lookupo
                          (eqo op)
                          (inj_list ["+"; "-"; "*"; "/"]) !(Some op))
                       (mako gamma x !(!Nat, xt))
                       (mako gamma y !(!Nat, yt))
                       (term'' === !(!Nat, !(Binop (op, !(!Nat, xt), !(!Nat, yt)))));

                 ((term === !True) ||| (term === !False)) &&& (term'' === !(!Bool, term));

                 fresh (cond th el condt tht elt)
                       (term   === !(If (cond, th, el)))
                       (mako gamma th !(typ, tht))
                       (mako gamma el !(typ, elt))
                       (mako gamma cond !(!Bool, condt))
                       (term'' === !(typ, !(If (!(!Bool, condt), !(typ, tht), !(typ, elt)))));

                 fresh (unfix untyp unfixt)
                       (term   === !(Fix unfix))
                       (mako gamma unfix !(!(Fun (typ, typ)), unfixt))
                       (term'' === !(typ, !(Fix !(!(Fun (typ, typ)), unfixt))))
            ])

    let make term : (typ * tt) option =
      run q (fun t -> mako nil
                           !(!Untyped,
                             inj_tterm_ltt (inj_term_tterm term)) t)
          (fun ts ->
	    match Stream.take ~n:1 ts with
	    | []  -> None
            | [t] ->
               let (typ, tt) = prj t in
               Some (prj_typ typ, prj_ltt_tterm tt)
          )

  end

exception Error of string
 
module Parser =
  struct

    open Ostap.Util

    let hparse s = 
      let ostap (
        def[env] : 
          %"def" -x:IDENT -"=" -e:apps[env] %"in" def[(x, `Def e)::env] 
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
        | k:DECIMAL {Const k}
        | %"true" {True} 
        | %"false" {False}
        | %"fix" e:expr[env] {Fix e}
        | %"if" c:expr[env] %"then" e1:expr[env] %"else" e2:expr[env] %"fi" {If (c, e1, e2)} 
        | %"new" n:IDENT %"in" e:expr[env] {New (n, e)}
        | %"semaphore" n:IDENT %"in" e:expr[env] {Sema (n, e)}
        | %"grab" e:expr[env] {Grab e}
        | %"release" e:expr[env] {Release e}
        | %"skip" {Skip}
        | "!" e:expr[env] {Deref e}        
        | n:IDENT s:(-":=" expr[env])? {
            try
              match s with
	      | None ->
                 (match List.assoc n env with
                  | `Def e -> e
                  | `Arg   -> Var n
                 )
	      | Some e -> Assn (Var n, e)
            with Not_found -> raise (Error (Printf.sprintf "undefined identifier %s" n))
          }
        | "\\" ns:IDENT+ "." e:expr[List.map (fun n -> (n, `Arg)) ns @ env] {
            List.fold_right (fun n acc -> Lam (n, acc)) ns e
          }
      ) in
      def [] s

    let parse s = ostap (hparse -EOF) s
    
  end

let fromFile fname =
  let s = Ostap.Util.read fname in
  Ostap.Util.parse 
    (object
       inherit Ostap.Matcher.t s 
       inherit Ostap.Util.Lexers.skip [
         Ostap.Matcher.Skip.whitespaces " \n\t\r"; 
         Ostap.Matcher.Skip.nestedComment "(*" "*)";
         Ostap.Matcher.Skip.lineComment "--"
       ] s
       inherit Ostap.Util.Lexers.decimal s
       inherit Ostap.Util.Lexers.ident ["def"; "new"; "in"; "semaphore"; "if"; "then"; "else"; "fi"; "fix"; "grab"; "release"; "true"; "false"; "skip"] s
     end
    )
    Parser.parse

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
	  | DelSema of string * e 

        @type path = N | L of path | R of path

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
  let rec fix f x = f (fix f) x in
  let fin = Sys.argv.(1) in
  let text = Ostap.Util.read fin in
  match fromFile fin with
  | `Ok ast -> 
      Printf.printf "Parsing ok.\n%!";
      let fout = open_out Sys.argv.(2) in
      Printf.fprintf fout "%s\n%!" (
        HTML.toHTML (
          HTML.html (
            HTML.seq [
              HTML.title (HTML.string @@ Printf.sprintf "Parsing tree for %s" fin);
              HTML.textarea ~attrs:"readonly rows=20 cols=100" @@ HTML.string text;
              HTML.br;
              HTML.body (
                HTML.seq [
                    html(option)
                        (fix (fun to_html_p ->
                             (html(pair)
                                  (fun typ -> (fix (fun to_html -> html(atyp) to_html) typ))
                                  (html(at) (html(string)) (html(int)) to_html_p))))
                      (Typing.make ast)
		]
              )              
            ]
          )
	)
      );
      close_out fout
  | `Fail m -> Printf.eprintf "Syntax error: %s\n" m
