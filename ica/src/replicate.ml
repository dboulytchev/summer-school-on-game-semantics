open GT
open MiniKanren

@type ('int, 'self) abox = L of 'int | N of 'int * 'self with gmap, show

type box  = (int, box) abox
type lbox = (int logic, lbox) abox logic

let (!) = inj

let rec inj_box b = ! (gmap(abox) (!) inj_box b)
let rec prj_box b = gmap(abox) (prj_k (fun l -> match destruct l with `Var (i, _) -> i)) prj_box @@ prj b

let rec show_box b = show(abox) (show(int)) show_box b

let rec make_boxo n b =
  conde [
    fresh (l)
      (n === !O)
      (b === !(L l));
    fresh (m l sb bm)
      (n === !(S m))
      (b === !(N (l, bm)))
      (conde [
         (bm === !(L l));
         (bm === !(N (l, sb)))
       ])
      (make_boxo m bm)
  ]

let _ =
  run q (fun b  -> make_boxo (inj_nat 3) b)
        (fun bs -> 
           Printf.printf "%s\n" (show_box @@ prj_box @@ Stream.hd bs)
        );;

@type ('string, 'int, 'self) ap = 
  | End 
  | Var of 'string * 'self 
  | Int of 'string * 'int * 'self with gmap

type  p = (string, int, p) ap
type lp = (string logic, int logic, lp) ap logic
  
let rec inj_p p = (!) @@ gmap(ap) (!) inj_nat inj_p p
let rec prj_p p = gmap(ap) prj prj prj_p @@ prj p

let extend f x v = fun y -> if x = y then v else f y 

let rec lookupo a g t =
  fresh (a' t' tl) 
    (g === !(a', t')%tl)
    (conde [
      (a' === a) &&& (t' === t);
      lookupo a tl t
     ])  

module Meta =
  struct

    let rec make_p gamma = function
    | End                 -> (fun boxes -> boxes === nil)
    | Var (name, ps)      -> (fun boxes -> 
                                fresh (b bs) 
                                  (gamma name b)
                                  (make_p gamma ps bs)
                                  (boxes === b % bs)
			     )  
    | Int (name, int, ps) -> (fun boxes ->
                                fresh (b bs)
                                  (boxes === b % bs)
                                  (make_boxo (inj_nat int) b)
                                  (make_p (extend gamma name (fun b -> make_boxo (inj_nat int) b)) ps bs)
                             )

  end

let rec make_p gamma p boxes =
  conde [
    (p === !End) &&& (boxes === nil);
    fresh (name ps b bs)
      (p === !(Var (name, ps)))
      (lookupo name gamma b)
      (boxes === b % bs)
      (make_p gamma ps bs);
    fresh (nat name ps b bs)
      (p === !(Int (name, nat, ps)))
      (boxes === b % bs)
      (make_boxo nat b)
      (make_p (!(name, b) % gamma) ps bs)
  ]

let _ =
  run q (fun bs -> make_p nil (inj_p (Int ("x", 2, Int ("y", 3, Var ("x", Var ("x", End)))))) bs)
        (fun bs -> 
	   Printf.printf "%s\n" @@ show(list) show_box (List.to_list (List.prj prj_box @@ Stream.hd bs))
        )

let _ =
  run q (fun bs -> Meta.make_p (fun _ -> invalid_arg "") (Int ("x", 2, Int ("y", 3, Var ("x", Var ("x", End))))) bs)
        (fun bs -> 
	   Printf.printf "%s\n" @@ show(list) show_box (List.to_list (List.prj prj_box @@ Stream.hd bs))
        )
