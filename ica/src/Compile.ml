open AST
open GT
open MiniKanren

@type ('string, 'self) aport =
  | N of 'string * 'string 
  | F of 'self   * 'self with gmap, html, show

type port  = (string, port) aport
type lport = (string logic, lport) aport logic

let (!) = inj

let rec inj_port port  = (!) @@ gmap(aport) (!) inj_port port
let rec prj_port lport = gmap(aport) prj prj_port @@ prj lport

let rec reverso lport lport_rev =
  conde [
      fresh (inp outp)
            (lport     === !(N (inp, outp)))
            (lport_rev === !(N (outp, inp)));
      fresh (l r l_rev r_rev)
            (lport     === !(F (l, r)))
            (lport_rev === !(F (l_rev, r_rev)))
            (reverso l l_rev) 
            (reverso r r_rev);
    ]

let rec make_porto typ lport =
  conde [
      fresh (inp outp)
            ((typ  === !Nat) ||| (typ === !Bool))
            (lport === !(N (inp, outp)));
      fresh (targ tbody parg pbody parg_rev)
            (typ   === !(Fun (targ, tbody)))
            (lport === !(F   (parg_rev, pbody)))
            (reverso    parg  parg_rev)
            (make_porto targ  parg)
            (make_porto tbody pbody);
    ]
;;

@type ('string, 'int) arg =
  | Acc
  | Reg of 'string
  | Lit of 'int 

@type ('string, 'int, 'arg) command =
  | Label of 'string
  | Jmp   of 'string
  | JmpZ  of 'arg * 'string

  | Mov   of 'arg * 'arg            (* Moves a value from the left to the right argument *)
  | Arith of 'string * 'arg * 'arg  (* Result goes to the second argument *)

(* type ('string, 'int, 'command) box = 'command list  *)

let rec in_out_porto (inp : string logic) (outp  : string logic) (port : lport) =
  conde [
      (port === !(N (inp, outp)));

      fresh (l r)
            (port === !(F (l, r)))
            (in_out_porto inp outp r)
    ]

let rec compilo gamma (ltyp_ltt : (ltyp * ltt) logic) (lport : lport) box =
  fresh (ltyp ltt)
        (ltyp_ltt === !(ltyp, ltt))
        (make_porto ltyp lport)
        (conde [
             fresh (n inp outp)
                   (ltt   === !(Const n))
                   (lport === !(N (inp, outp)))
                   (box   === !(Label inp) %
                                (!(Mov (!(Lit n), !Acc)) %
                                   (!(Jmp outp) % nil)));
                   
             fresh (n inp outp)
                   (((ltt === !True) &&& (n === !1)) |||
                      ((ltt === !False) &&& (n === !0)))
                   (lport === !(N (inp, outp)))
                   (box   === !(Label inp) %
                                (!(Mov (!(Lit n), !Acc)) %
                                   (!(Jmp outp) % nil)));

             (* fresh (name inp outp) *)
             (*       (ltt === !(Var name)) *)
             (*       (Typing.lookupo gamma name box) *)
             (* TODO: remove copying of the box. *)
                   
              fresh (op l r inp outp
                        lbox rbox
                        inl outl
                        inr outr
                        r0)
                   (ltt   === !(Binop (op, l, r)))
                   (lport === !(N (inp, outp)))
                   (box   === !(Label inp) %
                                (!(Jmp inl) %
                                   (!(Label outl) %
                                      (!(Mov (!Acc, !(Reg r0))) %
                                         (!(Jmp inr) %
                                            (!(Label outr) %
                                               (!(Arith (op, !(Reg r0), !Acc)) %
                                                  (!(Jmp outp) % nil))))))))
                   
                   (compilo gamma l !(N (inl, outl)) lbox)
                   (compilo gamma r !(N (inr, outr)) rbox);

               fresh (c the els inp outp
                        cbox thebox elsbox
                        cport theport elsport
                        inc outc
                        inthe outthe
                        inels outels)
                   (ltt   === !(If (c, the, els)))
                   
                   (box   === !(Label inp) %
                                (!(Jmp inc) %
                                   (!(Label outc) %
                                      (!(JmpZ (!Acc, inels)) %
                                        (!(Jmp inthe) %
                                          (!(Label outthe) %
                                             (!(Jmp outp) %
                                                (!(Label outels) %
                                                   (!(Jmp outp) % nil)))))))))
                   
                   (in_out_porto inels outels elsport)
                   (in_out_porto inthe outthe theport)

                   (compilo gamma c   cport   cbox)
                   (compilo gamma the theport thebox)
                   (compilo gamma els elsport elsbox);
                   
        ])

  (* | Var     of 'string *)
  (* | Lam     of 'string * 't *)
  (* | App     of 't * 't *)

let _ =
  run q (fun q ->
        fresh (lport)
              (compilo nil !(!Nat, !(Binop (!"+", !(!Nat, !(Const !2)), !(!Nat, !(Const !2))))) lport q))
      (fun qs ->
        match Stream.take ~n:1 qs with
	| []  -> Printf.printf "Problem\n"
        | [t] -> Printf.printf "Ok\n"
      )
