(* test for pattern-match compilation from Sestoft *)
datatype lam = Var of int | Lam of int * lam | App of lam * lam | Let of int * lam * lam;

fun f2 arg = (case arg
       of Var _ => 111
        | Lam(_, Var _) => 222
        | Lam(_, Lam(_, _)) => 333
        | Lam(_, App(_, _)) => 444
        | App(Lam(_, _), _) => 555
        | App(App(_, _), _) => 666
        | Let(_, Let(_, _, _), _) => 777
        | Lam(_, Let(_, _, _)) => 888
        | Let(_, _, App(_, _)) => 999
(*
        | App(App(Lam(_, Lam(_, _)), _), _) => 1010  (* redundant *)
*)
      (* end case *));

val _ = f2(Var 6)
