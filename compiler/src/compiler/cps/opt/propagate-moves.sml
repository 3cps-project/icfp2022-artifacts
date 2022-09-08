(* propagate-moves.sml
 *
 * For any x <- y [tys] where tys are empty, substitute x with y
 *)

structure CPSPropagateMoves : sig

   val propagate_moves : CPS.comp_unit -> CPS.comp_unit option

   type stats = {elim_move_count : int}
   val stats : unit -> stats

end = struct

   type stats = {elim_move_count : int}
   val st = ref {elim_move_count=0}
   fun stats () = !st
   fun incr_elim_move_count n = let
      val {elim_move_count=elim_move_count} = !st
   in st := {elim_move_count=elim_move_count + n}
   end

   structure C = CPS
   structure LVT = LVar.Tbl
   structure CVT = CVar.Tbl

   fun propagate_moves (C.CU lam0) = let
       val has_changed = ref false
       fun changed () = (has_changed := true)
       
       val lvarMove = LVT.mkTable (100, Fail "CPSPropagateMoves.lvarMove")
       fun rename x = case LVT.find lvarMove x of NONE => x | SOME x' => x'
       fun rename_lst xs = List.map rename xs

       fun propagate_exp (C.EXP (lab_e, e)) =
           case e
           of C.LETFUN(bindings, body) => let
               val bindings = List.map propagate_lam bindings
               val body = propagate_exp body
           in C.EXP (lab_e, C.LETFUN(bindings, body)) end
	    | C.LETCONT(bindingKs, body) => let
                val bindingKs = List.map propagate_lamK bindingKs
                val body = propagate_exp body
            in C.EXP (lab_e, C.LETCONT(bindingKs, body)) end
	    | C.IF(oper, args, thn, els) => let
                val thn = propagate_exp thn
                val els = propagate_exp els
            in C.EXP (lab_e, C.IF(oper, rename_lst args, thn, els)) end
	     | C.ATOM (arg, x, e') => 
               (case arg
                 of C.LVAR (arg, []) => let
                     val _ = LVT.insert lvarMove (x, rename arg)
                     val _ = changed ()
                     val _ = incr_elim_move_count 1
                     val e' = propagate_exp e'
                 in e' end
                  | C.LVAR (arg, tys) => let
                      val e' = propagate_exp e'
                      val arg = rename arg
                  in C.EXP (lab_e, C.ATOM (C.LVAR (arg, tys), x, e')) end
                  | _ => let
                      val e' = propagate_exp e'
                  in C.EXP (lab_e, C.ATOM (arg, x, e')) end)
	     | C.PURE (oper, args, x, e') => let
                 val e' = propagate_exp e'
                 val args = rename_lst args
             in C.EXP (lab_e, C.PURE (oper, args, x, e')) end
	     | C.ARITH (oper, args, x, e', e_exn) => let
                 val e' = propagate_exp e'
                 val e_exn = propagate_exp e_exn
                 val args = rename_lst args
             in C.EXP (lab_e, C.ARITH (oper, args, x, e', e_exn)) end
	     | C.GET (oper, args, x, e') => let
                 val e' = propagate_exp e'
                 val args = rename_lst args
             in C.EXP (lab_e, C.GET (oper, args, x, e')) end
	     | C.SET (oper, args, x, e') => let
                 val e' = propagate_exp e'
                 val args = rename_lst args
             in C.EXP (lab_e, C.SET (oper, args, x, e')) end
	     | C.TUPLE(args, x, e') => let
                 val e' = propagate_exp e'
                 val args = rename_lst args
             in C.EXP (lab_e, C.TUPLE (args, x, e')) end
	     | C.SELECT(offset, arg, x, e') => let
                 val e' = propagate_exp e'
                 val arg = rename arg
             in C.EXP (lab_e, C.SELECT (offset, arg, x, e')) end 
	     | C.DCAPPLY(dcon, tys, arg, x, e') => let
                 val e' = propagate_exp e'
                 val arg = rename arg
             in C.EXP (lab_e, C.DCAPPLY (dcon, tys, arg, x, e')) end
	     | C.SWITCH(arg, pats) => let
                 fun handle_pat (pat, e') = let
                     val e' = propagate_exp e'
                 in (pat, e') end
                 val pats = List.map handle_pat pats
                 val arg = rename arg
             in C.EXP (lab_e, C.SWITCH (arg, pats)) end 
	     | C.APPLY(f, tys, args, argKs) => let
                 val args = rename_lst args
             in C.EXP (lab_e, C.APPLY (rename f, tys, args, argKs)) end
	     | C.THROW(k, args) => let
                 val args = rename_lst args
             in C.EXP (lab_e, C.THROW (k, args)) end
       (* end case *)
       and propagate_lam (lam as (f, lam_lab, xs, ks, body)) = let
           val body = propagate_exp body
       in (f, lam_lab, xs, ks, body) end
       and propagate_lamK (lamK as (k, lamK_lab, xs, body)) = let
           val body = propagate_exp body
       in (k, lamK_lab, xs, body) end

       val cu = C.CU (propagate_lam lam0)
   in if !has_changed
      then SOME cu
      else NONE
   end






end
