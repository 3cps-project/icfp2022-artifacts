
structure CPSVarAnalysis : sig

  val analyze : CPS.comp_unit -> ExtentSet.t LVar.Map.map * ExtentSet.t CVar.Map.map

end = struct

  structure C = CPS
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure E = ExtentSet

  fun analysis (C.CU lam0) = let
      val lvarExtents = ref LVM.empty
      val cvarRefCount = ref CVM.empty
      fun ex_diff (ex1, ex2) =
          case (ex1, ex2)
           of E.HSR, E.HSR
      fun init_lvar x =
          lvarExtents := LVM.insert (!lvarExtents, x, E.HSR)
      fun init_cvar k =
          cvarExtents := CVM.insert (!cvarExtents, k, E.HSR)
      fun kill_lvar (x, ex) =
          lvarExtents := LVM.insert (lvarRefCount, x, ex_diff (LVM.lookup (! lvarExtents, x), ex))
      fun kill_cvar (k, ex) =
          cvarExtents := CVM.insert (cvarRefCount, k, ex_diff (CVM.lookup (! cvarExtents, k), ex))
      fun contract_exp (exp as C.EXP (lab_e, e), kill_lvar_SR, kill_cvar_SR, kill_lvar_R, kill_cvar_R) = 
	  case e
	   of C.LETFUN(bindings, body) => let
               val kill_lvar_R' = List.foldl (fn ((f, _, _, _, _), acc) => LVS.add (f, acc))
                                             kill_lvar_R bindings
	       val body = contract_exp (body, kill_lvar_SR, kill_cvar_SR, kill_lvar_R', kill_cvar_R)
               val () = List.app (fn ulam => contract_lam (lam, kill_lvar_SR< kill_cvar_SR, kill_lvar_R', kill_cvar_R))
                                 bindings
               (* we do something neat to determine fun binds that are not reachable. *)
               fun keep_bind (f, _, _, _, _) = keep_lvar f
               fun prune_bindings (keep, not_yet) = let
                   val keep = List.map contract_lam keep
                   val (keep', not_yet') = List.partition keep_bind not_yet
               in case keep'
                   of [] => keep
                    | _ => prune_bindings (keep', not_yet') @ keep
               end
               val bindings' = prune_bindings ([], bindings)
               val _ = List.app (fn (f, _, _, _, _) => destroy_lvar f) bindings
           in case bindings'
               of [] => body
                | _ => C.EXP (lab_e, C.LETFUN (bindings', body))
           end
	    | C.LETCONT(bindingKs, body) => let
                val _ = List.app (fn (k, _, _, _) => init_cvar k) bindingKs
		val body = contract_exp body
                (* we do something neat to determine fun binds that are not reachable. *)
                fun keep_bindK (k, _, _,  _) = keep_cvar k
                fun prune_bindingKs (keep, not_yet) = let
                    val keep = List.map contract_lamK keep
                    val (keep', not_yet') = List.partition keep_bindK not_yet
                in case keep'
                    of [] => keep
                     | _ => prune_bindingKs (keep', not_yet') @ keep
                end
                val bindingKs' = prune_bindingKs ([], bindingKs)
                val _ = List.app (fn (k, _, _, _) => destroy_cvar k) bindingKs
            in case bindingKs'
                of [] => body
                 | _ => C.EXP (lab_e, C.LETCONT (bindingKs', body))
            end
	    | C.IF(oper, args, thn, els) => let
		val _ = List.app add_lvar args
		val thn = contract_exp thn
		val els = contract_exp els
	    in C.EXP (lab_e, C.IF (oper, args, thn, els)) end
	    | C.ATOM (arg, x, e') => let
                val _ = init_lvar x
		val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     case arg of C.LVAR (y, _) => add_lvar y | _ => ();
                     C.EXP (lab_e, C.ATOM (arg, x, e')))
               else (destroy_lvar x; e')
            end
	    | C.PURE (oper, args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     List.app add_lvar args;
                     C.EXP (lab_e, C.PURE (oper, args, x, e')))
               else (destroy_lvar x; e')
            end
            (* Ariths may terminate early, so have to keep them *)
	    | C.ARITH (oper, args, x, e', e_exn) => let
                val _ = init_lvar x
                val e' = contract_exp e'
                val e_exn = contract_exp e_exn
            in C.EXP (lab_e, C.ARITH  (oper, args, x, e', e_exn)) end
	    | C.GET (oper, args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     List.app add_lvar args;
                     C.EXP (lab_e, C.GET (oper, args, x, e')))
               else (destroy_lvar x; e')
            end
            (* Sets cause side effects, so they need to stay *)
	    | C.SET (oper, args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in C.EXP (lab_e, C.SET (oper, args, x, e')) end
	    | C.TUPLE(args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     List.app add_lvar args;
                     C.EXP (lab_e, C.TUPLE (args, x, e')))
               else (destroy_lvar x; e')
            end
	    | C.SELECT(offset, arg, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     add_lvar arg;
                     C.EXP (lab_e, C.SELECT (offset, arg, x, e')))
               else (destroy_lvar x; e')
            end
	    | C.DCAPPLY(dcon, tys, arg, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     add_lvar arg;
                     C.EXP (lab_e, C.DCAPPLY (dcon, tys, arg, x, e')))
               else (destroy_lvar x; e')
            end
	    | C.SWITCH(arg, pats) => let
                (* can't kill patterns *)
		fun contract_pat (pat, e') = 
		    case pat
		     of C.VPAT x => let
                         val _ = init_lvar x
                         val e' = contract_exp e'
                         val _ = destroy_lvar x
                     in (C.VPAT x, contract_exp e') end
		      | C.LPAT lit => (C.LPAT lit, e')
		      | C.DCPAT (dcon, tys, SOME x) => let
                          val _ = init_lvar x
                          val e' = contract_exp e'
                          val _ = destroy_lvar x
                      in (C.DCPAT (dcon, tys, SOME x), e') end
		      | C.DCPAT (dcon, tys, NONE) => (C.DCPAT (dcon, tys, NONE), contract_exp e')
	        val pats = List.map contract_pat pats
	        val _ = add_lvar arg
            in C.EXP (lab_e, C.SWITCH (arg, pats)) end
	    | C.APPLY(f, tys, args, argKs) => let
		val _ = add_lvar f
                val _ = List.app add_lvar args
                val _ = List.app add_cvar argKs
	    in C.EXP (lab_e, C.APPLY (f, tys, args, argKs)) end
	    | C.THROW(k, args) => let
		val _ = add_cvar k
                val _ = List.app add_lvar args
            in C.EXP (lab_e, C.THROW (k, args)) end
	  (* end case *)
          (* can only kill arguments per web *) 
	  and contract_lamK (lamK as (k, lamK_lab, xs, body)) = let
              val _ = List.app init_lvar xs
	      val body = contract_exp body
              val _ = List.app destroy_lvar xs
	  in (k, lamK_lab, xs, body) end
	  and contract_lam (lam as (f, lam_lab, xs, ks, body)) = let
              val _ = List.app init_lvar xs
              val _ = List.app init_cvar ks
	      val body = contract_exp body
              val _ = List.app destroy_lvar xs
              val _ = List.app destroy_cvar ks
	  in (f, lam_lab, xs, ks, body) end
      in C.CU (contract_lam lam0) end





end
