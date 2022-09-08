(* contraction.sml
 *
 *)

structure CPSContraction : sig

  val contract : CPS.comp_unit -> CPS.comp_unit option

  type stats = {elim_count : int}
  val stats : unit -> stats

end = struct

  type stats = {elim_count : int}
  val st = ref {elim_count=0}
  fun stats () = !st
  fun incr_elim_count n = let
      val {elim_count=elim_count} = !st
  in st := {elim_count=elim_count + n}
  end

  structure C = CPS
  structure LVT = LVar.Tbl
  structure CVT = CVar.Tbl

  fun contract (C.CU lam0) = let
      val has_changed = ref false
      fun changed () = (has_changed := true)
      val lvarRefCount = LVar.Tbl.mkTable (100, Fail "CPSContraction.lvarRefCount")
      val cvarRefCount = CVar.Tbl.mkTable (100, Fail "CPSContraction.cvarRefCount")
      (* killing things out of the tables may improve running time *)
      fun lookup_lvar x =
          case LVT.find lvarRefCount x
           of SOME res => res
            | _ => raise Fail (LVar.toString x)
      fun lookup_cvar k =
          case CVT.find cvarRefCount k
           of SOME res => res
            | _ => raise Fail (CVar.toString k)
      fun destroy_lvar x =
          (LVT.remove lvarRefCount x; ())
      fun destroy_cvar k =
          (CVT.remove cvarRefCount k; ())
      fun init_lvar x =
          LVT.insert lvarRefCount (x, 0)
      fun init_cvar k =
          CVT.insert cvarRefCount (k, 0)
      fun add_lvar x =
          LVT.insert lvarRefCount (x, lookup_lvar x + 1)
      fun add_cvar k =
          CVT.insert cvarRefCount (k, lookup_cvar k + 1)
      fun keep_lvar x =
          (lookup_lvar x) > 0
      fun keep_cvar k =
          (lookup_cvar k) > 0
      fun contract_exp (exp as C.EXP (lab_e, e)) = 
	  case e
	   of C.LETFUN(bindings, body) => let
               val _ = List.app (fn (f, _, _, _, _) => init_lvar f) bindings
	       val body = contract_exp body
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
               val _ = if List.length bindings' <> List.length bindings
                       then (changed ();
                             incr_elim_count ((List.length bindings') - (List.length bindings)))
                       else ()
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
                val _ = if List.length bindingKs' <> List.length bindingKs
                        then (changed ();
                              incr_elim_count ((List.length bindingKs') - (List.length bindingKs)))
                        else ()
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
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
            end
	    | C.PURE (oper, args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     List.app add_lvar args;
                     C.EXP (lab_e, C.PURE (oper, args, x, e')))
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
            end
            (* Ariths may terminate early, so have to keep them *)
	    | C.ARITH (oper, args, x, e', e_exn) => let
                val _ = init_lvar x
                val _ = List.app add_lvar args
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
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
            end
            (* Sets cause side effects, so they need to stay *)
	    | C.SET (oper, args, x, e') => let
                val _ = init_lvar x
                val _ = List.app add_lvar args
                val e' = contract_exp e'
            in C.EXP (lab_e, C.SET (oper, args, x, e')) end
	    | C.TUPLE(args, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     List.app add_lvar args;
                     C.EXP (lab_e, C.TUPLE (args, x, e')))
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
            end
	    | C.SELECT(offset, arg, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     add_lvar arg;
                     C.EXP (lab_e, C.SELECT (offset, arg, x, e')))
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
            end
	    | C.DCAPPLY(dcon, tys, arg, x, e') => let
                val _ = init_lvar x
                val e' = contract_exp e'
            in if keep_lvar x
               then (destroy_lvar x;
                     add_lvar arg;
                     C.EXP (lab_e, C.DCAPPLY (dcon, tys, arg, x, e')))
               else (changed (); incr_elim_count 1; destroy_lvar x; e')
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
		      | C.LPAT lit => (C.LPAT lit, contract_exp e')
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
          (* can only kill arguments per web, so a separate analysis does that *) 
	  and contract_lam (lam as (f, lam_lab, xs, ks, body)) = let
              val _ = List.app init_lvar xs
              val _ = List.app init_cvar ks
	      val body = contract_exp body
              val _ = List.app destroy_lvar xs
              val _ = List.app destroy_cvar ks
	  in (f, lam_lab, xs, ks, body) end
	  and contract_lamK (lamK as (k, lamK_lab, xs, body)) = let
              val _ = List.app init_lvar xs
	      val body = contract_exp body
              val _ = List.app destroy_lvar xs
	  in (k, lamK_lab, xs, body) end
      val cu = C.CU (contract_lam lam0)
  in if !has_changed
     then SOME cu
     else NONE
  end

end
