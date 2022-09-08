(* simple-arity-raising.sml
 *
 * Identifies functions f that are
 * - only used in function position
 * - f has a parameter that is unused
 *
 * Then, eliminates the unused arguments
 * 
 * Does the same for continuations
 *)

structure CPSSimpleArgumentElimination : sig

   val eliminate_arguments : CPS.comp_unit -> CPS.comp_unit option

   type stats = {elim_arg_count : int}
   val stats : unit -> stats

end = struct

   type stats = {elim_arg_count : int}
   val st = ref {elim_arg_count=0}
   fun stats () = !st
   fun incr_elim_arg_count n = let
      val {elim_arg_count=elim_arg_count} = !st
   in st := {elim_arg_count=elim_arg_count + n}
   end

   structure C = CPS
   structure LVT = LVar.Tbl
   structure CVT = CVar.Tbl

   datatype shape = Unconstrained
                  | Tuple of int
                  | Overconstrained

   (* get the functions f that are only used in function position and
      are given a tuple at all call sites that can be raised *)
   fun candidates (C.CU lam0) = let
       val lvarCandidates : bool list LVT.hash_table = LVT.mkTable (100, Fail "CPSSimpleArgumentElimination.lvarCandidates")
       val cvarCandidates : bool list CVT.hash_table = CVT.mkTable (100, Fail "CPSSimpleArgumentElimination.cvarCandidates")
       val lvarUnused : unit LVT.hash_table = LVT.mkTable (100, Fail "CPSSimpleArgumentElimination.lvarUnused")
       fun kill_lvar x =
           case LVT.find lvarCandidates x
            of NONE => ()
             | _ => (LVT.remove lvarCandidates x; ())
       fun kill_cvar k =
           case CVT.find cvarCandidates k
            of NONE => ()
             | _ => (CVT.remove cvarCandidates k; ()) 
       fun used x =
           case LVT.find lvarUnused x
            of SOME () => (LVT.remove lvarUnused x; ())
             | NONE => ()
       fun candidate_exp (exp as C.EXP (lab_e, e)) =
           case e
	    of C.LETFUN(bindings, body) => let
                fun init_bind (f, _, xs, _, _) =
                    LVT.insert lvarCandidates (f, List.map (fn x => true) xs) 
                val _ = List.app init_bind bindings
                val _ = List.app candidate_lam bindings
                fun handle_bind (f, _, xs, _, _) =
                    (case LVT.find lvarCandidates f
                      of SOME _ => LVT.insert lvarCandidates (f, List.map (LVT.inDomain lvarUnused) xs)
                       | NONE => ())
                val _ = List.app handle_bind bindings
            in candidate_exp body end
	     | C.LETCONT(bindingKs, body) => let
                fun init_bindK (k, _, xs, _) =
                    CVT.insert cvarCandidates (k, List.map (fn x => true) xs) 
                val _ = List.app init_bindK bindingKs
                val _ = List.app candidate_lamK bindingKs
                fun handle_bindK (k, _, xs, _) =
                    (case CVT.find cvarCandidates k
                      of SOME _ => CVT.insert cvarCandidates (k, List.map (LVT.inDomain lvarUnused) xs)
                       | NONE => ())
                val _ = List.app handle_bindK bindingKs
            in candidate_exp body end
	    | C.IF(oper, args, thn, els) => 
              (List.app kill_lvar args;
	       List.app used args;
	       candidate_exp thn;
	       candidate_exp els)
	    | C.ATOM (arg, x, e') => 
                (case arg 
                  of C.LVAR (y, ty) => (kill_lvar y; used y)
                   | _ => ();
	         candidate_exp e')
	    | C.PURE (oper, args, x, e') =>
              (List.app kill_lvar args;
	       List.app used args;
               candidate_exp e')
	    | C.ARITH (oper, args, x, e', e_exn) => 
              (List.app kill_lvar args;
               List.app used args;
               candidate_exp e';
               candidate_exp e_exn)
	    | C.GET (oper, args, x, e') =>
              (List.app kill_lvar args;
	       List.app used args;
               candidate_exp e')
	    | C.SET (oper, args, x, e') => 
              (List.app kill_lvar args;
	       List.app used args;
               candidate_exp e')
	    | C.TUPLE(args, x, e') => 
              (List.app kill_lvar args;
	       List.app used args;
               candidate_exp e')
	    | C.SELECT(offset, arg, x, e') => 
              (kill_lvar arg;
               used arg;
               candidate_exp e')
	    | C.DCAPPLY(dcon, tys, arg, x, e') => 
              (kill_lvar arg;
	       used arg;
               candidate_exp e')
	    | C.SWITCH(arg, pats) => 
              (kill_lvar arg;
	       used arg;
               List.app (fn (_, e') => candidate_exp e') pats)
	    | C.APPLY(f, tys, args, argKs) => 
              (List.app kill_lvar args;
	       used f;
	       List.app used args;
               List.app kill_cvar argKs)
	    | C.THROW(k, args) => 
              (List.app kill_lvar args;
	       List.app used args)
	  (* end case *)
       and candidate_lam (_, _, xs, _, body) =
           (List.app (fn x => LVT.insert lvarUnused (x, ())) xs;
            candidate_exp body)
       and candidate_lamK (_, _, xs, body) = 
           (List.app (fn x => LVT.insert lvarUnused (x, ())) xs;
            candidate_exp body)
   in candidate_lam lam0;
      (lvarCandidates, cvarCandidates)
   end
                    
   fun modify (C.CU lam0, lvarCandidates, cvarCandidates) = let
       val has_changed = ref false
       fun changed () = (has_changed := true)
       val lvarRetyped = LVT.mkTable (100, Fail "CPSSimpleArgumentElimination.lvarRetyped")
       val cvarRetyped = CVT.mkTable (100, Fail "CPSSimpleArgumentElimination.cvarRetyped")
       fun getType x = let
           val CPSTypes.TyScheme (_, ty) = LVar.typeOf x
       in ty end
       fun rename x = case LVT.find lvarRetyped x of NONE => x | SOME x' => x'
       fun rename_lst xs = List.map rename xs
       fun renameK k = case CVT.find cvarRetyped k of NONE => k | SOME k' => k'
       fun renameK_lst ks = List.map renameK ks
       fun elim_args (args, elims) = let
           fun fold (arg, elim, args) = if elim then (changed (); args) else arg :: args
       in ListPair.foldr fold [] (args, elims) end
       fun elim_params (xs, elims) = let
           fun fold (x, elim, xs) = if elim then (changed (); incr_elim_arg_count 1; xs) else x :: xs
       in ListPair.foldr fold [] (xs, elims) end
       fun modify_exp (exp as C.EXP (lab_e, e)) = 
           C.EXP (lab_e, case e
	    of C.LETFUN(bindings, body) => let
                val bindings = List.map modify_lam bindings
                val bindings = List.map (fn bind => bind ()) bindings
                val body = modify_exp body
            in C.LETFUN(bindings, body) end
	     | C.LETCONT(bindingKs, body) => let
                val bindingKs = List.map modify_lamK bindingKs
                val bindingKs = List.map (fn bindK => bindK ()) bindingKs
                val body = modify_exp body
            in C.LETCONT(bindingKs, body) end
	     | C.IF(oper, args, thn, els) => let
                 val thn = modify_exp thn
                 val els = modify_exp els
             in C.IF(oper, rename_lst args, thn, els) end
	     | C.ATOM (arg, x, e') => let
                 val e' = modify_exp e'
                 val arg = case arg of C.LVAR (arg, tys) => C.LVAR (rename arg, tys) | _ => arg
             in C.ATOM (arg, x, e') end
	     | C.PURE (oper, args, x, e') => let
                 val e' = modify_exp e'
             in C.PURE (oper, rename_lst args, x, e') end
	     | C.ARITH (oper, args, x, e', e_exn) => let
                 val e' = modify_exp e'
                 val e_exn = modify_exp e_exn
             in C.ARITH (oper, rename_lst args, x, e', e_exn) end
	     | C.GET (oper, args, x, e') => let
                 val e' = modify_exp e'
             in C.GET (oper, rename_lst args, x, e') end
	     | C.SET (oper, args, x, e') => let
                 val e' = modify_exp e'
             in C.SET (oper, rename_lst args, x, e') end
	     | C.TUPLE(args, x, e') => let
                 val e' = modify_exp e'
             in C.TUPLE (rename_lst args, x, e') end
	     | C.SELECT(offset, arg, x, e') => let
                 val e' = modify_exp e'
             in C.SELECT (offset, rename arg, x, e') end 
	     | C.DCAPPLY(dcon, tys, arg, x, e') => let
                 val e' = modify_exp e'
             in C.DCAPPLY (dcon, tys, rename arg, x, e') end
	     | C.SWITCH(arg, pats) => let
                 fun handle_pat (pat, e') = let
                     val e' = modify_exp e'
                 in (pat, e') end
                 val pats = List.map handle_pat pats
             in C.SWITCH (rename arg, pats) end 
	     | C.APPLY(f, tys, args, argKs) =>
               (case LVT.find lvarCandidates f
                 of NONE => C.APPLY (rename f, tys, rename_lst args, renameK_lst argKs)
                  | SOME elims => C.APPLY (rename f, tys, elim_args (args, elims), renameK_lst argKs))
	     | C.THROW(k, args) => 
               (case CVT.find cvarCandidates k
                 of NONE => C.THROW (renameK k, rename_lst args)
                  | SOME elims => C.THROW (renameK k, elim_args (args, elims)))
       (* end case *))
       and modify_lam (lam as (f, lam_lab, xs, ks, body)) =
           case LVT.find lvarCandidates f
            of NONE => (fn () => (rename f, lam_lab, xs, ks, modify_exp body))
             | SOME elims => let
                 val xs = elim_params (xs, elims)
                 val CPSTypes.TyScheme (sch, CPSTypes.FunTy (_, ctys)) = LVar.typeOf f
                 val ty = CPSTypes.TyScheme (sch, CPSTypes.FunTy (List.map getType xs, ctys))
                 val f' = LVar.newTmp (LVar.nameOf f, ty, LVar.extentOf f)
                 val _ = LVT.insert lvarRetyped (f, f')
             in (fn () => (f', lam_lab, xs, ks, modify_exp body)) end
       and modify_lamK (lamK as (k, lamK_lab, xs, body)) = 
           case CVT.find cvarCandidates k
            of NONE => (fn () => (renameK k, lamK_lab, xs, modify_exp body))
             | SOME elims => let
                 val xs = elim_params (xs, elims)
                 val tys = List.map getType xs
                 val k' = CVar.newTmp (CVar.nameOf k, CPSTypes.ContTy tys, CVar.extentOf k)
                 val _ = CVT.insert cvarRetyped (k, k')
             in (fn () => (k', lamK_lab, xs, modify_exp body)) end
   in (C.CU (modify_lam lam0 ()), !has_changed) end

   fun eliminate_arguments cu = let
       val (lvarCandidates, cvarCandidates) = candidates cu
       val (cu, changed) = modify (cu, lvarCandidates, cvarCandidates)
   in if changed
      then SOME cu
      else NONE
   end

end
