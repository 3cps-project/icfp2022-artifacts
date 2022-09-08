(* simple-arity-raising.sml
 *
 * Identifies functions f that are
 * - only used in function position
 * - at each call to f, it is given a tuple for an argument whose components are available
 *
 * Additionally, is conservative:
 * - the tuple parameter is a candidate for arity raising only if it is only selected from in f
 *
 * Then, arity raises each of those functions f
 * 
 * Does the same for continuations
 *)

structure CPSSimpleArityRaising : sig

   val raise_arities : CPS.comp_unit -> CPS.comp_unit option

   type stats = {intro_arg_count : int}
   val stats : unit -> stats

end = struct

   type stats = {intro_arg_count : int}
   val st = ref {intro_arg_count=0}
   fun stats () = !st
   fun incr_intro_arg_count n = let
      val {intro_arg_count=intro_arg_count} = !st
   in st := {intro_arg_count=intro_arg_count + n}
   end

   structure C = CPS
   structure LVT = LVar.Tbl
   structure CVT = CVar.Tbl

   datatype shape = Unconstrained
                  | Tuple of int
                  | Overconstrained

   (* get the functions f that are only used in function position and
      are given a tuple at all call sites that can be raised *)
   fun candidate_functions (C.CU lam0) = let
       val lvarCheck : shape list LVT.hash_table = LVT.mkTable (100, Fail "CPSSimpleArityRaising.lvarCheck")
       val cvarCheck : shape list CVT.hash_table = CVT.mkTable (100, Fail "CPSSimpleArityRaising.cvarCheck")
       val lvarShape : LVar.t list LVT.hash_table = LVT.mkTable (100, Fail "CPSSimpleArityRaising.lvarShape")
       val lvarOnlySelected : unit LVT.hash_table = LVT.mkTable (100, Fail "CPSSimpleArityRaising.lvarOnlySelected")
       fun kill_lvar x =
           case LVT.find lvarCheck x
            of NONE => ()
             | _ => (LVT.remove lvarCheck x; ())
       fun kill_cvar k =
           case CVT.find cvarCheck k
            of NONE => ()
             | _ => (CVT.remove cvarCheck k; ()) 
       fun not_selected x =
           case LVT.find lvarOnlySelected x
            of SOME () => (LVT.remove lvarOnlySelected x; ())
             | NONE => ()
       fun unify_one (par, arg) =
           case (par : shape, LVT.find lvarShape arg : LVar.t list option)
            of (Overconstrained, _) => Overconstrained
             | (_, NONE) => Overconstrained
             | (Unconstrained, SOME lst) => Tuple (List.length lst)
             | (Tuple n, SOME lst) =>
               (* the type system should ensure that they are the same length *)
               if List.length lst = n then Tuple n else Overconstrained
       fun unify (f, args) =
           case LVT.find lvarCheck f
            of NONE => ()
             | SOME pars => let
                 val pars = ListPair.map unify_one (pars, args)
             in LVT.insert lvarCheck (f, pars) end
       fun unify_c (k, args) =
           case CVT.find cvarCheck k
            of NONE => ()
             | SOME pars => let
                 val pars = ListPair.map unify_one (pars, args)
             in CVT.insert cvarCheck (k, pars) end
       fun candidate_exp (exp as C.EXP (lab_e, e)) =
           case e
	    of C.LETFUN(bindings, body) => let
                fun handle_bind (f, _, xs, _, _) = let
                    fun handle_param x =
                        (case LVar.typeOf x
                          of CPSTypes.TyScheme (_, CPSTypes.TupleTy _) => Unconstrained
                           | _ => Overconstrained)
                    val shapes = List.map handle_param xs
                in LVT.insert lvarCheck (f, shapes) end
                val _ = List.app handle_bind bindings
                val _ = List.app candidate_lam bindings
                fun ensureConservative (f, _, xs, _, _) = let
                    fun handle_pair (x, shape) =
                        if LVT.inDomain lvarOnlySelected x
                        then shape
                        else Overconstrained
                in (case LVT.find lvarCheck f
                    of SOME shapes => let
                        val shapes = ListPair.map handle_pair (xs, shapes)
                    in LVT.insert lvarCheck (f, shapes) end
                     | NONE => ())
                end
                val _ = List.app ensureConservative bindings
            in candidate_exp body end
	     | C.LETCONT(bindingKs, body) => let
                 fun handle_bindK (k, _, xs, _) = let
                     fun handle_param x =
                         (case LVar.typeOf x
                           of CPSTypes.TyScheme (_, CPSTypes.TupleTy _) => Unconstrained
                            | _ => Overconstrained)
                     val shapes = List.map handle_param xs
                 in CVT.insert cvarCheck (k, shapes) end
                 val _ = List.app handle_bindK bindingKs
                 val _ = List.app candidate_lamK bindingKs
                 fun ensureConservative (k, _, xs, _) = let
                     fun handle_pair (x, shape) =
                         if LVT.inDomain lvarOnlySelected x
                         then shape
                         else Overconstrained
                 in (case CVT.find cvarCheck k
                      of SOME shapes => let
                          val shapes = ListPair.map handle_pair (xs, shapes)
                      in CVT.insert cvarCheck (k, shapes) end
                       | NONE => ())
                 end
                 val _ = List.app ensureConservative bindingKs
             in candidate_exp body end
	    | C.IF(oper, args, thn, els) => 
              (List.app kill_lvar args;
	       List.app not_selected args;
	       candidate_exp thn;
	       candidate_exp els)
	    | C.ATOM (arg, x, e') => let
                val _ = case arg 
                         of C.LVAR (y, ty) =>
                            (kill_lvar y;
	                     not_selected y;
                             (case LVT.find lvarShape y
                               of NONE => ()
                                | SOME shape => LVT.insert lvarShape (x, shape)))
                          | C.UNIT => LVT.insert lvarShape (x, [])
                          | _ => ()
	    in candidate_exp e' end
	    | C.PURE (oper, args, x, e') =>
              (List.app kill_lvar args;
	       List.app not_selected args;
               candidate_exp e')
	    | C.ARITH (oper, args, x, e', e_exn) => 
              (List.app kill_lvar args;
               List.app not_selected args;
               candidate_exp e';
               candidate_exp e_exn)
	    | C.GET (oper, args, x, e') =>
              (List.app kill_lvar args;
	       List.app not_selected args;
               candidate_exp e')
	    | C.SET (oper, args, x, e') => 
              (List.app kill_lvar args;
	       List.app not_selected args;
               candidate_exp e')
	    | C.TUPLE(args, x, e') => 
              (List.app kill_lvar args;
	       List.app not_selected args;
               LVT.insert lvarShape (x, args);
               candidate_exp e')
	    | C.SELECT(offset, arg, x, e') => 
              (kill_lvar arg;
              (* Don't be smart here, just let redundant selection elmination take care of it *)
               candidate_exp e')
	    | C.DCAPPLY(dcon, tys, arg, x, e') => 
              (kill_lvar arg;
	       not_selected arg;
               candidate_exp e')
	    | C.SWITCH(arg, pats) => 
              (kill_lvar arg;
	       not_selected arg;
               List.app (fn (_, e') => candidate_exp e') pats)
	    | C.APPLY(f, tys, args, argKs) => 
              (List.app kill_lvar args;
	       List.app not_selected args;
               List.app kill_cvar argKs;
               unify (f, args))
	    | C.THROW(k, args) => 
              (List.app kill_lvar args;
	       List.app not_selected args;
               unify_c (k, args))
	  (* end case *)
       and candidate_lam (_, _, xs, _, body) =
           (List.app (fn x => LVT.insert lvarOnlySelected (x, ())) xs;
            candidate_exp body)
       and candidate_lamK (_, _, xs, body) = 
           (List.app (fn x => LVT.insert lvarOnlySelected (x, ())) xs;
            candidate_exp body)
   in candidate_lam lam0;
      (lvarCheck, cvarCheck, lvarShape)
   end
                    
   fun modify (C.CU lam0, lvarCheck, cvarCheck, lvarShape) = let
       val has_changed = ref false
       fun changed () = (has_changed := true)
       val lvarRetyped = LVT.mkTable (100, Fail "CPSSimpleArityRaising.lvarRetyped")
       val cvarRetyped = CVT.mkTable (100, Fail "CPSSimpleArityRaising.cvarRetyped")
       fun getType x = let
           val CPSTypes.TyScheme (_, ty) = LVar.typeOf x
       in ty end
       fun rename x = case LVT.find lvarRetyped x of NONE => x | SOME x' => x'
       fun rename_lst xs = List.map rename xs
       fun renameK k = case CVT.find cvarRetyped k of NONE => k | SOME k' => k'
       fun renameK_lst ks = List.map renameK ks
       fun expand_args (args, data) = let
           fun fold (arg, data, acc) =
               case data
                of Tuple n => (changed (); (rename_lst (LVT.lookup lvarShape arg)) @ acc)
                 | _ => (rename arg) :: acc
       in ListPair.foldr fold [] (args, data) end
       fun expand_params_and_introduce_tuples (xs, body, data) = let
           fun newLVar (x, tys) i =
               LVar.newTmp ((LVar.nameOf x) ^ "[" ^ (Int.toString i) ^ "]",
                            CPSTypes.TyScheme ([], List.nth (tys, i)),
                            Extent.HEAP)
               handle Subscript => let
                   val tys_str = String.concatWith " " (List.map CPSTypes.toString tys)
               in (Verbose.say [tys_str, " ", Int.toString i, "\n"]; raise Subscript) end
           fun fold (x, data, (xs, body)) =
               case data
                of Tuple n => let
                    (* TODO: not sure if the type vars should be empty here *)
                    val CPSTypes.TyScheme ([], CPSTypes.TupleTy tys) = LVar.typeOf x
                    val ys = List.tabulate (n, newLVar (x, tys))
                    val body = if List.length ys = 0
                               then (fn () => C.mkATOM (C.UNIT, rename x, body ()))
                               else (fn () => C.mkTUPLE (ys, rename x, body ()))
                    val _ = changed ()
                    val _ = incr_intro_arg_count (List.length ys)
                in (ys @ xs, body) end
                 | _ => ((rename x) :: xs, body)
       in ListPair.foldr fold ([], body) (xs, data) end
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
               (case LVT.find lvarCheck f
                 of NONE => C.APPLY (rename f, tys, rename_lst args, renameK_lst argKs)
                  | SOME data => C.APPLY (rename f, tys, expand_args (args, data), renameK_lst argKs))
	     | C.THROW(k, args) => 
               (case CVT.find cvarCheck k
                 of NONE => C.THROW (renameK k, rename_lst args)
                  | SOME data => C.THROW (renameK k, expand_args (args, data)))
       (* end case *))
       and modify_lam (lam as (f, lam_lab, xs, ks, body)) =
           case LVT.find lvarCheck f
            of NONE => (fn () => (rename f, lam_lab, xs, ks, modify_exp body) )
             | SOME data => let
                 (* introduce tuples in the body, 
                    and then clean them up using redundant selection elimination *)
                 val (xs, body) = expand_params_and_introduce_tuples (xs, fn () => modify_exp body, data)
                 val CPSTypes.TyScheme (sch, CPSTypes.FunTy (_, ctys)) = LVar.typeOf f
                 val ty = CPSTypes.TyScheme (sch, CPSTypes.FunTy (List.map getType xs, ctys))
                 val f' = LVar.newTmp (LVar.nameOf f, ty, LVar.extentOf f)
                 val _ = LVT.insert lvarRetyped (f, f')
             in (fn () => (f', lam_lab, xs, ks, body ())) end
       and modify_lamK (lamK as (k, lamK_lab, xs, body)) = 
           case CVT.find cvarCheck k
            of NONE => (fn () => (renameK k, lamK_lab, xs, modify_exp body))
             | SOME data => let
                 (* introduce tuples in the body, 
                    and then clean them up using redundant selection elimination *)
                 val (xs, body) = expand_params_and_introduce_tuples (xs, fn () => modify_exp body, data)
                 val tys = List.map getType xs
                 val k' = CVar.newTmp (CVar.nameOf k, CPSTypes.ContTy tys, CVar.extentOf k)
                 val _ = CVT.insert cvarRetyped (k, k')
             in (fn () => (k', lamK_lab, xs, body ())) end
   in (C.CU (modify_lam lam0 ()), !has_changed) end

   fun raise_arities cu = let
       val (lvarCheck, cvarCheck, lvarShape) = candidate_functions cu
       val (cu, changed) = modify (cu, lvarCheck, cvarCheck, lvarShape)
   in if changed
      then SOME cu
      else NONE
   end

end
