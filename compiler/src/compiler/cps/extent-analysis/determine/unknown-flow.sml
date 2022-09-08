(* unknown-flow.sml
 *
 * Determines which variables unknown flows to.
 *)

structure DetermineUnknownFlow :> DETERMINE_INFO =
  struct

  structure C = CPS
  structure PInfo = CPSInformation

  structure AInfo = AnalysisInformation
  structure U = TransitionUtil

  structure LVS = LVar.Set
  structure CVS = CVar.Set

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val sideEffectVars = #sideEffectVars (#util_addrs state_space)

      val unknownLVars = ref LVS.empty
      val unknownCVars = ref CVS.empty
      fun addUnknownLVar (x) = (unknownLVars := LVS.add (!unknownLVars, x))
      fun addUnknownCVar (x) = (unknownCVars := CVS.add (!unknownCVars, x))

      val (C.CU (_, _, xs0, ks0, _)) = #cu analysis_space
      val () = List.app addUnknownLVar xs0
      val () = List.app addUnknownCVar ks0

      fun handle_config (xi, ()) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
       of C.LETFUN (bindings, body) => ()
        | C.LETCONT (bindingKs, body) => ()
        | C.IF (oper, args, thn, els) => ()
        | C.ATOM (arg, x, e') => let
            val d = U.evalAtom (lab_e, (fn _ => ()), arg, env, store)
            val () = Value.fold_unknown (fn () => addUnknownLVar x) () d
        in () end
        | C.PURE (oper, args, x, e') => let
            val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
            val (d, _) = U.performPurePrim (sideEffectVars, lab_e, oper, d_args, tenv, aP, [])
            val () = Value.fold_unknown (fn () => addUnknownLVar x) () d
        in () end
        | C.ARITH (oper, args, x, e', e_exn) => let
            val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
            val d = U.performArithPrim (oper, d_args)
            val () = Value.fold_unknown (fn () => addUnknownLVar x) () d
        in () end
        | C.GET (oper, args, x, e') => let
            val d_args = List.map (fn arg => U.evalLVar_add (fn _ => (), arg, env, store)) args
            val _ = U.performGetPrim (fn (a_ref, _) =>
                                         (case Store.find (store, a_ref)
                                           of SOME d_get => Value.fold_unknown (fn () => addUnknownLVar x) () d_get
                                            | NONE => ()))
                                              ()
                                              (oper, d_args)
        in () end
        | C.SET (oper, args, x, e') => let
            val d_args = List.map (fn arg => U.evalLVar_add (fn _ => (), arg, env, store)) args
            val (d, _, _) = U.performSetPrim (oper, d_args, [])
            val () = Value.fold_unknown (fn () => addUnknownLVar x) () d
        in () end
        | C.TUPLE (args, x, e') => ()
        | C.SELECT (offset, arg, x, e') => let
            val d_arg = U.evalLVar_add (fn _ => (), arg, env, store)
            val _ = Value.select_offset (fn (a_sel, _) => let
                                             val d_sel = Store.lookup (store, a_sel)
                                         in Value.fold_unknown (fn () => addUnknownLVar x) () d_sel end)
                                        ()
                                        (offset, d_arg)
        in () end
        | C.DCAPPLY (dcon, tys, arg, x, e') => ()
        | C.SWITCH (arg, pats) => let
            val d_arg = U.evalLVar_add (fn _ => (), arg, env, store)
            (* More precise would be to handle each dv in d_arg and 
               find the pat that it goes to, then make the transition.
               That way we could find dead code / branches. 
               However, I think most of the time all branches are used, 
               so we do the less precise thing here. *)
            (* we could also just do the analysis on the argument
               after computing the state space *)
            fun doCase ((pat, exp'), ()) =
                (case pat
                  of C.VPAT x => let
                      val () = Value.fold_unknown (fn () => addUnknownLVar x) () d_arg
                  in () end
                   | C.DCPAT(dcon, _, SOME x) => let
                       val _ = Value.match_dcon (fn (a_get, _) => let
                                                     val d_get = Store.lookup (store, a_get)
                                                 in Value.fold_unknown (fn () => addUnknownLVar x) () d_get end)
                                                ()
                                                (dcon, d_arg)
                   in () end
                   | _ => ()
                (* end case *))
            val () = List.foldl doCase () pats
        in () end

        | C.APPLY (f, tys, args, argKs) => let
            val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
            val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
            val d_f = U.evalLVar_add (fn _ => (), f, env, store)
            val d_args = List.map (fn arg => U.evalLVar_add (fn _ => (), arg, env, store)) args
            val dK_argKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
            val dK_unknowns = List.map (fn dK => let
                                            val (_, any_unknown) = U.cloKOf (fn _ => (), dK, aP, storeP)
                                        in any_unknown end)
                                       dK_argKs
            fun handle_clo (clo, ()) = let
                val (lam as (_, lam_lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
                val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
            in
                case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                 of NONE => ()
                  | SOME tenv' => let
                      val () = ListPair.app (fn (x, d_arg) => Value.fold_unknown (fn () => addUnknownLVar x) () d_arg) (xs, d_args)
                      val () = ListPair.app (fn (k, any_unknown) => if any_unknown then addUnknownCVar k else ()) (ks, dK_unknowns)
                  in () end
            end
            val () = Value.fold_clos handle_clo () d_f
        in () end
        | C.THROW (k, args) => let
            val k_cty = U.instantiateCTy (tenv, CVar.typeOf k)
            val d_args = List.map (fn arg => U.evalLVar_add (fn _ => (), arg, env, store)) args
            val dK = U.evalCVar (k, envK, storeK)
            val (cloK_aPs, any_unknown) = U.cloKOf (fn _ => (), dK, aP, storeP)
            fun handle_cloK_aP ((cloK, aP'), ()) = let
                val (lamK as (_, lamK_lab, xs, body), env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
                val cloK_ty = CPSTypes.ContTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs)
                val cloK_ty = U.instantiateCTy (tenv_cloK, cloK_ty)
            in
                case U.unifyCont (tenv_cloK, k_cty, cloK_ty)
                 of NONE => ()
                  | SOME _ => let
                      val () = ListPair.app (fn (x, d_arg) => Value.fold_unknown (fn () => addUnknownLVar x) () d_arg) (xs, d_args)
                  in () end
            end
            val () = List.foldl handle_cloK_aP () cloK_aPs
        in () end
      end
      val () = Config.Set.foldl handle_config () configs
      val ainfo = AInfo.with_unknownLVars (ainfo, !unknownLVars)
      val ainfo = AInfo.with_unknownCVars (ainfo, !unknownCVars)
  in ainfo end

end
