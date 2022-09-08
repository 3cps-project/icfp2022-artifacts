(* determine-call-webs.sml
 *
 * Determines call web information from the given state space,
 * for both user lambdas and call sites and cont lambdas and call sites.
 *)

structure DetermineCallWebs :> DETERMINE_INFO =
  struct

  structure C = CPS
  structure PInfo = CPSInformation

  structure AInfo = AnalysisInformation
  structure U = TransitionUtil

  structure LM = Label.Map
  structure LS = Label.Set

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space

      fun addUnknown (map, x) = let
          val (prev, _) = LM.lookup (map, x)
      in LM.insert (map, x, (prev, true)) end
      fun addMap (map, x, l) = let
          val (prev, unknown) = LM.lookup (map, x)
      in LM.insert (map, x, (LS.add (prev, l), unknown)) end

      fun handle_config (xi, (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK)) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.APPLY (f, tys, args, argKs) => let
               val d = U.evalLVar (f, env, store)
               fun handle_clo (clo, (callWebs, lamToCall, callToLam)) = let
                   val ((_, lam_lab, _, _, _), _, _) = Clo.get clo
                   val callWebs = CallWebs.add (callWebs, {call=lab_e, lambda=lam_lab})
                   val lamToCall = addMap (lamToCall, lam_lab, lab_e)
                   val callToLam = addMap (callToLam, lab_e, lam_lab)
               in (callWebs, lamToCall, callToLam) end
               fun handle_unknown (callWebs, callToLam) = let
                   val callWebs = CallWebs.add_unknown_lam (callWebs, {call=lab_e})
                   val callToLam = addUnknown (callToLam, lab_e)
               in (callWebs, callToLam) end
               val (callWebs, lamToCall, callToLam) = Value.fold_clos handle_clo (callWebs, lamToCall, callToLam) d
               val (callWebs, callToLam) = Value.fold_unknown handle_unknown (callWebs, callToLam) d
               in (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK) end
            | C.THROW(k, args) => let
                val dK = U.evalCVar (k, envK, storeK)
                val (cloK_aPs, any_unknown) = U.cloKOf (fn _ => (), dK, aP, storeP)
                fun handle_cloK_aP ((cloK, _), (callWebsK, lamKToCallK, callKToLamK)) = let
                    val ((_, lamK_lab, _, _), _, _, _) = CloK.get cloK
                    val callWebsK = CallWebs.add (callWebsK, {call=lab_e, lambda=lamK_lab})
                    val lamKToCallK = addMap (lamKToCallK, lamK_lab, lab_e)
                    val callKToLamK = addMap (callKToLamK, lab_e, lamK_lab)
                in (callWebsK, lamKToCallK, callKToLamK) end
                val (callWebsK, lamKToCallK, callKToLamK) = List.foldl handle_cloK_aP (callWebsK, lamKToCallK, callKToLamK) cloK_aPs
                val (callWebsK, callKToLamK) =
                    if any_unknown
                    then let
                        val callWebsK = CallWebs.add_unknown_lam (callWebsK, {call=lab_e})
                        val callKToLamK = addUnknown (callKToLamK, lab_e)
                    in (callWebsK, callKToLamK) end
                    else (callWebsK, callKToLamK)
                in (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK) end
            | _ => (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK)
      end
      fun handle_ld_passed_to_unknown (ld, (callWebs, lamToCall)) =
          if PInfo.ld_is_lam pinfo ld
          then let
              val callWebs = CallWebs.add_unknown_call (callWebs, {lam=ld})
              val lamToCall = addUnknown (lamToCall, ld)
          in (callWebs, lamToCall) end
          else (callWebs, lamToCall)
      fun handle_cd_passed_to_unknown (cd, (callWebsK, lamKToCallK)) =
          if PInfo.cd_is_lamK pinfo cd
          then let
              val callWebsK = CallWebs.add_unknown_call (callWebsK, {lam=cd})
              val lamKToCallK = addUnknown (lamKToCallK, cd)
          in (callWebsK, lamKToCallK) end
          else (callWebsK, lamKToCallK) 
      val ld_passed_to_unknown = #ldata_passed_to_unknown state_space
      val cd_passed_to_unknown = #cdata_passed_to_unknown state_space
      val callWebs = CallWebs.initial {lams=PInfo.lams pinfo, calls=PInfo.call_sites pinfo}
      val callWebsK = CallWebs.initial {lams=PInfo.lamKs pinfo, calls=PInfo.callK_sites pinfo}
      fun init lst = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lst
      val lamToCall = init (PInfo.lams pinfo)
      val callToLam = init (PInfo.call_sites pinfo)
      val lamKToCallK = init (PInfo.lamKs pinfo)
      val callKToLamK = init (PInfo.callK_sites pinfo)
      val (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK) =
            Config.Set.foldl handle_config (callWebs, callWebsK, lamToCall, callToLam, lamKToCallK, callKToLamK) configs
      val (callWebs, lamToCall) = Label.Set.foldl
            handle_ld_passed_to_unknown (callWebs, lamToCall) ld_passed_to_unknown
      val (callWebsK, lamKToCallK) = Label.Set.foldl
            handle_cd_passed_to_unknown (callWebsK, lamKToCallK) cd_passed_to_unknown
      val ainfo = AInfo.with_callWebs (ainfo, callWebs)
      val ainfo = AInfo.with_callWebsK (ainfo, callWebsK)
      val ainfo = AInfo.with_funInfo (ainfo, {lamToCall=lamToCall, callToLam=callToLam})
      val ainfo = AInfo.with_funKInfo (ainfo, {lamKToCallK=lamKToCallK, callKToLamK=callKToLamK})
  in ainfo end

end
