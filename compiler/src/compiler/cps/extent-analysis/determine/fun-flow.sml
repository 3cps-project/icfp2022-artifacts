(* fun-flow.sml
 *
 * Determines function flow information from the given state space,
 * i.e. which functions (continuations) flow to which call (throw) sites
 *)

structure DetermineFunFlow :> DETERMINE_INFO =
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

      fun handle_config (xi, (lamToCall, callToLam, lamKToCallK, callKToLamK)) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.APPLY (f, tys, args, argKs) => let
               val d = U.evalLVar (f, env, store)
               fun handle_clo (clo, (lamToCall, callToLam)) = let
                   val ((_, lam_lab, _, _, _), _, _) = Clo.get clo
                   val lamToCall = addMap (lamToCall, lam_lab, lab_e)
                   val callToLam = addMap (callToLam, lab_e, lam_lab)
               in (lamToCall, callToLam) end
               fun handle_unknown callToLam = let
                   val callToLam = addUnknown (callToLam, lab_e)
               in callToLam end
               val (lamToCall, callToLam) = Value.fold_clos handle_clo (lamToCall, callToLam) d
               val callToLam = Value.fold_unknown handle_unknown callToLam d
               in (lamToCall, callToLam, lamKToCallK, callKToLamK) end
            | C.THROW(k, args) => let
                val dK = U.evalCVar (k, envK, storeK)
                val (cloK_aPs, any_unknown) = U.cloKOf (fn _ => (), dK, aP, storeP)
                fun handle_cloK_aP ((cloK, _), (lamKToCallK, callKToLamK)) = let
                    val ((_, lamK_lab, _, _), _, _, _) = CloK.get cloK
                    val lamKToCallK = addMap (lamKToCallK, lamK_lab, lab_e)
                    val callKToLamK = addMap (callKToLamK, lab_e, lamK_lab)
                in (lamKToCallK, callKToLamK) end
                val (lamKToCallK, callKToLamK) = List.foldl handle_cloK_aP (lamKToCallK, callKToLamK) cloK_aPs
                val callKToLamK =
                    if any_unknown
                    then let
                        val callKToLamK = addUnknown (callKToLamK, lab_e)
                    in callKToLamK end
                    else callKToLamK
                in (lamToCall, callToLam, lamKToCallK, callKToLamK) end
            | _ => (lamToCall, callToLam, lamKToCallK, callKToLamK)
      end
      fun handle_ld_passed_to_unknown (ld, lamToCall) =
          if PInfo.ld_is_lam pinfo ld
          then let
              val lamToCall = addUnknown (lamToCall, ld)
          in lamToCall end
          else lamToCall
      fun handle_cd_passed_to_unknown (cd, lamKToCallK) =
          if PInfo.cd_is_lamK pinfo cd
          then let
              val lamKToCallK = addUnknown (lamKToCallK, cd)
          in lamKToCallK end
          else lamKToCallK 
      val ld_passed_to_unknown = #ldata_passed_to_unknown state_space
      val cd_passed_to_unknown = #cdata_passed_to_unknown state_space
      fun init lst = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lst
      val lamToCall = init (PInfo.lams pinfo)
      val callToLam = init (PInfo.call_sites pinfo)
      val lamKToCallK = init (PInfo.lamKs pinfo)
      val callKToLamK = init (PInfo.callK_sites pinfo)
      val (lamToCall, callToLam, lamKToCallK, callKToLamK) =
            Config.Set.foldl handle_config (lamToCall, callToLam, lamKToCallK, callKToLamK) configs
      val lamToCall = Label.Set.foldl
            handle_ld_passed_to_unknown lamToCall ld_passed_to_unknown
      val lamKToCallK = Label.Set.foldl
            handle_cd_passed_to_unknown lamKToCallK cd_passed_to_unknown
      val ainfo = AInfo.with_funInfo (ainfo, {lamToCall=lamToCall, callToLam=callToLam})
      val ainfo = AInfo.with_funKInfo (ainfo, {lamKToCallK=lamKToCallK, callKToLamK=callKToLamK})
  in ainfo end

end
