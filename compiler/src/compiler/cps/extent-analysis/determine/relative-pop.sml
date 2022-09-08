(* relative-pop.sml
 *
 * computes at continuation and tail call sites when the pop is a
 * "relative pop"; that is, when the only popped frame is the current
 * one.
 *)

structure DetermineRelativePop : DETERMINE_INFO =
struct

  structure C = CPS
  structure U = TransitionUtil
  structure LS = Label.Set

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      (* the continuation values at a call or continuation call give a
         relative pop if there is continuation closure being called
         locally in the function or if there if the continuation
         closure being called is always on the previous call's proxy *)
      fun isRelativePop_dKs (dKs, aP) =
          if List.exists U.valueK_isCloK dKs
          then true
          else let
              val indices = List.map U.valueK_indexOf dKs
              val dP = StoreProxy.lookup (storeP, aP)
              fun localPopProxy (proxy, acc) = let
                  val (_, dKs', _) = Proxy.get proxy
              in acc andalso (List.exists U.valueK_isCloK (U.select (indices, dKs'))) end
          in (not (ValueProxy.isUnknown dP))
             andalso (ValueProxy.fold_proxy localPopProxy true dP) end
      fun chkConfig (xi, relativePop) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.APPLY (_, _, _, argKs) => let
               val dKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
           in if isRelativePop_dKs (dKs, aP)
              then relativePop
              else LS.subtract (relativePop, lab_e)
           end
            | C.THROW (k, _) => let
                val dKs = [U.evalCVar (k, envK, storeK)]
            in if isRelativePop_dKs (dKs, aP)
               then relativePop
               else LS.subtract (relativePop, lab_e)
            end
            | _ => relativePop
      end
      val relativePop = LS.fromList (PInfo.call_sites pinfo)
      val relativePop = LS.addList (relativePop, PInfo.callK_sites pinfo)
      val relativePop = Config.Set.foldl chkConfig relativePop configs
      val ainfo = AInfo.with_relativePop (ainfo, relativePop)
  in ainfo end

end (* RelativePop *)



