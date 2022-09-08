(* extent-criteria.sml
 *
 * Finds the pairs that satisfy the extent criteria.
 *)

structure DetermineExtentCriteria : DETERMINE_INFO =
struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure LM = Label.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation
  structure U = TransitionUtil

  structure B = Binding
  structure BS = Binding.Set

  val timerLiveChecks = PhaseTimer.newPhase (Timers.timeExtAnalysisDetermineExt, "live queries")
  fun doTimer timer f arg =
      PhaseTimer.withTimer timer f arg

  fun returnValues pinfo (xi, store, storeK, storeP)
      : Addr.t list * Label.t list * Label.Set.set = let
      val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
  in case e
       of C.APPLY (f, tys, args, argKs) => let
              val dKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
              val proxy = (exp, dKs, aP)
              val poppedProxies_pop_sites = U.poppedProxies (proxy, storeP)
              val ds = List.map (fn arg => Env.lookup (env, arg)) (f :: args)
          in (ds, PInfo.local_pop pinfo lab_e, poppedProxies_pop_sites) end
        | C.THROW(k, args) => let
              val dK = U.evalCVar (k, envK, storeK)
              val poppedProxies_pop_sites = U.poppedProxies_valueK (dK, aP, storeP)
              val ds = List.map (fn arg => Env.lookup (env, arg)) args
           in (ds, PInfo.local_pop pinfo lab_e, poppedProxies_pop_sites) end
        | _ => ([], [], LS.empty)
  end

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val sideEffectVars = #sideEffectVars (#utilAddrs analysis_space)
      val pinfo = #pinfo analysis_space
      val liveMemo = #liveMemo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val ldata_passed_to_unknown = #ldata_passed_to_unknown state_space
      val live_b_base = Live.live_b liveMemo
      fun live_b query = doTimer timerLiveChecks live_b_base query
      val live_ld_base = Live.live_ld liveMemo
      fun live_ld query = doTimer timerLiveChecks live_ld_base query
      val lams = PInfo.lams pinfo
      val fv_lam_lv = PInfo.fv_lam_lv pinfo
      val choices_lv = PInfo.alloc_loc_choices_lv pinfo
      val choices_ld = PInfo.alloc_loc_choices_ld pinfo
      fun remove_from_lv alloc_locs (x, crit) =
          LVM.insert (crit, x, LS.subtractList (LVM.lookup (crit, x), alloc_locs))
      fun remove_from_ld alloc_locs (ld, crit) =
          LM.insert (crit, ld, LS.subtractList (LM.lookup (crit, ld), alloc_locs))
      fun chkConfig (xi, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) = let
          val (a_rets, local_popped, pop_sites) = returnValues pinfo (xi, store, storeK, storeP)
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in if LS.isEmpty pop_sites andalso List.null local_popped
         then (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
         else let
             val bs_list = live_b (NONE, a_rets, [])
             val lds_list = live_ld (NONE, a_rets, [])
             (* for each pop site (a call site), grab all the frames allocated from that user lambda up to the call site *)
             val popped_frames_list = List.map (PInfo.pop_past pinfo) (LS.toList pop_sites) 
             (* also, grab the local pops for the current pop *)
             val popped_frames_list = local_popped :: popped_frames_list
             fun pop (popped_frames, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) = let
                 val local_popped_alloc_locs = popped_frames
                 fun handle_pop_lv alloc_loc (x, (crit_birth_lv, crit_death_lv)) =
                     if List.exists (fn bs => BS.exists (fn (y, a) => LVar.same (x, y)) bs) bs_list
                     then (crit_birth_lv, remove_from_lv [alloc_loc] (x, crit_death_lv))
                     else (crit_birth_lv, crit_death_lv)
                 fun handle_pop_ld alloc_loc (ld, (crit_birth_lv, crit_birth_ld,
                                                   crit_death_lv, crit_death_ld)) =
                     if List.exists (fn lds => LS.member (lds, ld)) lds_list
                     then let
                         val crit_death_ld =
                             remove_from_ld [alloc_loc] (ld, crit_death_ld)
                     in if PInfo.ld_is_lam pinfo ld
                        then let
                            val crit_birth_lv = List.foldl (remove_from_lv [alloc_loc]) crit_birth_lv (choices_lv ld)
                            val crit_birth_ld = List.foldl (remove_from_ld [alloc_loc]) crit_birth_ld (choices_ld ld)
                        in (crit_birth_lv, crit_birth_ld,
                            crit_death_lv, crit_death_ld) end
                        else (crit_birth_lv, crit_birth_ld,
                              crit_death_lv, crit_death_ld)
                     end
                     else (crit_birth_lv, crit_birth_ld,
                           crit_death_lv, crit_death_ld)
                 fun handle_alloc_loc_lv (alloc_loc, acc) =
                     List.foldl (handle_pop_lv alloc_loc) acc (choices_lv alloc_loc)
                 fun handle_alloc_loc_ld (alloc_loc, acc) =
                     List.foldl (handle_pop_ld alloc_loc) acc (choices_ld alloc_loc)
                 val (crit_birth_lv, crit_death_lv) =
                     List.foldl handle_alloc_loc_lv (crit_birth_lv, crit_death_lv) local_popped_alloc_locs
                 val (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) =
                     List.foldl handle_alloc_loc_ld (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) local_popped_alloc_locs
             in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end

             val (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) =
                 List.foldl pop (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) popped_frames_list
         in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end
      end

      fun killExtents insert (x, extentCrit) = insert (extentCrit, x, LS.empty)

      (* remove every allocation contained in the lam from
         the lam as well as all frames contained in the lam *)
      fun killLam (lam_lab, crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) = let
          (* val to_remove = PInfo.cn_ld_lam pinfo lam_lab *)
          (* fun remove_from labs = LS.difference (labs, to_remove) *)
          (* could do better here, though it doesn't matter atm *)
          fun killLV (x, (crit_birth_lv, crit_death_lv)) =
              (LVM.insert (crit_birth_lv, x, LS.empty),
               LVM.insert (crit_death_lv, x, LS.empty))
          fun killLD (ld, (crit_birth_ld, crit_death_ld)) =
              (LM.insert (crit_birth_ld, ld, LS.empty),
               LM.insert (crit_death_ld, ld, LS.empty))
          val (crit_birth_lv, crit_death_lv) =
              List.foldl killLV (crit_birth_lv, crit_death_lv) (choices_lv lam_lab)
          val (crit_birth_ld, crit_death_ld) =
              List.foldl killLD (crit_birth_ld, crit_death_ld) (choices_ld lam_lab)
      in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end

      (* any ldata which is passed to the unknown and any variable
         that is passed to the unknown (i.e. is closed over in a closure)
         cannot be given any extent except for H.
         Additionally, for any closures passed to the unknown, any
         bindings or values allocated in those closures cannot be
         allocated on any frames that contain the closure. *)
      fun handlePassedToUnknown extentCrits = let
          fun handleLD (ld, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) = let
              val crit_birth_ld = killExtents LM.insert (ld, crit_birth_ld)
              val crit_death_ld = killExtents LM.insert (ld, crit_death_ld)
              val crit_birth_lv =
                  if PInfo.ld_is_lam pinfo ld
                  then LVS.foldl (killExtents LVM.insert) crit_birth_lv (fv_lam_lv ld)
                  else crit_birth_lv
              val crit_death_lv =
                  if PInfo.ld_is_lam pinfo ld
                  then LVS.foldl (killExtents LVM.insert) crit_death_lv (fv_lam_lv ld)
                  else crit_death_lv
              val (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) =
                  if PInfo.ld_is_lam pinfo ld
                  then killLam (ld, crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
                  else (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
          in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end
      in LS.foldl handleLD extentCrits ldata_passed_to_unknown end

      (* For now, we don't know anything about any binding/closure reachable via a ref/array *)
      fun handleSideEffects extentCrit = 
          extentCrit
      (* TODO: write a separate function to go over the configs and
         grab the created ref addrs, or track them during generation *)
      (*
      fun handleSideEffects extentCrit = let
          fun handleSideEffect (_, a, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) =
              case Store.find (store, a)
               of NONE => (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
                | SOME _ => let
                    val bs_list = live_b (NONE, [a], [])
                    val lds_list = live_ld (NONE, [a], [])
                    val (crit_birth_lv, crit_death_lv) =
                        List.foldl (fn (bs, (crit_birth_lv, crit_death_lv)) =>
                                       Binding.Set.foldl
                                           (fn ((x, a), (crit_birth_lv, crit_death_lv)) =>
                                               (killExtents LVM.insert (x, crit_birth_lv),
                                                killExtents LVM.insert (x, crit_death_lv)))
                                           (crit_birth_lv, crit_death_lv) bs)
                                   (crit_birth_lv, crit_death_lv) bs_list
                    val (crit_birth_ld, crit_death_ld) =
                        List.foldl (fn (lds, (crit_birth_ld, crit_death_ld)) =>
                                       (LS.foldl (killExtents LM.insert) crit_birth_ld lds,
                                        LS.foldl (killExtents LM.insert) crit_death_ld lds))
                                   (crit_birth_ld, crit_death_ld) lds_list
                in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end
      in LM.foldli handleSideEffect extentCrit sideEffectVars end
      *)

      fun findExtentCrits extentCrit = let
          val extentCrit = Config.Set.foldl chkConfig extentCrit configs
          val extentCrit = handlePassedToUnknown extentCrit
          val extentCrit = handleSideEffects extentCrit
      in extentCrit end

      fun initial_crit_lv pinfo = let
          fun add alloc_loc (x, acc) =
              LVM.insert (acc, x, LS.add (LVM.lookup (acc, x), alloc_loc))
          fun handle_alloc_loc (alloc_loc, acc) =
              List.foldl (add alloc_loc) acc (PInfo.alloc_loc_choices_lv pinfo alloc_loc)
          val crit =
              List.foldl (fn (x, acc) => LVM.insert (acc, x, LS.empty)) LVM.empty (PInfo.lvars pinfo)
          val crit =
              List.foldl handle_alloc_loc crit (PInfo.alloc_locs pinfo)
      in crit end
      fun initial_crit_ld pinfo = let
          fun add alloc_loc (x, acc) =
              LM.insert (acc, x, LS.add (LM.lookup (acc, x), alloc_loc))
          fun handle_alloc_loc (alloc_loc, acc) =
              List.foldl (add alloc_loc) acc (PInfo.alloc_loc_choices_ld pinfo alloc_loc)
          val crit =
              List.foldl (fn (x, acc) => LM.insert (acc, x, LS.empty)) LM.empty (PInfo.ldata pinfo)
          val crit =
              List.foldl handle_alloc_loc crit (PInfo.alloc_locs pinfo)
      in crit end
      val crit_birth_lv = initial_crit_lv pinfo
      val crit_birth_ld = initial_crit_ld pinfo
      val crit_death_lv = initial_crit_lv pinfo
      val crit_death_ld = initial_crit_ld pinfo
      val (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) =
          findExtentCrits (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
      val ainfo = AInfo.with_crit_birth_lv (ainfo, crit_birth_lv)
      val ainfo = AInfo.with_crit_birth_ld (ainfo, crit_birth_ld)
      val ainfo = AInfo.with_crit_death_lv (ainfo, crit_death_lv)
      val ainfo = AInfo.with_crit_death_ld (ainfo, crit_death_ld)
  in ainfo end

end (* ExtentCriteria *)


