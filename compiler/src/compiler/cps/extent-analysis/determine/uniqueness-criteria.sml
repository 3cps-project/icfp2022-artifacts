(* uniqueness-criteria.sml
 *
 * Finds the pairs that satisfy the uniqueness criteria.
 *)

structure DetermineUniquenessCriteria : DETERMINE_INFO =
struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure LM = Label.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation
  structure U = TransitionUtil

  structure B = Binding
  structure BS = Binding.Set
  structure AKS = AddrK.Set
  structure AKM = AddrK.Map

  val timerLiveChecks = PhaseTimer.newPhase (Timers.timeExtAnalysisDetermineUniq, "live queries")
  fun doTimer timer f arg =
      PhaseTimer.withTimer timer f arg

  fun noBindingsFor (x, bs) = not (BS.exists (fn (x', a) => LVar.same(x', x)) bs)
  fun noLDataFor (ld, lds) = not (LS.exists (fn ld' => Label.same (ld, ld')) lds)

  exception StopPrecompute of bool

  fun precompute (pinfo, storeP) : Label.Set.set AddrProxy.Map.map = let
      fun handle_aP_lam (aP0, lam_lab, map : Label.Set.set AddrProxy.Map.map, handled_aP) = let
          fun handle_proxy (proxy, (wl, seen)) = let
              val (e, _, aP') = Proxy.get proxy
          in if Label.same (PInfo.exp_lam pinfo (CU.labelOfExp e), lam_lab)
             then raise StopPrecompute true
             else if AddrProxy.Set.member (handled_aP, aP')
             then raise StopPrecompute (LS.member (AddrProxy.Map.lookup (map, aP'), lam_lab))
             else if AddrProxy.Set.member (seen, aP')
             then (wl, seen)
             else (aP' :: wl, AddrProxy.Set.add (seen, aP'))
          end
          fun do_wl (wl, seen) =
              case wl
               of [] => false
                | aP :: rst => let
                    val dP = StoreProxy.lookup (storeP, aP)
                in do_wl (ValueProxy.fold_proxy handle_proxy (rst, seen) dP) end
      in do_wl ([aP0], AddrProxy.Set.singleton aP0) end handle StopPrecompute res => res
      fun handle_aP_dP lam_lab (aP, _, (handled_aP, map)) =
          if handle_aP_lam (aP, lam_lab, map, handled_aP)
          then (AddrProxy.Set.add (handled_aP, aP),
                AddrProxy.Map.insert (map, aP, Label.Set.add (AddrProxy.Map.lookup (map, aP), lam_lab)))
          else (AddrProxy.Set.add (handled_aP, aP), map)

      fun handle_lam (lam_lab, map) = let
          val (_, map) = StoreProxy.foldi (handle_aP_dP lam_lab) (AddrProxy.Set.empty, map) storeP
      in map end
      val initial_map = StoreProxy.foldi (fn (aP, _, map) => AddrProxy.Map.insert (map, aP, LS.empty)) AddrProxy.Map.empty storeP
  in List.foldl handle_lam initial_map (PInfo.lams pinfo) end

  fun search (pinfo, crit_birth_lv, crit_birth_ld, live_b, live_ld, storeK, storeP, aP_map)
             (lam_lab, lvUCrit, ldUCrit, xs0, lds0, addrs0 : Addr.t list, aK_aPs0 : (AddrK.t * AddrProxy.t) list, fv_lv0, fv_cv0, env0, envK0, aP0) = let
      (*
      val _ = Verbose.say ["search:",
                           " ", String.concatWithMap " " LVar.toString xs0,
                           " ", String.concatWithMap " " Label.toString lds0,
                           " ", AddrProxy.toString aP0,
                           "\n"]
      *)
      fun kill_set_all (lam_lab, acc) =
          if Label.same (lam_lab, PInfo.lam_lab0 pinfo)
          then lam_lab :: acc
          else kill_set_all (PInfo.icn_ld_lam pinfo lam_lab, lam_lab :: acc)
      fun kill_set_lv (x, search_lam_lab) = let
          fun lp' (lab, acc) =
              if Label.same (lab, PInfo.lam_lab0 pinfo)
              then lab :: acc
              else lp' (PInfo.icn_ld_lam pinfo lab, lab :: acc)
          fun lp (lab, acc) =
              if Label.same (lab, PInfo.lam_lab0 pinfo)
              then lab :: acc
              else if Label.same (lab, search_lam_lab)
              then lp' (lab, acc)
              else if LS.member (LVM.lookup (crit_birth_lv, x), lab)
              then lp (PInfo.icn_ld_lam pinfo lab, [])
              else lp (PInfo.icn_ld_lam pinfo lab, lab :: acc)
      in lp (PInfo.icn_lv_lam pinfo x, []) end
      fun kill_set_ld (ld, search_lam_lab) = let
          fun lp' (lab, acc) =
              if Label.same (lab, PInfo.lam_lab0 pinfo)
              then lab :: acc
              else lp' (PInfo.icn_ld_lam pinfo lab, lab :: acc)
          fun lp (lab, acc) =
              if Label.same (lab, PInfo.lam_lab0 pinfo)
              then lab :: acc
              else if Label.same (lab, search_lam_lab)
              then lp' (lab, acc)
              else if LS.member (LM.lookup (crit_birth_ld, ld), lab)
              then lp (PInfo.icn_ld_lam pinfo lab, [])
              else lp (PInfo.icn_ld_lam pinfo lab, lab :: acc)
      in lp (PInfo.icn_ld_lam pinfo ld, []) end
      fun kill_lv (x, lvUCrit, kill_list) =
          ((* Verbose.say ["killing x: ", LVar.toString x, "; ", String.concatWithMap " " Label.toString kill_list, "\n"]; *)
           LVM.insert (lvUCrit, x, LS.subtractList (LVM.lookup (lvUCrit, x), kill_list)))
      fun kill_ld (ld, ldUCrit, kill_list) =
          ((* Verbose.say ["killing ld: ", Label.toString ld, "; ", String.concatWithMap " " Label.toString kill_list, "\n"]; *)
           LM.insert (ldUCrit, ld, LS.subtractList (LM.lookup (ldUCrit, ld), kill_list)))
      (* TODO: broken if have recursive continuations *)
      fun handle_cloK_b (cloK, acc) = let
          val (lamK as (_, lab, _, _), env, envK, tenv) = CloK.get cloK
          val fv_lv = PInfo.fv_lamK_lv pinfo lab
          val bs_list = live_b (SOME (fv_lv, CVar.Set.empty, env, EnvK.empty, aP0), [], [])
          val fv_cv = PInfo.fv_lamK_cv pinfo lab
          val bs_list =
              CVar.Set.foldl (fn (k, acc) => handle_dK_b (U.evalCVar (k, envK, storeK), acc)) (bs_list @ acc) fv_cv
      in bs_list end
      and handle_dK_b (dK, acc) =
          case dK
           of ValueK.CLOK cloKs => CloK.Set.foldl handle_cloK_b acc cloKs
            | _ => acc
      fun handle_cloK_ld (cloK, acc) = let
          val (lamK as (_, lab, _, _), env, envK, tenv) = CloK.get cloK
          val fv_lv = PInfo.fv_lamK_lv pinfo lab
          val lds_list = live_ld (SOME (fv_lv, CVar.Set.empty, env, EnvK.empty, aP0), [], [])
          val fv_cv = PInfo.fv_lamK_cv pinfo lab
          val lds_list =
              CVar.Set.foldl (fn (k, acc) => handle_dK_ld (U.evalCVar (k, envK, storeK), acc)) (lds_list @ acc) fv_cv
      in lds_list end
      and handle_dK_ld (dK, acc) =
          case dK
           of ValueK.CLOK cloKs => CloK.Set.foldl handle_cloK_ld acc cloKs
            | _ => acc
      fun handle_kills_lv (xs, lvUCrit, dKs, search_lam_lab) =
          if List.null xs
          then (xs, lvUCrit)
          else let
              val bs_list = List.foldl handle_dK_b [] dKs
              fun handle_x (x, (xs', lvUCrit)) =
                  if List.all (fn bs => noBindingsFor (x, bs)) bs_list
                  then (x :: xs', lvUCrit)
                  else (xs', kill_lv (x, lvUCrit, kill_set_lv (x, search_lam_lab)))
              (*
              val _ = Verbose.say ["testing ", String.concatWithMap " " LVar.toString xs, " against ",
                                   String.concatWithMap " " (fn bs => String.concatWithMap " " Binding.toString (BS.listItems bs))
                                                        bs_list, "\n"]
                *)
              val (xs', lvUCrit') = List.foldl handle_x ([], lvUCrit) xs
          in (xs', lvUCrit') end
      fun handle_kills_ld (lds, ldUCrit, dKs, search_lam_lab) =
          if List.null lds
          then (lds, ldUCrit)
          else let
              val lds_list = List.foldl handle_dK_ld [] dKs
              fun handle_ld (ld, (lds', ldUCrit)) =
                  if List.all (fn lds => noLDataFor (ld, lds)) lds_list
                  then (ld :: lds', ldUCrit)
                  else (lds', kill_ld (ld, ldUCrit, kill_set_ld (ld, search_lam_lab)))
              val (lds', ldUCrit') = List.foldl handle_ld ([], ldUCrit) lds
          in (lds', ldUCrit') end
      fun handle_kills (xs, lds, lvUCrit, ldUCrit, dKs, search_lam_lab) = let
          val (xs, lvUCrit) = handle_kills_lv (xs, lvUCrit, dKs, search_lam_lab)
          val (lds, ldUCrit) = handle_kills_ld (lds, ldUCrit, dKs, search_lam_lab)
      in (xs, lds, lvUCrit, ldUCrit) end

      fun search_for (xs, lds, lvUCrit, ldUCrit, search_lam_lab, proxy, seen_aP) = let
          val (e, dKs, aP') = Proxy.get proxy
      in
          ((* Verbose.say ["    trying proxy: ", Proxy.toString proxy, " at ", Label.toString search_lam_lab, "\n"]; *)
           if Label.Set.member (AddrProxy.Map.lookup (aP_map, aP'), search_lam_lab)
              orelse Label.same (search_lam_lab, CU.labelOfExp e)
           then let
               (* val _ = Verbose.say ["    try good\n"] *)
               val seen_aP' = AddrProxy.Set.add (seen_aP, aP')
               val acc = handle_kills (xs, lds, lvUCrit, ldUCrit, dKs, search_lam_lab)
               fun handle_proxy (proxy', (xs', lds', lvUCrit, ldUCrit)) =
                   search_for (xs', lds', lvUCrit, ldUCrit, search_lam_lab, proxy', seen_aP')
               val acc = if not (AddrProxy.Set.member (seen_aP, aP'))
                         then ValueProxy.fold_proxy handle_proxy acc (StoreProxy.lookup (storeP, aP'))
                         else acc
           in acc end
           else (xs, lds, lvUCrit, ldUCrit))
      end

      fun lp (lam_lab, (xs, lds, lvUCrit, ldUCrit)) =
          if Label.same (lam_lab, PInfo.lam_lab0 pinfo)
             orelse (List.null xs andalso List.null lds)
          then (lvUCrit, ldUCrit)
          else let
              val lam_lab' = PInfo.icn_ld_lam pinfo lam_lab
              fun handle_proxy (proxy, (xs', lds', lvUCrit, ldUCrit)) =
                  search_for (xs', lds', lvUCrit, ldUCrit, lam_lab', proxy, AddrProxy.Set.empty)
              val (xs', lds', lvUCrit, ldUCrit) =
                  ValueProxy.fold_proxy handle_proxy (xs, lds, lvUCrit, ldUCrit) (StoreProxy.lookup (storeP, aP0))
          in lp (lam_lab', (xs', lds', lvUCrit, ldUCrit)) end

      (* val _ = Verbose.say ["search begin\n"] *)
      val xs = xs0
      val lds = lds0
      val initial = let
          val (xs, lvUCrit) =
              if List.null xs
              then (xs, lvUCrit)
              else let
                  val bs_list = live_b (SOME (fv_lv0, CVar.Set.empty, env0, EnvK.empty, aP0), addrs0, [])
                  val bs_list =
                      CVar.Set.foldl (fn (k, acc) => raise Fail "not fixed" (* handle_dK_b (U.evalCVar (k, envK0, storeK), acc) *)) bs_list fv_cv0
                  val bs_list = List.foldl (fn ((dK, _), acc) => raise Fail "not fixed" (* handle_dK_b (dK, acc) *)) bs_list aK_aPs0
                  fun handle_x (x, (xs', lvUCrit)) =
                      if List.all (fn bs => noBindingsFor (x, bs)) bs_list
                      then (x :: xs', lvUCrit)
                      else (xs', kill_lv (x, lvUCrit, kill_set_all (lam_lab, [])))
                  val (xs', lvUCrit') = List.foldl handle_x ([], lvUCrit) xs
              in (xs', lvUCrit') end
          val (lds, ldUCrit) =
              if List.null lds
              then (lds, ldUCrit)
              else let
                  val lds_list = live_ld (SOME (fv_lv0, CVar.Set.empty, env0, EnvK.empty, aP0), addrs0, [])
                  val lds_list =
                      CVar.Set.foldl (fn (k, acc) => handle_dK_ld (U.evalCVar (k, envK0, storeK), acc)) lds_list fv_cv0
                  val lds_list = List.foldl (fn ((dK, _), acc) => raise Fail "not fixed" (* handle_dK_ld (dK, acc) *)) lds_list aK_aPs0
                  fun handle_ld (ld, (lds', ldUCrit)) =
                      if List.all (fn lds => noLDataFor (ld, lds)) lds_list
                      then (ld :: lds', ldUCrit)
                      else (lds', kill_ld (ld, ldUCrit, kill_set_all (lam_lab, [])))
                  val (lds', ldUCrit') = List.foldl handle_ld ([], ldUCrit) lds
              in (lds', ldUCrit') end
      in (xs, lds, lvUCrit, ldUCrit) end
      val res = lp (lam_lab, initial)
      (* val _ = Verbose.say ["search end\n"] *)
  in res end

  val USE_SOPHISTICATED = false

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val utilAddrs = #utilAddrs analysis_space
      val sideEffectVars = #sideEffectVars utilAddrs
      val tyAddrs = #tyAddrs utilAddrs
      val pinfo = #pinfo analysis_space
      val liveMemo = #liveMemo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val ldata_passed_to_unknown = #ldata_passed_to_unknown state_space
      val live_b_base = Live.live_b liveMemo
      fun live_b (query : ((LVar.Set.set * CVar.Set.set * Env.t * EnvK.t * 
                    AddrProxy.t) option * Addr.t list * 
                   (AddrK.t * AddrProxy.t) list)) = doTimer timerLiveChecks live_b_base query
      val live_ld_base = Live.live_ld liveMemo
      fun live_ld (query : ((LVar.Set.set * CVar.Set.set * Env.t * EnvK.t * 
                    AddrProxy.t) option * Addr.t list * 
                   (AddrK.t * AddrProxy.t) list)) = doTimer timerLiveChecks live_ld_base query
      fun fv_exp_lv e = PInfo.fv_exp_lv pinfo (CU.labelOfExp e)
      fun fv_exp_cv e = PInfo.fv_exp_cv pinfo (CU.labelOfExp e)
      val fv_lam_lv = PInfo.fv_lam_lv pinfo
      val fv_lamK_lv = PInfo.fv_lamK_lv pinfo
      val fv_lamK_cv = PInfo.fv_lamK_cv pinfo
      val cn_lv_lam = PInfo.cn_lv_lam pinfo
      val cn_ld_lam = PInfo.cn_ld_lam pinfo
      val crit_birth_lv = AInfo.crit_birth_lv ainfo
      val crit_birth_ld = AInfo.crit_birth_ld ainfo
      (* val _ = Verbose.say ["aP_map begin\n"] *)
      (* val _ = Verbose.say ["aP_map end\n"] *)
      (*
      val _ = Verbose.say ["storeP: "]
      val _ = StoreProxy.appi (fn (aP, dP) =>
                                  Verbose.say [AddrProxy.toString aP, " -> ", ValueProxy.toString dP, "\n"])
                              storeP
      val _ = Verbose.say ["aP_map: "]
      val _ = AddrProxy.Map.appi (fn (aP, labs) =>
                                  Verbose.say [AddrProxy.toString aP, " -> ", String.concatWithMap " " Label.toString (LS.listItems labs), "\n"])
                              aP_map
      *)
      val aP_map = ref NONE
      fun compute_aP_map () = case ! aP_map of NONE => aP_map := SOME (precompute (pinfo, storeP)) | _ => ()
      fun kill_lv (x, lvUCrit) =
          LVM.insert (lvUCrit, x, LS.singleton (PInfo.immediate_alloc_loc_lv pinfo x))
      fun kill_ld (ld, ldUCrit) =
          LM.insert (ldUCrit, ld, LS.singleton (PInfo.immediate_alloc_loc_ld pinfo ld))

      fun chk_bs_list bs_list (x, lvUCrit) =
          if List.all (fn bs => noBindingsFor (x, bs)) bs_list
          then lvUCrit
          else kill_lv (x, lvUCrit)

      fun chk_lds_list lds_list (ld, ldUCrit) =
          if List.all (fn lds => noLDataFor (ld, lds)) lds_list
          then ldUCrit
          else kill_ld (ld, ldUCrit)

      fun chk (lam_lab, lvUCrit, ldUCrit, xs, lds, addrs : Addr.t list, addrKs : (AddrK.t * AddrProxy.t) list, fv_lv, fv_cv, env, envK, aP) =
          if USE_SOPHISTICATED
          then let
              val () = compute_aP_map ()
              val search = search (pinfo, crit_birth_lv, crit_birth_ld, live_b, live_ld, storeK, storeP, Option.valOf (! aP_map))
          in search (lam_lab, lvUCrit, ldUCrit, xs, lds, addrs, addrKs, fv_lv, fv_cv, env, envK, aP) end
          else let
              val lvUCrit = if List.null xs
                            then lvUCrit
                            else let
                                val bs_list = live_b (SOME (fv_lv, fv_cv, env, envK, aP), addrs, addrKs)
                            in List.foldl (chk_bs_list bs_list) lvUCrit xs end
              val ldUCrit = if List.null lds
                            then ldUCrit
                            else let
                                val lds_list = live_ld (SOME (fv_lv, fv_cv, env, envK, aP), addrs, addrKs)
                            in List.foldl (chk_lds_list lds_list) ldUCrit lds end
          in (lvUCrit, ldUCrit) end

      (* For all states, for all definitions of xR, there is no other globally live binding of xR *)
      fun chkConfig (xi, (lvUCrit, ldUCrit)) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
          val lam_lab = PInfo.exp_lam pinfo lab_e
      in case e
          of C.LETFUN(bindings, body) => let
              val xs = List.map (fn (f, _, _, _, _) => f) bindings
              val lds = List.map (fn (_, ld, _, _, _) => ld) bindings
              val fv_lv = fv_exp_lv exp
              val fv_cv = fv_exp_cv exp
          in chk (lam_lab, lvUCrit, ldUCrit, xs, lds, [], [], fv_lv, fv_cv, env, envK, aP) end
           | C.LETCONT(bindings, body) => (lvUCrit, ldUCrit)
           | C.IF _ => (lvUCrit, ldUCrit)
           | C.ATOM (arg, x, e') => let
               (* need to chk arg, as well as e', in these cases *)
               val d = U.evalAtom (lab_e, fn _ => (), arg, env, store)
               val a = (* case arg
                        of C.LIT (Literal.Int _, _) => #a_int tyAddrs
                         | C.LIT (Literal.Word _, _) => #a_word tyAddrs
                         | C.LIT (Literal.Real _, _) => #a_real tyAddrs
                         | C.LIT (Literal.Char _, _) => #a_char tyAddrs
                         | C.LIT (Literal.String _, _) => #a_string tyAddrs
                         | C.UNIT => #a_unit tyAddrs
                         | _ => *) U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end

           (* in the below, we need to just check e' \ x and the result of the primop *)
           | C.PURE (oper, args, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
           | C.ARITH (oper, args, x, e', e_exn) => let
               (* do not need to check e_exn because x is only bound in e' *)
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
           | C.GET (oper, args, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
           | C.SET (oper, args, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end

           | C.TUPLE(args, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
           | C.SELECT (offset, arg, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end

           | C.DCAPPLY (dcon, tys, arg, x, e') => let
               val a = U.alloc (x, tenv, aP)
               val fv_lv = LVS.subtract (fv_exp_lv e', x)
               val fv_cv = fv_exp_cv e'
           in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
           | C.SWITCH(arg, pats) => let
               val a = Env.lookup (env, arg)
               val d = Store.lookup (store, a)
               fun chk_pat ((C.VPAT x, exp'), (lvUCrit, ldUCrit)) =  let
                   val fv_lv = LVS.subtract(fv_exp_lv exp', x)
                   val fv_cv = fv_exp_cv exp'
               in chk (lam_lab, lvUCrit, ldUCrit, [x], [], [a], [], fv_lv, fv_cv, env, envK, aP) end
                 | chk_pat ((C.DCPAT(dcon, _, SOME x), exp'), (lvUCrit, ldUCrit)) = let
                     val a_get = Value.match_dcon (fn (a, acc) => a :: acc) [] (dcon, d)
                     val fv_lv = LVS.subtract(fv_exp_lv exp', x)
                     val fv_cv = fv_exp_cv exp'
                 in chk (lam_lab, lvUCrit, ldUCrit, [x], [], a_get, [], fv_lv, fv_cv, env, envK, aP) end
                 | chk_pat (_, (lvUCrit, ldUCrit)) = (lvUCrit, ldUCrit)
           in List.foldl chk_pat (lvUCrit, ldUCrit) pats end

           | C.APPLY (f, tys, args, argKs) => let
               val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
               val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
               val d_f = U.evalLVar (f, env, store)
               val a_arg = List.map (fn arg => Env.lookup (env, arg)) args
               val a_argK = List.map (fn argK => (EnvK.lookup (envK, argK), aP)) argKs
               fun handle_clo (clo, (lvUCrit, ldUCrit)) = let
                   val ((_, lam_lab, xs, ks, _), env_clo, tenv_clo) = Clo.get clo
                   val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                   val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
               in
                   case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                    of NONE => (lvUCrit, ldUCrit)
                     | SOME tenv' => let
                      val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                      val fv_lv = fv_lam_lv lam_lab
                     in chk (lam_lab, lvUCrit, ldUCrit, xs, [], a_arg, a_argK, fv_lv, CVar.Set.empty, env_clo, EnvK.empty, aP') end
               end
           in Value.fold_clos handle_clo (lvUCrit, ldUCrit) d_f end
           | C.THROW(k, args) => let
               val k_cty = U.instantiateCTy (tenv, CVar.typeOf k)
               val a_arg = List.map (fn arg => Env.lookup (env, arg)) args
               val dK = U.evalCVar (k, envK, storeK)
               val (cloK_aPs, any_unknown) = U.cloKOf (fn _ => (), dK, aP, storeP)
               fun handle_cloK_aP ((cloK, aP'), (lvUCrit, ldUCrit)) = let
                   val (lamK as (_, lab, xs, body), env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
                   val fv_lv = fv_lamK_lv lab
                   val fv_cv = fv_lamK_cv lab
                   val lam_lab' = PInfo.exp_lam pinfo (CU.labelOfExp body)
                   val cloK_ty = CPSTypes.ContTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs)
                   val cloK_ty = U.instantiateCTy (tenv_cloK, cloK_ty)
               in
                   case U.unifyCont (tenv_cloK, k_cty, cloK_ty)
                    of NONE => (lvUCrit, ldUCrit)
                     | SOME _ => 
                       chk (lam_lab', lvUCrit, ldUCrit, xs, [], a_arg, [], fv_lv, fv_cv, env_cloK, envK_cloK, aP')
               end
               val (lvUCrit, ldUCrit) = List.foldl handle_cloK_aP (lvUCrit, ldUCrit) cloK_aPs
           in (lvUCrit, ldUCrit) end
      end

      (* remove every allocation contained in the lam from
         the lam as well as all frames contained in the lam *)
      fun killLam (lam_lab, lvUCrit, ldUCrit) = let
          val cn_lv = PInfo.cn_lam_lv pinfo lam_lab
          val cn_ld = PInfo.cn_lam_ld pinfo lam_lab
          val to_remove = PInfo.cn_ld_lam pinfo lam_lab
          val lvUCrit = LVS.foldl kill_lv lvUCrit cn_lv
          val ldUCrit = LS.foldl kill_ld ldUCrit cn_ld
      in (lvUCrit, ldUCrit) end

      (* any ldata which is passed to the unknown and any variable
         that is passed to the unknown (i.e. is closed over in a closure)
         cannot be given any uniqueness except for H.
         Additionally, for any closures passed to the unknown, any
         bindings or values allocated in those closures cannot be
         allocated on any frames that contain the closure. *)
      fun handlePassedToUnknown uniquenessCrits = let
          fun handleLD (ld, (lvUCrit, ldUCrit)) = let
              val ldUCrit = kill_ld (ld, ldUCrit)
              val lvUCrit =
                  if PInfo.ld_is_lam pinfo ld
                  then LVS.foldl kill_lv lvUCrit (fv_lam_lv ld)
                  else lvUCrit
              val (lvUCrit, ldUCrit) =
                  if PInfo.ld_is_lam pinfo ld
                  then killLam (ld, lvUCrit, ldUCrit)
                  else (lvUCrit, ldUCrit)
          in (lvUCrit, ldUCrit) end
      in LS.foldl handleLD uniquenessCrits ldata_passed_to_unknown end

      (* For now, we don't know anything about any binding/closure reachable via a ref/array *)
      fun handleSideEffects UCrit = 
          UCrit
      (* TODO: write a separate function to go over the configs and
         grab the created ref addrs, or track them during generation *)
      (*
      fun handleSideEffects UCrit = let
          fun handleSideEffect (_, a, (lvUCrit, ldUCrit)) =
              case Store.find (store, a)
               of NONE => (lvUCrit, ldUCrit)
                | SOME _ => let
                    val bs_list = live_b (NONE, [a], [])
                    val lds_list = live_ld (NONE, [a], [])
                    val lvUCrit =
                        List.foldl (fn (bs, lvUCrit) =>
                                       Binding.Set.foldl
                                           (fn ((x, a), lvUCrit) =>
                                               kill_lv (x, lvUCrit))
                                           lvUCrit bs)
                                   lvUCrit bs_list
                    val ldUCrit =
                        List.foldl (fn (lds, ldUCrit) =>
                                       LS.foldl kill_ld ldUCrit lds)
                                   ldUCrit lds_list
                in (lvUCrit, ldUCrit) end
      in LM.foldli handleSideEffect UCrit sideEffectVars end
      *)

      (* For all states, for all definitions of xR, there is no other globally live binding of xR *)
      fun isUnique (lvUCrit, ldUCrit) = let
          val (lvUCrit, ldUCrit) = Config.Set.foldl chkConfig (lvUCrit, ldUCrit) configs
          val (lvUCrit, ldUCrit) = handlePassedToUnknown (lvUCrit, ldUCrit)
          val (lvUCrit, ldUCrit) = handleSideEffects (lvUCrit, ldUCrit)
      in (lvUCrit, ldUCrit) end

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

      val lvUCrit = initial_crit_lv pinfo
      val ldUCrit = initial_crit_ld pinfo
      (*
      fun init (insert, containing_lams) (x, acc) = insert (acc, x, containing_lams x)
      val lvUCrit = List.foldl (init (LVM.insert, cn_lv_lam)) LVM.empty (PInfo.lvars pinfo)
      val ldUCrit = List.foldl (init (LM.insert, cn_ld_lam)) LM.empty (PInfo.ldata pinfo)
      *)
      val (lvUCrit, ldUCrit) = isUnique (lvUCrit, ldUCrit)
      fun assert_lv (x) =
          if LS.member (LVM.lookup (lvUCrit, x), PInfo.immediate_alloc_loc_lv pinfo x)
          then ()
          else raise Fail "bad u crit lv"
      val _ = List.app assert_lv (PInfo.lvars pinfo)
      fun assert_ld (ld) =
          if LS.member (LM.lookup (ldUCrit, ld), PInfo.immediate_alloc_loc_ld pinfo ld)
          then ()
          else raise Fail "bad u crit ld"
      val _ = List.app assert_ld (PInfo.ldata pinfo)

      in AInfo.with_ldataUniquenessCrit (AInfo.with_lvarUniquenessCrit (ainfo, lvUCrit), ldUCrit) end

end (* DetermineUniquenessCriteria *)
