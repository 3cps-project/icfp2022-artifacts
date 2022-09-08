(* continuation-order.sml
 *
 * Determines an ordering between pop continuation variables.
 * k <= k' means that k' always will pop at least the frames that k does.
 *)

structure DetermineContinuationOrder : DETERMINE_INFO =
struct

  structure C = CPS
  structure U = TransitionUtil
  structure LS = Label.Set
  structure CVS = CVar.Set
  structure CVM = CVar.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  (* given a list of variables in a proxy-address context, returns all
     of the pairs (k, k') where k <= k', i.e. k (always) points to a
     continuation closure that is at least far from the top of the
     stack than k' is. That is, popping to k pops less than or the
     same as popping to k' *)
  (* Does not return reflexive pairs (k, k) *)
  fun find_orders (pinfo, storeP, ks0, aP0) = let
      fun same_pair_as (k, k') (k'', k''') =
          CVar.same (k, k'') andalso CVar.same (k', k''')
      fun unify (pairs1, pairs2) =
          List.filter (fn pair => List.exists (same_pair_as pair) pairs2) pairs1
      fun all ks =
          List.foldl (fn (k, acc) => List.foldl (fn (k', acc) => (k, k') :: acc) acc ks) [] ks
      fun search (ks, inds : int list, aP : AddrProxy.t, seen) =
          if List.length ks = 1
          then [(hd ks, hd ks)]
          else if List.length ks = 0
          then []
          else if U.AP_Indices.Set.member (seen, (aP, inds))
          then all ks (* TODO: I think this is correct *)
          else let
              val dP = StoreProxy.lookup (storeP, aP)
          in if false (* ValueProxy.isUnknown dP *)
             then [] (* if the cont vars point into the unknown, then no ordering about then can be determined *)
             else let
                 fun handle_proxy (proxy, acc) = let
                     val (_, valKs, aP') = Proxy.get proxy
                     val valKs = U.select (inds, valKs)
                     fun handle_k_valK (k, valK, (ks_stop, cloKs_stop, ks', inds')) =
                         if U.valueK_isCloK valK
                         then (k :: ks_stop, U.valueK_cloKOf valK :: cloKs_stop, ks', inds')
                         else (ks_stop, cloKs_stop, k :: ks', (U.valueK_indexOf valK) :: inds')
                     val (ks_stop, cloKs_stop, ks', inds') =
                         ListPair.foldl handle_k_valK ([], [], [], []) (ks, valKs)
                     (* every variable that has stopped is <= every other
                        variable that is being searched for at the moment *)
                     fun handle_k_cloK (k, cloKs, acc) = let
                         val acc = List.foldl (fn (k', acc) => (k, k') :: acc) acc ks'
                         val cloK = CloK.Set.minItem cloKs
                         val (lamK as (_, lab, _, _), _, _, _) = CloK.get cloK
                         fun handle_k_cloK' (k', cloKs', acc) = let
                             (* right now, there should be exactly one single cont closure in the set(s).
                                however, it shouldn't matter in general if there are more, as they all
                                should have the same label. *)
                             val cloK' = CloK.Set.minItem cloKs'
                             val (lamK' as (_, lab', _, _), _, _, _) = CloK.get cloK'
                         in
                             (* if lamK is known to be <= lamK' *)
                             if LS.member (PInfo.leq_lamKs pinfo lab, lab')
                             then (k, k') :: acc
                             else acc
                         end
                         val acc = ListPair.foldl handle_k_cloK' acc (ks_stop, cloKs_stop)
                     in acc end
                     val base = ListPair.foldl handle_k_cloK [] (ks_stop, cloKs_stop)
                     val seen' = U.AP_Indices.Set.add (seen, (aP', inds'))
                     val rec_res = search (ks', inds', aP', seen')
                 in unify (acc, base @ rec_res) end
             in ValueProxy.fold_proxy handle_proxy (all ks) dP end
          end
      val inds0 = List.tabulate (List.length ks0, fn x => x)
      val res = search (ks0, inds0, aP0, U.AP_Indices.Set.empty)
  in res end

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val ldata_passed_to_unknown = #ldata_passed_to_unknown state_space
      fun unify (set1, set2) =
          CVS.intersection (set1, set2)
      fun handle_config (xi, contOrder) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.APPLY (f, tys, args, argKs) => let
               val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
               val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
               val d_f = U.evalLVar(f, env, store)
               fun handle_clo (clo, contOrder) = let
                   val (lam as (_, lam_lab, xs, ks, body), _, tenv_clo) = Clo.get clo
                   val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                   val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
               in
                   case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                    of NONE => contOrder
                     | SOME tenv' => let
                         val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                         val res = find_orders (pinfo, storeP, ks, aP')
                         fun handle_k (k, contOrder) = let
                             fun handle_pair ((k', k''), acc) =
                                 if CVar.same (k, k') then CVS.add (acc, k'') else acc
                             val prev = CVM.lookup (contOrder, k)
                             val next = CVS.add (List.foldl handle_pair CVS.empty res, k)
                             val contOrder = CVM.insert (contOrder, k, unify (prev, next))
                         in contOrder end
                         val contOrder = List.foldl handle_k contOrder ks
                     in contOrder end
               end
               val contOrder = Value.fold_clos handle_clo contOrder d_f
               in contOrder end
            | C.LETCONT (bindingKs, _) => let
                val ks = List.foldl (fn ((k, _, _, _), acc) => k :: acc) [] bindingKs
                fun handle_k (k, contOrder) =
                    CVM.insert (contOrder, k, PInfo.possible_leq_ks pinfo k)
                val contOrder = List.foldl handle_k contOrder ks
            in contOrder end
            | _ => contOrder
      end
      fun handle_ldata_passed_to_unknown (ld, contOrder) =
          if PInfo.ld_is_lam pinfo ld
          then let
              val lam as (_, _, _, ks, _) = PInfo.lam pinfo ld
              val contOrder = List.foldl (fn (k, contOrder) =>
                                             CVM.insert (contOrder, k, CVS.singleton k))
                                         contOrder ks
          in contOrder end
          else contOrder
      val contOrder0 = List.foldl (fn (k, acc) => CVM.insert (acc, k, PInfo.possible_leq_ks pinfo k))
                                  CVM.empty (PInfo.cvars pinfo)
      val contOrder = Config.Set.foldl handle_config contOrder0 configs
      val contOrder = LS.foldl handle_ldata_passed_to_unknown
                               contOrder (LS.add (ldata_passed_to_unknown, PInfo.lam_lab0 pinfo))
      val ainfo = AInfo.with_continuationOrder (ainfo, contOrder)
      in ainfo end

end
