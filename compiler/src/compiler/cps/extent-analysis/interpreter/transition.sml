(* transition.sml
 *
 * Transitions a concrete state.
 *)

structure CTransition : sig

  datatype transResult = TRANS of CTransitionUtil.state | HALT of CValue.t list

  val initialState : CPSInformation.t -> CPS.comp_unit -> CTransitionUtil.mutable_state * CTransitionUtil.state

  val transAndObtain : CPSInformation.t -> CTransitionUtil.mutable_state -> (CTransitionUtil.state * AnalysisInformation.t) -> transResult * AnalysisInformation.t

end = struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure LS = Label.Set

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation
  structure U = CTransitionUtil
  structure Update = UpdateInterpreterInformation

  structure A = CAddr
  structure AK = CAddrK
  structure AT = A.Tbl
  structure VB = CValueBase
  structure V = CValue
  structure VKB = CValueKBase
  structure VK = CValueK

  datatype transResult = TRANS of CTransitionUtil.state | HALT of V.t list

  (* Obtains the initial interpreter state for the program *)
  fun initialState pinfo (C.CU(f, lab0, xs, ks, e0)) : U.mutable_state * U.state = let
      val curr_frm_id = ref CId.initial
      fun frm_alloc lab = let
            val res = Frame.make (lab, ! curr_frm_id)
            in
              curr_frm_id := CId.succ (! curr_frm_id); res
            end
      val frm0 = frm_alloc (lab0)

      val a_id = ref CId.initial
      val aK_id = ref CId.initial
      val d_id = ref CId.initial
      val dK_id = ref CId.initial
      fun a_alloc () = let
          val id = ! a_id
          val a = A.alloc id
          in a_id := CId.succ (! a_id); a end
      fun aK_alloc () = let
          val id = ! aK_id
          val aK = AK.alloc id
          in aK_id := CId.succ (! aK_id); aK end
      fun d_alloc (base, frms) = let
          val id = ! d_id
          val d = V.make (id, base, frms)
          in d_id := CId.succ (! d_id); d end
      fun dK_alloc (base, frms) = let
          val id = ! dK_id
          val dK = VK.make (id, base, frms)
          in dK_id := CId.succ (! dK_id); dK end
      val env0 = CEnv.empty
      val envK0 = CEnvK.empty
      val store0 = CStore.makeEmpty()
      val storeK0 = CStoreK.makeEmpty ()
      val triples0 = List.map (fn x => (x, a_alloc (), d_alloc (VB.UNIT, Frame.Set.empty))) xs
      fun handle_triple ((x, a, d), (env, store)) = U.extendMaps (x, a, d, env, store)
      val (env0, store0) = List.foldl handle_triple (env0, store0) triples0
      val triplesK0 = List.map (fn k => (k, aK_alloc (), VK.halt)) ks
      fun handle_tripleK ((k, aK, dK), (envK, storeK)) = U.extendMapsK (k, aK, dK, envK, storeK)
      val (envK0, storeK0) = List.foldl handle_tripleK (envK0, storeK0) triplesK0
      val lexFrms0 = [frm0]
      val stack0 = [frm0]
      val bindings0 = List.foldl (fn ((x, a, _), acc) => (x, a) :: acc) [] triples0
      val frm_bindingAlloc = Frame.Tbl.mkTable (10000, Fail "frm_bindingAlloc")
      val () = Frame.Tbl.insert frm_bindingAlloc (frm0, bindings0)
      val frm_ldataAlloc = Frame.Tbl.mkTable (10000, Fail "frm_ldataAlloc")
      val () = Frame.Tbl.insert frm_ldataAlloc (frm0, [])
      val frm_live = Frame.Tbl.mkTable (10000, Fail "frm_live")
      val () = Frame.Tbl.insert frm_live (frm0, true)
      val memo = CLive.make (pinfo, store0, storeK0)
      val lvarsBound = ref (LVS.fromList xs)
      val expsSeen = ref LS.empty
      val count_lvar_alloc = LVar.Tbl.mkTable (10000, Fail "count_lvar_alloc")
      val () = List.app (fn x => LVar.Tbl.insert count_lvar_alloc (x, 0)) (PInfo.lvars pinfo)
      val count_lam_alloc = Label.Tbl.mkTable (10000, Fail "count_lam_alloc")
      val () = List.app (fn lam => Label.Tbl.insert count_lam_alloc (lam, 0)) (PInfo.lams pinfo)
      val mutable_state0 : U.mutable_state = {
              count_lvar_alloc=count_lvar_alloc,
              count_lam_alloc=count_lam_alloc,
              frm_alloc=frm_alloc,
              a_alloc=a_alloc,
              aK_alloc=aK_alloc,
              d_alloc=d_alloc,
              dK_alloc=dK_alloc,
              memo=memo,
              frm_bindingAlloc=frm_bindingAlloc,
              frm_ldataAlloc=frm_ldataAlloc,
              frm_live=frm_live,
              expsSeen=expsSeen,
              lvarsBound=lvarsBound
            }
      val state0 = (e0, env0, store0, envK0, storeK0, lexFrms0, stack0)
      in (mutable_state0, state0) end

  fun transAndObtain pinfo (mutable_state) (state, iinfo) = let
      val (exp as C.EXP (lab_e,e), env, store, envK, storeK, lexFrms, stack) = state
      val memo = #memo mutable_state
      val frm_bindingAlloc = #frm_bindingAlloc mutable_state
      val frm_ldataAlloc = #frm_ldataAlloc mutable_state
      val frm_live = #frm_live mutable_state
      val frm_alloc = #frm_alloc mutable_state
      val a_alloc = #a_alloc mutable_state
      val aK_alloc = #aK_alloc mutable_state
      val d_alloc = #d_alloc mutable_state
      val dK_alloc = #dK_alloc mutable_state
      val expsSeen = #expsSeen mutable_state
      val () = expsSeen := LS.add (!expsSeen, lab_e)
      val lvarsBound = #lvarsBound mutable_state
      fun addLVarsBound (lvs) = lvarsBound := LVS.addList (! lvarsBound, lvs)
      fun fv_exp_lv e = PInfo.fv_exp_lv pinfo (CU.labelOfExp e)
      fun fv_exp_cv e = PInfo.fv_exp_cv pinfo (CU.labelOfExp e)
      val evalAtom = U.evalAtom mutable_state
      val glb = CLive.glb memo
      val gld = CLive.gld memo
      fun push_new_frm (lab, lexFrms, stack) = let
            val frm' = frm_alloc (lab)
            val () = Frame.Tbl.insert frm_live (frm', true)
            val () = Frame.Tbl.insert frm_bindingAlloc (frm', [])
            val () = Frame.Tbl.insert frm_ldataAlloc (frm', [])
            in (frm' :: lexFrms, frm' :: stack) end
      val (lexFrms, stack) =
          if (PInfo.is_alloc_loc pinfo lab_e)
          then push_new_frm (lab_e, lexFrms, stack)
          else (lexFrms, stack)
      in
        case e
         of C.LETFUN (bindings, body) => let
             (* allocate the addresses which will be needed *)
             val triples = List.map (fn lam => (#1 lam, a_alloc (), lam)) bindings
             val glbs = glb (SOME (fv_exp_lv exp, fv_exp_cv exp, env, envK), NONE, NONE)
             val glds = gld (SOME (fv_exp_lv exp, fv_exp_cv exp, env, envK), NONE, NONE)
             val iinfo = Update.update_lvarUniquenessCrit (
                    List.map #1 triples,
                    glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
             val iinfo = Update.update_ldataUniquenessCrit (
(* FIXME: fuse maps *)
                    List.map #2 (List.map #3 triples),
                    glds, lexFrms, frm_ldataAlloc, frm_live, iinfo)
             val env' = List.foldl (fn ((x, a, lam), env) => CEnv.extend (env, x, a)) env triples
             val triples = List.map (fn (x, a, lam) => (x, a, d_alloc (VB.CLO (lam, env', lexFrms), Frame.Set.fromList lexFrms))) triples
             val store' = List.foldl (fn ((x, a, d), store) => CStore.extend(store, a, d)) store triples
             val () = CLive.add_a (memo, store', List.map #2 triples)
             val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, List.map (fn (x, a, _) => (x, a)) triples)
             val () = U.update_frm_ldataAlloc (frm_ldataAlloc, lexFrms, List.map #3 triples)
             val () = addLVarsBound (List.map #1 bindings)
             val () = List.app (fn lam => U.incr_lvar_count (mutable_state, #1 lam)) bindings
             val () = List.app (fn lam => U.incr_lam_count (mutable_state, #2 lam)) bindings
             in (TRANS (body, env', store', envK, storeK, lexFrms, stack), iinfo) end
          | C.LETCONT (bindings, body) => let
             (* allocate the addresses which will be needed *)
             val triplesK = List.map
                    (fn lamK => (#1 lamK, aK_alloc (), lamK))
                      bindings
             val envK' = List.foldl
                    (fn ((k, aK, lamK), envK) => CEnvK.extend (envK, k, aK))
                      envK triplesK
             val triplesK = List.map
                    (fn (k, aK, lamK) => (k, aK, dK_alloc (VKB.CLOK (lamK, env, envK', lexFrms), Frame.Set.fromList lexFrms)))
                      triplesK
             val storeK' = List.foldl
                    (fn ((k, aK, dK), storeK) => CStoreK.extend(storeK, aK, dK))
                      storeK triplesK
             val () = CLive.add_aK (memo, storeK', List.map #2 triplesK)
             in (TRANS (body, env, store, envK', storeK', lexFrms, stack), iinfo) end
          | C.IF (oper, args, thn, els) =>
            if U.evalTestPrim (oper, List.map (fn arg => U.evalLVar (arg, env, store)) args, store)
            then (TRANS (thn, env, store, envK, storeK, lexFrms, stack), iinfo)
            else (TRANS (els, env, store, envK, storeK, lexFrms, stack), iinfo)
          | C.ATOM (arg, x, e') => let
              val d_arg = evalAtom (lab_e, arg, env, store, lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_arg, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_arg], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              val iinfo = Update.update_lvarEnvMatch (x, d_arg, lexFrms, iinfo)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end

          | C.PURE (oper, args, x, e') => let
              val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              val (d_res, store') = U.evalPurePrim mutable_state (oper, d_args, store, lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_res, env, store')
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_res], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
          | C.ARITH (oper, args, x, e', e_exn) => (let
              val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              val d_res = U.evalArithPrim mutable_state (oper, d_args, lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_res, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_res], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
          (* If we see a fail exception, that was due to a failure to handle a primop.
             Otherwise, the primop application had an exception and we should transition
             to the exception expression. *)
                handle Fail x => raise Fail x
                     | _ => (TRANS (e_exn, env, store, envK, storeK, lexFrms, stack), iinfo))
          | C.GET (oper, args, x, e') => let
              val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              val d_res = U.evalGetPrim mutable_state (oper, d_args, store)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_res, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_res], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              val iinfo = Update.update_lvarEnvMatch (x, d_res, lexFrms, iinfo)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
          | C.SET (oper, args, x, e') => let
              val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              val (d_res, store') = U.evalSetPrim mutable_state (oper, d_args, store, lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_res, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_res], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end

          | C.TUPLE (args, x, e') => let
              val d_tup = d_alloc (VB.TUPLE (lab_e, List.map (fn arg => CEnv.lookup (env, arg)) args), Frame.Set.fromList lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_tup, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_tup], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
              in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
          | C.SELECT (offset, arg, x, e') => let
              val d_arg = U.evalLVar (arg, env, store)
              val iinfo = Update.update_tupleInfo (lab_e, d_arg, iinfo)
              in
                case V.base d_arg
                 of VB.TUPLE (lab_tup, addrs) => if offset <= (List.length addrs)
                      then let
                        val d_sel = CStore.lookup (store, List.nth(addrs, offset-1))
                        val a_x = a_alloc ()
                        val (env', store') = U.extendMaps (x, a_x, d_sel, env, store)
                        val () = CLive.add_a (memo, store', [a_x])
                        val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_sel], NONE)
                        val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
                        val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
                        val () = addLVarsBound [x]
                        val () = U.incr_lvar_count (mutable_state, x)
                        val iinfo = Update.update_lvarEnvMatch (x, d_sel, lexFrms, iinfo)
                        in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
                      else raise Fail(concat[
                          "bad value: SELECT not given TUPLE of long enough length: ",
                          Int.toString offset, " ", VB.toString (VB.TUPLE (lab_tup, addrs))
                        ])
                  | _ => raise Fail("bad value: SELECT not given TUPLE: " ^ VB.toString (V.base d_arg))
                (* end case *)
              end

          | C.DCAPPLY (dcon, tys, arg, x, e') => let
              val d_dv = d_alloc (VB.DATA (lab_e, dcon, SOME (CEnv.lookup (env, arg))), Frame.Set.fromList lexFrms)
              val a_x = a_alloc ()
              val (env', store') = U.extendMaps (x, a_x, d_dv, env, store)
              val () = CLive.add_a (memo, store', [a_x])
              val glbs = glb (SOME (LVS.subtract(fv_exp_lv e', x), fv_exp_cv e', env, envK), SOME [d_dv], NONE)
              val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
              val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
              val () = addLVarsBound [x]
              val () = U.incr_lvar_count (mutable_state, x)
          in (TRANS (e', env', store', envK, storeK, lexFrms, stack), iinfo) end
          | C.SWITCH (arg, pats) => let
              val d = U.evalLVar (arg, env, store)
              val iinfo = Update.update_dataInfo (lab_e, d, iinfo)
              (* val _ = if (Label.toString lab_e) = (*"L05DE"*) "L05FC" then CheckAnalysisResults.say [CValue.toString d, "switch", "\n"] else () *)
              fun handle_pats pats =
                  (case pats
                    of [] => raise Fail "no pattern"
                     | (pat,body)::rst =>
                       (case (pat, V.base d)
                         of (C.VPAT x, _) => let
                             val a_x = a_alloc ()
                             val (env', store') = U.extendMaps (x, a_x, d, env, store)
                             val () = CLive.add_a (memo, store', [a_x])
                             val glbs = glb (SOME (LVS.subtract(fv_exp_lv body, x), fv_exp_cv body, env, envK), SOME [d], NONE)
                             val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
                             val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
                             val () = addLVarsBound [x]
                             val () = U.incr_lvar_count (mutable_state, x)
                             val iinfo = Update.update_lvarEnvMatch (x, d, lexFrms, iinfo)
                         in (TRANS (body, env', store', envK, storeK, lexFrms, stack), iinfo) end
                          | (C.DCPAT (dcon', _, xo), VB.DATA (_, dcon, ao)) =>
                            (case (CPSDataCon.compare(dcon, dcon'), ao, xo)
                              of (EQUAL, SOME a, SOME x) => let
                                  val d_inner = CStore.lookup (store, a)
                                  val a_x = a_alloc ()
                                  val (env', store') = U.extendMaps (x, a_x, d_inner, env, store)
                                  val () = CLive.add_a (memo, store', [a_x])
                                  val glbs = glb (SOME (LVS.subtract(fv_exp_lv body, x), fv_exp_cv body, env, envK), SOME [d_inner], NONE)
                                  val iinfo = Update.update_lvarUniquenessCrit ([x], glbs, lexFrms, frm_bindingAlloc, frm_live, iinfo)
                                  val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, [(x, a_x)])
                                  val () = addLVarsBound [x]
                                  val () = U.incr_lvar_count (mutable_state, x)
                                  val iinfo = Update.update_lvarEnvMatch (x, d_inner, lexFrms, iinfo)
                              in (TRANS (body, env', store', envK, storeK, lexFrms, stack), iinfo) end
                               | (EQUAL, NONE, NONE) => (TRANS (body, env, store, envK, storeK, lexFrms, stack), iinfo)
                               | _ => handle_pats rst)
                          | (C.LPAT (lit, _), base) =>
                            if (VB.compare (U.literalToValueBase lit, base)) = EQUAL
                            then (TRANS (body, env, store, envK, storeK, lexFrms, stack), iinfo)
                            else handle_pats rst
                          | _ => raise Fail ("bad pattern: got " ^ (V.toString d) ^ " at " ^ (Label.toString lab_e))))
          in handle_pats pats end

          | C.APPLY (f, tys, args, argKs) => let
              val args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              (* val _ = if (Label.toString lab_e) = "L05CB" then CheckAnalysisResults.say ((List.map CValue.toString args) @ ["call", "\n"]) else () *)
              val argKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
              val d_f = U.evalLVar (f, env, store)
              val iinfo = Update.update_funInfo (lab_e, d_f, iinfo)
              val call_lab = lab_e
              in
                case V.base d_f
                 of VB.CLO (clo as (lam, env_lam, lexFrms_clo)) => let
                      val (_, lab, xs, ks, body) = lam
                      (* val _ = Verbose.say ["Calling ", Label.toString lab, " with ", String.concatWithMap " " V.toString args, "\n"] *)
                      val iinfo = Update.update_display_clo pinfo (call_lab, lexFrms, lexFrms_clo, iinfo)
                      val iinfo = AInfo.with_callWebs (iinfo, CallWebs.add (AInfo.callWebs iinfo, {call=call_lab, lambda=lab}))
                      val () = addLVarsBound xs

                      val argKs_frms = List.foldl (fn (argK, acc) => CValueK.frms_lex argK @ acc) [] argKs
                      val (frms_popped, stack_popped) = U.popFrms (argKs_frms, stack)
                      val () = List.app (fn frm => Frame.Tbl.insert frm_live (frm, false)) frms_popped
                      (*
                      val () = Verbose.say ["popping: ", String.concatWithMap " " Frame.toString frms_popped, "\n"]
                      val () = List.app (fn frm =>
                                           Verbose.say ["bindings: ",
                                                        String.concatWithMap " " CBinding.toString
                                                                             (Frame.Tbl.lookup frm_bindingAlloc frm), "\n"]) frms_popped
                      *)
                      val glbs = glb (NONE, SOME (d_f :: args), SOME argKs)
                      val glds = gld (NONE, SOME (d_f :: args), SOME argKs)
                      val iinfo = Update.update_crit_death_lv (glbs, frms_popped, frm_bindingAlloc, iinfo)
                      val iinfo = Update.update_crit_death_ld (glds, frms_popped, frm_ldataAlloc, iinfo)
                      val iinfo = Update.update_relativePop (call_lab, frms_popped, iinfo)
                      val (lexFrms', stack') = push_new_frm (lab, lexFrms_clo, stack_popped)
                      val triples = ListPair.map (fn (x, arg) => (x, a_alloc (), arg)) (xs, args)
                      val (env', store') = List.foldl (fn ((x, a, arg), (env, store)) => U.extendMaps (x, a, arg, env, store)) (env_lam, store) triples
                      val () = CLive.add_a (memo, store', List.map #2 triples)
                      val triplesK = ListPair.map (fn (k, argK) => (k, aK_alloc (), argK)) (ks, argKs)
                      val (envK', storeK') = List.foldl (fn ((k, aK, argK), (envK, storeK)) => U.extendMapsK (k, aK, argK, envK, storeK)) (CEnvK.empty, storeK) triplesK
                      val () = CLive.add_aK (memo, storeK', List.map #2 triplesK)
                      val glbs = glb (NONE, SOME (d_f::args), SOME argKs)
                      val iinfo = Update.update_lvarUniquenessCrit (xs, glbs, lexFrms', frm_bindingAlloc, frm_live, iinfo)
                      val iinfo = Update.update_continuationOrder pinfo (ks, envK', storeK', stack, iinfo)
                      val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms', List.map (fn (x, a, _) => (x, a)) triples)
                      val () = List.app (fn x => U.incr_lvar_count (mutable_state, x)) xs
                      val iinfo = ListPair.foldl (fn (x, d, iinfo) => Update.update_lvarEnvMatch (x, d, lexFrms, iinfo)) iinfo (xs, args)
                      val iinfo = ListPair.foldl (fn (k, dK, iinfo) => Update.update_cvarEnvMatch (k, dK, lexFrms, iinfo)) iinfo (ks, argKs)
                      in (TRANS (body, env', store', envK', storeK', lexFrms', stack'), iinfo) end
                  | _ => raise Fail ("bad value: APPLY: " ^ (VB.toString (V.base d_f)))
                (* end case *)
              end
          | C.THROW (k, args) => let
              val args = List.map (fn arg => U.evalLVar (arg, env, store)) args
              (* val _ = if (Label.toString lab_e) = "L05C0" then CheckAnalysisResults.say ((List.map CValue.toString args) @ [" throw \n"]) else () *)
              val cont = U.evalCVar (k, envK, storeK)
              val iinfo = Update.update_funKInfo (lab_e, cont, iinfo)
              val lexFrms_caller = lexFrms
              val throw_lab = lab_e
              val glbs = glb (NONE, SOME args, SOME [cont])
              val glds = gld (NONE, SOME args, SOME [cont])
              val (frms_popped, stack_popped) = U.popFrms (CValueK.frms_lex cont, stack)
              (* val () = Verbose.say ["popping: ", String.concatWithMap " " Frame.toString frms_popped, "\n"] *)
              (* val () = List.app (fn frm => Verbose.say ["bindings: ", String.concatWithMap " " CBinding.toString (Frame.Tbl.lookup frm_bindingAlloc frm), "\n"]) frms_popped *)
              val () = List.app (fn frm => Frame.Tbl.insert frm_live (frm, false)) frms_popped
              val iinfo = Update.update_crit_death_lv (glbs, frms_popped, frm_bindingAlloc, iinfo)
              val iinfo = Update.update_crit_death_ld (glds, frms_popped, frm_ldataAlloc, iinfo)
              val iinfo = Update.update_relativePop (throw_lab, frms_popped, iinfo)
              in
                case VK.base cont
                 of VKB.HALT => let
                     val iinfo = Update.update_display_halt pinfo (throw_lab, iinfo)
                     val glb_list = glb (NONE, SOME args, NONE)
                     val gld_list = gld (NONE, SOME args, NONE)
                     val iinfo = Update.update_halt_values pinfo (glb_list, gld_list, iinfo)
                     val iinfo = AInfo.with_callWebsK (iinfo, CallWebs.add_unknown_lam (AInfo.callWebsK iinfo, {call=throw_lab}))
                     in (HALT args, iinfo) end
                  | (VKB.CLOK (cloK as ((_, lab, xs, body), env_K, envK_K, lexFrms_cloK))) =>
                    if (length args) <> (length xs)
                      then raise Fail "bad program"
                      else let
                        (* val _ = if (Label.toString lab) = (*"L061F"*) "L05D7" then CheckAnalysisResults.say ((List.map CValue.toString args) @ ["cont", "\n"]) else () *)
                        val (lexFrms', stack') = push_new_frm (lab, lexFrms_cloK, stack_popped)
                        (* val () = Verbose.say ["CallingK ", Label.toString lab, " with ", String.concatWithMap " " V.toString args, "\n"] *)
                        val () = addLVarsBound xs
                        val iinfo = Update.update_display_cloK pinfo (throw_lab, lexFrms_caller, lexFrms', iinfo)
                        val iinfo = AInfo.with_callWebsK (iinfo, CallWebs.add (AInfo.callWebsK iinfo, {call=throw_lab, lambda=lab}))
                        val triples = ListPair.map (fn (x, arg) => (x, a_alloc (), arg)) (xs, args)
                        val (env', store') = List.foldl (fn ((x, a, arg), (env, store)) => U.extendMaps (x, a, arg, env, store)) (env_K, store) triples
                        val () = CLive.add_a (memo, store', List.map #2 triples)
                        val iinfo = Update.update_lvarUniquenessCrit (xs, glbs, lexFrms', frm_bindingAlloc, frm_live, iinfo)
                        val () = U.update_frm_bindingAlloc (frm_bindingAlloc, lexFrms', List.map (fn (x, a, _) => (x, a)) triples)
                        val () = List.app (fn x => U.incr_lvar_count (mutable_state, x)) xs
                        val iinfo = ListPair.foldl (fn (x, d, iinfo) => Update.update_lvarEnvMatch (x, d, lexFrms, iinfo)) iinfo (xs, args)
                        in (TRANS (body, env', store', envK_K, storeK, lexFrms', stack'), iinfo) end
              end
        (* end case *)
      end

end
