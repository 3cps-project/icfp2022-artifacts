(* live.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Computes liveness information by looking through all reachable values and continuation values.
 *)

structure Live : sig

  type t

  val make : CPSInformation.t * StateSpace.t -> t
  val live_b : t
        -> ((LVar.Set.set * CVar.Set.set * Env.t * EnvK.t * AddrProxy.t) option) * (Addr.t list) * ((AddrK.t * AddrProxy.t) list)
        -> Binding.Set.set list
  val live_ld : t
        -> ((LVar.Set.set * CVar.Set.set * Env.t * EnvK.t * AddrProxy.t) option) * (Addr.t list) * ((AddrK.t * AddrProxy.t) list)
        -> Label.Set.set list

end = struct

  structure C = CPS
  structure CU = CPSUtil
  structure U = TransitionUtil
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set

  structure PInfo = CPSInformation

  structure AS = Addr.Set
  structure BS = Binding.Set

  structure AddrKProxyPair = struct
  type t = AddrK.t * AddrProxy.t
  fun compare ((aK1, aP1), (aK2, aP2)) =
      case AddrK.compare (aK1, aK2)
       of EQUAL => AddrProxy.compare (aP1, aP2)
        | ord => ord
  structure Key = struct type ord_key = t val compare = compare end
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  end

  structure AKPS = AddrKProxyPair.Set
  structure AKPM = AddrKProxyPair.Map

  structure IntSet = RedBlackSetFn (struct type ord_key = int
                                           val compare = Int.compare
                                    end)
  structure IntHSet = HashSetFn (struct type hash_key = int
                                         fun sameKey (i : int, j : int) = (i = j)
                                         val hashVal = Word.fromInt
                                 end)
  structure IntTbl = HashTableFn (struct type hash_key = int
                                         fun sameKey (i : int, j : int) = (i = j)
                                         val hashVal = Word.fromInt
                                  end)

  (*
  val timerAddrSuccs = PhaseTimer.newPhase (Timers.timeExtAnalysisAbstractGC, "address successors")
  val timerSCC = PhaseTimer.newPhase (Timers.timeExtAnalysisAbstractGC, "scc")
  val timerImmLiveB = PhaseTimer.newPhase (Timers.timeExtAnalysisAbstractGC, "imm live b")
  val timerImmLiveLD = PhaseTimer.newPhase (Timers.timeExtAnalysisAbstractGC, "imm live ld")
  val timerDP = PhaseTimer.newPhase (Timers.timeExtAnalysisAbstractGC, "dp")
  val timerWL = PhaseTimer.newPhase (timerDP, "wl")
  fun doTimer timer f arg =
      PhaseTimer.withTimer timer f arg
  *)

  type t = {pinfo : PInfo.t,
            store : Store.t,
            storeK : StoreK.t,
            storeP : StoreProxy.t,
            a_scc : int Addr.Tbl.hash_table,
            a_succ : Addr.Set.set Addr.Tbl.hash_table,
            a_i_b : BS.set Addr.Tbl.hash_table,
            a_i_ld : LS.set Addr.Tbl.hash_table,
            scc_succ : IntSet.set IntTbl.hash_table,
            scc_b : BS.set IntTbl.hash_table,
            scc_ld : LS.set IntTbl.hash_table,
            a_b : BS.set Addr.Tbl.hash_table,
            a_ld : LS.set Addr.Tbl.hash_table,
            aK_aP_b : (BS.set AKPM.map) ref,
            aK_aP_ld : (LS.set AKPM.map) ref}

  exception LiveFail

    (*
    This story is simplified a lot if all varKs map through addresses...
    *)

  structure LiveBindingsWL : sig

    val lb_a : t -> Addr.t -> BS.set * IntSet.set
    val lb_aK_aP : t -> AddrK.t * AddrProxy.t -> BS.set * IntSet.set

  end = struct

    val empty = ([], AS.empty, [], AKPS.empty, BS.empty, IntSet.empty)

    fun add_a_wl (memo : t as {a_b, a_scc, ...}, a, (wl, seen, wl_KP, seen_KP, lb, scc_prev)) =
        if AS.member (seen, a)
        then (wl, seen, wl_KP, seen_KP, lb, scc_prev)
        else
            if Addr.Tbl.inDomain a_b a
            then (wl, AS.add (seen, a), wl_KP, seen_KP, lb, IntSet.add (scc_prev, Addr.Tbl.lookup a_scc a))
            else (a::wl, AS.add (seen, a), wl_KP, seen_KP, lb, scc_prev)

    fun add_aK_aP_wl (memo : t as {aK_aP_b, ...}, aK, aP, (wl, seen, wl_KP, seen_KP, lb, scc_prev)) =
        if AKPS.member (seen_KP, (aK, aP))
        then (wl, seen, wl_KP, seen_KP, lb, scc_prev)
        else case AKPM.find (! aK_aP_b, (aK, aP))
              of NONE => (wl, seen, (aK, aP)::wl_KP, AKPS.add (seen_KP, (aK, aP)), lb, scc_prev)
               | SOME bs => (wl, seen, wl_KP, AKPS.add (seen_KP, (aK, aP)), BS.union (lb, bs), scc_prev)

    fun add_lv_wl (memo, env, x, (wl, seen, wl_KP, seen_KP, lb, scc_prev)) = let
        val a = Env.lookup (env, x)
    in add_a_wl (memo, a, (wl, seen, wl_KP, seen_KP, BS.add (lb, (x, a)), scc_prev)) end

    fun add_cv_wl (memo as {pinfo, ...}, envK, k, aP, acc) = let
        val aK = EnvK.lookup (envK, k)
    in add_aK_aP_wl (memo, aK, aP, acc) end

    fun add_xs_wl (memo, xs, env, acc) = let
        val acc = LVS.foldl (fn (x, acc) => add_lv_wl (memo, env, x, acc)) acc xs
    in acc end

    fun add_vars_wl (memo, xs, ks, env, envK, aP, acc) = let
        val acc = add_xs_wl (memo, xs, env, acc)
        val acc = CVS.foldl (fn (k, acc) => add_cv_wl (memo, envK, k, aP, acc)) acc ks
    in acc end

    and add_cloK_aP_wl (memo : t as {pinfo, ...}, cloK, aP, acc) = let
        val (lamK, env, envK, tenv) = CloK.get cloK
        val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
        val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
    in add_vars_wl (memo, fv_lv, fv_cv, env, envK, aP, acc) end

    fun lb_wl (memo : t as {pinfo, a_succ, a_i_b, store, storeK, storeP, ...}, acc) = let
        fun loc (wl, seen, wl_KP, seen_KP, lb, scc_prev) =
            (case wl
              of [] =>
                 (case wl_KP
                   of [] => (lb, scc_prev)
                    | (aK, aP)::rst_KP => let
                        val dK = StoreK.lookup (storeK, aK)
                        val (cloK_aPs, _) = U.cloKOf (fn _ => (), dK, aP, storeP)
                        fun handle_cloK_aP ((cloK, aP), acc) =
                            add_cloK_aP_wl (memo, cloK, aP, acc)
                    in loc (List.foldl handle_cloK_aP ([], seen, rst_KP, seen_KP, lb, scc_prev) cloK_aPs) end)
               | a::rst => let
                   val lb = BS.union (lb, Addr.Tbl.lookup a_i_b a)
                   val acc = (rst, seen, wl_KP, seen_KP, lb, scc_prev)
                   val succs = Addr.Tbl.lookup a_succ a
                   val acc = Addr.Set.foldl (fn (a', acc) => add_a_wl (memo, a, acc)) acc succs
               in loc acc end)
    in loc acc end

    fun lb_a memo a =
        lb_wl (memo, add_a_wl (memo, a, empty))

    fun lb_aK_aP memo (aK, aP) =
        lb_wl (memo, add_aK_aP_wl (memo, aK, aP, empty))

  end

  structure LiveBindingsWL_A : sig

    val lb_a : t * int * Addr.t list -> BS.set * IntSet.set

  end = struct

    fun lb_a (memo as {a_scc, a_succ, a_i_b, ...} : t, scc, addrs) = let
        fun handle_a (a, (bs, scc_prev)) = let
            val bs = BS.union (bs, Addr.Tbl.lookup a_i_b a)
            val succs = Addr.Tbl.lookup a_succ a
            fun handle_a' (a', scc_prev) = let
                val scc' = Addr.Tbl.lookup a_scc a'
            in if scc' = scc
               then scc_prev
               else IntSet.add (scc_prev, scc')
            end
            val scc_prev = Addr.Set.foldl handle_a' scc_prev succs
        in (bs, scc_prev) end
        val result = List.foldl handle_a (BS.empty, IntSet.empty) addrs
    in result end

  end

  structure LiveLDataWL_A : sig

    val ld_a : t * int * Addr.t list -> LS.set * IntSet.set

  end = struct

    fun ld_a (memo as {a_scc, a_succ, a_i_ld, ...} : t, scc, addrs) = let
        fun handle_a (a, (lds, scc_prev)) = let
            val lds = LS.union (lds, Addr.Tbl.lookup a_i_ld a)
            val succs = Addr.Tbl.lookup a_succ a
            fun handle_a' (a', scc_prev) = let
                val scc' = Addr.Tbl.lookup a_scc a'
            in if scc' = scc
               then scc_prev
               else IntSet.add (scc_prev, scc')
            end
            val scc_prev = Addr.Set.foldl handle_a' scc_prev succs
        in (lds, scc_prev) end
        val result = List.foldl handle_a (LS.empty, IntSet.empty) addrs
    in result end

  end

  structure LiveLDataWL : sig

    val ld_a : t -> Addr.t -> LS.set
    val ld_aK_aP : t -> AddrK.t * AddrProxy.t -> LS.set

  end = struct

    val empty = ([], AS.empty, [], AKPS.empty, LS.empty)

    fun add_a_wl (memo : t as {a_ld, store, ...}, a, (wl, seen, wl_KP, seen_KP, lds)) =
        if AS.member (seen, a)
        then (wl, seen, wl_KP, seen_KP, lds)
        else case Addr.Tbl.find a_ld a
              of NONE => let
                  val lds = LS.union (lds, Value.labels (Store.lookup (store, a)))
              in (a::wl, AS.add (seen, a), wl_KP, seen_KP, lds) end
               | SOME lds' => let
                   val lds = LS.union (LS.union (lds, lds'), Value.labels (Store.lookup (store, a)))
               in (wl, AS.add (seen, a), wl_KP, seen_KP, lds) end

    fun add_aK_aP_wl (memo : t as {aK_aP_ld, ...}, aK, aP, (wl, seen, wl_KP, seen_KP, lds)) =
        if AKPS.member (seen_KP, (aK, aP))
        then (wl, seen, wl_KP, seen_KP, lds)
        else case AKPM.find (! aK_aP_ld, (aK, aP))
              of NONE => (wl, seen, (aK, aP)::wl_KP, AKPS.add (seen_KP, (aK, aP)), lds)
               | SOME lds' => (wl, seen, wl_KP, AKPS.add (seen_KP, (aK, aP)), LS.union (lds, lds'))

    fun add_lv_wl (memo, env, x, acc) = let
        val a = Env.lookup (env, x)
    in add_a_wl (memo, a, acc) end

    fun add_cv_wl (memo, envK, k, aP, acc) = let
        val aK = EnvK.lookup (envK, k)
    in add_aK_aP_wl (memo, aK, aP, acc) end

    fun add_xs_wl (memo, xs, env, acc) = let
        val acc = LVS.foldl (fn (x, acc) => add_lv_wl (memo, env, x, acc)) acc xs
    in acc end

    fun add_vars_wl (memo, xs, ks, env, envK, aP, acc) = let
        val acc = add_xs_wl (memo, xs, env, acc)
        val acc = CVS.foldl (fn (k, acc) => add_cv_wl (memo, envK, k, aP, acc)) acc ks
    in acc end

    fun add_value_wl (memo : t as {pinfo, ...}, d, acc) = let
        fun loc_clo (clo, acc) = let
            val (lam, env, tenv) = Clo.get clo
            val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
        in add_xs_wl (memo, fv_lv, env, acc) end
        fun loc_dv (dv, acc) = let
            val (_, dcon, ao) = DataValue.get dv
        in case ao of SOME a => add_a_wl (memo, a, acc) | NONE => acc end
        fun loc_tv (tv, acc) = let
            val (_, addrs) = TupleValue.get tv
        in List.foldl (fn (a, acc) => add_a_wl (memo, a, acc)) acc addrs end
        fun loc_ref (a, acc) = add_a_wl (memo, a, acc)
        fun loc_arr ((_, a), acc) = add_a_wl (memo, a, acc)
        fun loc_unknown acc = acc
    in Value.fold loc_clo loc_dv loc_tv loc_ref loc_arr loc_unknown acc d end

    and add_cloK_aP_wl (memo : t as {pinfo, ...}, cloK, aP, acc) = let
        val (lamK, env, envK, tenv) = CloK.get cloK
        val fv_lv = PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK)
        val fv_cv = PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK)
    in add_vars_wl (memo, fv_lv, fv_cv, env, envK, aP, acc) end

    fun ld_wl (memo : t as {store, storeK, storeP, ...}, acc) = let
        fun loc (wl, seen, wl_KP, seen_KP, ld_list) =
            (case wl
              of [] =>
                 (case wl_KP
                   of [] => ld_list
                    | (aK, aP)::rst_KP => let
                        val dK = StoreK.lookup (storeK, aK)
                        val (cloK_aPs, _) = U.cloKOf (fn _ => (), dK, aP, storeP)
                        fun handle_cloK_aP ((cloK, aP), acc) =
                            add_cloK_aP_wl (memo, cloK, aP, acc)
                    in loc (List.foldl handle_cloK_aP ([], seen, rst_KP, seen_KP, ld_list) cloK_aPs) end)
               | a::rst => let
                   val d = Store.lookup (store, a)
               in loc (add_value_wl (memo, d, (rst, seen, wl_KP, seen_KP, ld_list))) end)
    in loc acc end

    fun ld_a memo a =
        ld_wl (memo, (add_a_wl (memo, a, empty)))

    fun ld_aK_aP memo (aK, aP) =
        ld_wl (memo, (add_aK_aP_wl (memo, aK, aP, empty)))

  end

  exception SCC of string
  (* compute the strongly connected components of the address space,
     using Tarjan's SCC algorithm.
     Derived using pseudocode from
     https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm *)
  fun scc (pinfo, a_succ, store) = let
      fun set_lowlink (lowlink_tbl, a, lowlink) =
          (Addr.Tbl.insert lowlink_tbl (a, lowlink); lowlink_tbl)
      fun set_index (index_tbl, a, index) =
          (Addr.Tbl.insert index_tbl (a, index); index_tbl)
      fun get_lowlink (lowlink_tbl, a) =
          Addr.Tbl.lookup lowlink_tbl a
      fun get_index (index_tbl, a) =
          Addr.Tbl.lookup index_tbl a
      fun isOnStack (onStack, a) =
          case Addr.Tbl.find onStack a of NONE => false | SOME b => b
      fun indexIsUndefined (index_tbl, a) =
          case Addr.Tbl.find index_tbl a of NONE => true | SOME _ => false
      fun handle_a (a, (index, stack, onStack, index_tbl, lowlink_tbl, sccs)) = let
          fun handle_succ (a', (index, stack, onStack, index_tbl, lowlink_tbl, sccs)) =
              if indexIsUndefined (index_tbl, a')
              then let
                  val (index, stack, onStack, index_tbl, lowlink_tbl, sccs) =
                      handle_a (a', (index, stack, onStack, index_tbl, lowlink_tbl, sccs))
                  val a_lowlink = get_lowlink (lowlink_tbl, a)
                  val a'_lowlink = get_lowlink (lowlink_tbl, a')
                  val min = Int.min (a_lowlink, a'_lowlink)
                  val lowlink_tbl =
                      if min = a_lowlink
                      then lowlink_tbl (* if nothing has changed, don't update the table *)
                      else set_lowlink (lowlink_tbl, a, min)
              in (index, stack, onStack, index_tbl, lowlink_tbl, sccs) end
              else if isOnStack (onStack, a')
              then let
                  val a_lowlink = get_lowlink (lowlink_tbl, a)
                  val a'_index = get_index (index_tbl, a')
                  val min = Int.min (a_lowlink, a'_index)
                  val lowlink_tbl =
                      if min = a_lowlink
                      then lowlink_tbl (* if nothing has changed, don't update the table *)
                      else set_lowlink (lowlink_tbl, a, min)
              in (index, stack, onStack, index_tbl, lowlink_tbl, sccs) end
              else (index, stack, onStack, index_tbl, lowlink_tbl, sccs)
          fun popStack (stack, scc, onStack) =
              case stack
               of a' :: stack' => let
                   val scc = a' :: scc
                   val onStack = (Addr.Tbl.insert onStack (a', false); onStack)
               in if Addr.same (a, a')
                  then (stack', scc, onStack)
                  else popStack (stack', scc, onStack)
               end
                | [] => raise Fail "bad"
          val index_tbl = set_index (index_tbl, a, index)
          val lowlink_tbl = set_lowlink (lowlink_tbl, a, index);
          val index = index + 1
          val stack = a :: stack
          val onStack = (Addr.Tbl.insert onStack (a, true); onStack)
          val (index, stack, onStack, index_tbl, lowlink_tbl, sccs) =
              Addr.Set.foldl handle_succ (index, stack, onStack, index_tbl, lowlink_tbl, sccs)
                             (Addr.Tbl.lookup a_succ a)
            in
              if (get_lowlink (lowlink_tbl, a)) = (get_index (index_tbl, a))
                then let
                  val (stack, scc, onStack) = popStack (stack, [], onStack)
                  val sccs = scc :: sccs
                  in (index, stack, onStack, index_tbl, lowlink_tbl, sccs) end
                else (index, stack, onStack, index_tbl, lowlink_tbl, sccs)
          end
      (* I tried using maps instead but it seems like hash tables were a little faster *)
      val index_tbl = Addr.Tbl.mkTable (100, SCC "index_tbl")
      val lowlink_tbl = Addr.Tbl.mkTable (100, SCC "lowlink_tbl")
      val onStack = Addr.Tbl.mkTable (100, SCC "onStack")
      val stack = []
      val index = 0
      val sccs = []
      val initial = (index, stack, onStack, index_tbl, lowlink_tbl, sccs)
      fun handle_entry (a, _, acc as (index, stack, onStack, index_tbl, lowlink_tbl, sccs)) =
          if indexIsUndefined (index_tbl, a)
          then handle_a (a, acc)
          else acc
      val (index, stack, onStack, index_tbl, lowlink_tbl, sccs) =
          Store.foldi handle_entry initial store
      val () = if List.null stack then () else raise Fail "hm"
      in List.rev sccs end

  fun reduce ({scc_succ, ...} : t, sccs) = let
      (* keep all the sccs which are not a successor of any other in the list *)
      fun check_scc scc =
          not (IntSet.exists (fn scc' => IntSet.member (IntTbl.lookup scc_succ scc', scc)) sccs)
      val sccs = IntSet.filter check_scc sccs
      in sccs end

  fun compute_bs (memo as {scc_b, ...} : t, (bs, scc_prev)) = let
      (* val scc_prev' = reduce (memo, scc_prev) *)
      val bs = IntSet.foldl (fn (scc', acc) => BS.union (acc, IntTbl.lookup scc_b scc')) bs scc_prev
      in bs end

  fun compute_lds (memo as {scc_ld, ...} : t, (lds, scc_prev)) = let
      (* val scc_prev = reduce (memo, scc_prev) *)
      val lds = IntSet.foldl (fn (scc', acc) => LS.union (acc, IntTbl.lookup scc_ld scc')) lds scc_prev
      in lds end

  fun make (pinfo, state_space : StateSpace.t) = let
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val a_b = Addr.Tbl.mkTable (100, Fail "live a_b")
      val a_ld = Addr.Tbl.mkTable (100, Fail "live a_ld")
      val a_scc = Addr.Tbl.mkTable (100, Fail "live a_scc")
      val a_succ = Addr.Tbl.mkTable (100, Fail "live a_succ")
      val a_i_b = Addr.Tbl.mkTable (100, Fail "live a_i_b")
      val a_i_ld = Addr.Tbl.mkTable (100, Fail "live a_i_ld")
      val scc_succ = IntTbl.mkTable (100, Fail "live scc_succ")
      val scc_b = IntTbl.mkTable (100, LiveFail)
      val scc_ld = IntTbl.mkTable (100, LiveFail)
      val aK_aP_b = ref AKPM.empty
      val aK_aP_ld = ref AKPM.empty
      val memo = {pinfo=pinfo, store=store, storeK=storeK, storeP=storeP,
                  a_scc=a_scc, a_succ=a_succ, scc_succ=scc_succ, scc_b=scc_b, scc_ld=scc_ld,
                  a_i_b=a_i_b, a_i_ld=a_i_ld,
                  a_b=a_b, a_ld=a_ld, aK_aP_b=aK_aP_b, aK_aP_ld=aK_aP_ld}
      fun get_succs a = let
          fun add_succ (a', succs) = Addr.Set.add (succs, a')
          fun add_succs (a's, succs) = Addr.Set.addList (succs, a's)
          fun loc_clo (clo, succs) = let
              val (lam, env, tenv) = Clo.get clo
              val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
          in LVar.Set.foldl (fn (x, succs) => add_succ (Env.lookup (env, x), succs)) succs fv_lv end
          fun loc_dv (dv, succs) = let
              val (_, dcon, ao) = DataValue.get dv
          in case ao of SOME a => add_succ (a, succs) | NONE => succs end
          fun loc_tv (tv, succs) = let
              val (_, addrs) = TupleValue.get tv
          in add_succs (addrs, succs) end
          fun loc_ref (a, succs) = add_succ (a, succs)
          fun loc_arr ((_, a), succs) = add_succ (a, succs)
          fun loc_unknown succs = succs
          val d = Store.lookup (store, a)
          in Value.fold loc_clo loc_dv loc_tv loc_ref loc_arr loc_unknown Addr.Set.empty d end
      fun compute_a_succ () = let
          fun handle_a (a, _) = let
              val succs = get_succs a
              val () = Addr.Tbl.insert a_succ (a, succs)
              in () end
          in Store.appi handle_a store end
      (* val () = doTimer timerAddrSuccs compute_a_succ () *)
      val () = compute_a_succ ()
      (* val sccs = doTimer timerSCC scc (pinfo, a_succ, store) *)
      val sccs = scc (pinfo, a_succ, store)

      (*
      val _ = Debug.say [Addr.Tbl.foldi (fn (a, addrs, acc) => Int.toString (Addr.Set.numItems addrs) ^ " " ^ acc) "" a_succ, "\n"]
      val _ = Debug.say [Store.foldi (fn (a, d, acc) => Int.toString (Value.fold_tvs (fn (_, acc) => 1 + acc) 0 d) ^ " " ^ acc) "" store, "\n"]
      *)
      fun compute_a_i_b () = let
          fun handle_a_d (a, d) = let
              fun loc_clo (clo, bs) = let
                  val (lam, env, tenv) = Clo.get clo
                  val fv_lv = PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam)
                  val bs = LVS.foldl (fn (x, bs) => BS.add (bs, (x, Env.lookup (env, x))))
                                     bs fv_lv
              in bs end
              val bs = Value.fold_clos loc_clo BS.empty d
              val () = Addr.Tbl.insert a_i_b (a, bs)
              in () end
          in Store.appi handle_a_d store end
      (* val () = doTimer timerImmLiveB compute_a_i_b () *)
      val () = compute_a_i_b ()

      fun compute_a_i_ld () = let
          fun handle_a_d (a, d) = let
              val lds = Value.labels d
              val () = Addr.Tbl.insert a_i_ld (a, lds)
              in () end
          in Store.appi handle_a_d store end
      (* val () = doTimer timerImmLiveLD compute_a_i_ld () *)
      val () = compute_a_i_ld ()

      fun compute_a_scc () = let
          fun handle_scc (index, scc) = let
              val () = List.app (fn a => Addr.Tbl.insert a_scc (a, index)) scc
              in () end
          in List.appi handle_scc sccs end
      val () = compute_a_scc ()

      (*
      fun compute_scc_succs () = let
          fun handle_scc (index, scc) = let
              val () = List.app (fn a => Addr.Tbl.insert a_scc (a, index)) scc
              fun handle_a (a, acc) = let
                  val succs = get_succs a
                  val acc = Addr.Set.foldl (fn (a', acc) => let
                                                val scc' = Addr.Tbl.lookup a_scc a'
                                            in if scc' = index
                                               then acc
                                               else IntSet.add (acc, scc')
                                            end)
                                           acc succs
              in acc end
              val scc_succs = List.foldl handle_a IntSet.empty scc
              (* val scc_succs = reduce (memo, scc_succs) *)
              val succs = IntSet.foldl (fn (scc', acc) => IntSet.union (acc, IntTbl.lookup scc_succ scc'))
                                       IntSet.empty scc_succs
              val () = IntTbl.insert scc_succ (index, scc_succs)
          in () end
      in List.appi handle_scc sccs end
      val () = doTimer timer5 compute_scc_succs ()
      *)
      fun dp_bs_and_lds () = let
          fun handle_scc (scc, addrs) = let
              (* The reachable bindings should be the same on each connected component
                 of the address reachability graph *)
              val a = hd addrs
              (* val bs_res = doTimer timerWL LiveBindingsWL_A.lb_a (memo, scc, addrs) *)
              val bs_res = LiveBindingsWL_A.lb_a (memo, scc, addrs)
              val bs = compute_bs (memo, bs_res)
              val () = List.app (fn a => Addr.Tbl.insert a_b (a, bs)) addrs
              val () = IntTbl.insert scc_b (scc, bs)
              (* val lds_res = doTimer timerWL LiveLDataWL_A.ld_a (memo, scc, addrs) *)
              val lds_res = LiveLDataWL_A.ld_a (memo, scc, addrs)
              val lds = compute_lds (memo, lds_res)
              val () = List.app (fn a => Addr.Tbl.insert a_ld (a, lds)) addrs
              val () = IntTbl.insert scc_ld (scc, lds)
          in () end
          val () = List.appi handle_scc sccs
      in () end
      (* val () = doTimer timerDP dp_bs_and_lds () *)
      val () = dp_bs_and_lds ()
      in memo end

  fun aux_live_b_a (memo : t as {scc_b, a_scc, ...}, a, (seen, seen_KP, bs_list)) = let
      val scc = Addr.Tbl.lookup a_scc a
      in
        if IntSet.member (seen, scc)
          then (seen, seen_KP, bs_list)
          else (IntSet.add (seen, scc), seen_KP, (IntTbl.lookup scc_b scc) :: bs_list)
      end

  and aux_live_b_aK_aP (memo : t as {aK_aP_b, ...}, aK, aP, (seen, seen_KP, bs_list)) =
      if AKPS.member (seen_KP, (aK, aP))
        then (seen, seen_KP, bs_list)
        else case AKPM.find (! aK_aP_b, (aK, aP))
            of SOME bs => (seen, AKPS.add (seen_KP, (aK, aP)), bs :: bs_list)
             | NONE => let
                 val bs_res = LiveBindingsWL.lb_aK_aP memo (aK, aP)
                 val bs = compute_bs (memo, bs_res)
             in aK_aP_b := AKPM.insert (! aK_aP_b, (aK, aP), bs);
                (seen, AKPS.add (seen_KP, (aK, aP)), bs :: bs_list)
             end

  and aux_live_b_xs (memo, xs, env, acc) = let
      fun handle_x (x, (seen, seen_KP, bs_list)) = let
          val a = Env.lookup (env, x)
      in aux_live_b_a (memo, a, (seen, seen_KP, BS.singleton (x, a) :: bs_list)) end
      val acc = LVS.foldl handle_x acc xs
      in acc end

  and aux_live_b_vars (memo, xs, ks, env, envK, aP, acc) = let
      val acc = aux_live_b_xs (memo, xs, env, acc)
      val acc =
          CVS.foldl (fn (k, acc) => let
                         val aK = EnvK.lookup (envK, k)
                     in aux_live_b_aK_aP (memo, aK, aP, acc) end)
                    acc ks
      in acc end

  fun live_b memo (vars_opt, addrs, addrKs) = let
      val acc = (IntSet.empty, AKPS.empty, [])
      val acc = case vars_opt
                 of SOME (lv, cv, env, envK, aP) => aux_live_b_vars (memo, lv, cv, env, envK, aP, acc)
                  | NONE => acc
      val acc = List.foldl (fn (a, acc) => aux_live_b_a (memo, a, acc)) acc addrs
      val acc = List.foldl (fn ((aK, aP), acc) => aux_live_b_aK_aP (memo, aK, aP, acc)) acc addrKs
      val (seen, seen_KP, bs_list) = acc
      in bs_list end

  fun aux_live_ld_a (memo : t as {scc_ld, a_scc, ...}, a, (seen, seen_KP, lds_list)) = let
      val scc = Addr.Tbl.lookup a_scc a
      in
        if IntSet.member (seen, scc)
          then (seen, seen_KP, lds_list)
          else (IntSet.add (seen, scc), seen_KP, (IntTbl.lookup scc_ld scc) :: lds_list)
      end

  and aux_live_ld_aK_aP (memo : t as {aK_aP_ld, ...}, aK, aP, (seen, seen_KP, ld_list)) =
      if AKPS.member (seen_KP, (aK, aP))
        then (seen, seen_KP, ld_list)
        else case AKPM.find (! aK_aP_ld, (aK, aP))
            of SOME ld => (seen, AKPS.add (seen_KP, (aK, aP)), ld :: ld_list)
             | NONE => let
                val ld = LiveLDataWL.ld_aK_aP memo (aK, aP)
                in aK_aP_ld := AKPM.insert (! aK_aP_ld, (aK, aP), ld);
                  (seen, AKPS.add (seen_KP, (aK, aP)), ld :: ld_list)
                end

  and aux_live_ld_xs (memo, xs, env, acc) = let
      fun handle_x (x, acc) = let
          val a = Env.lookup (env, x)
      in aux_live_ld_a (memo, a, acc) end
      val acc = LVS.foldl handle_x acc xs
      in acc end

  and aux_live_ld_vars (memo, xs, ks, env, envK, aP, acc) = let
      val acc = aux_live_ld_xs (memo, xs, env, acc)
      fun handle_cvar (k, acc) = let
          val aK = EnvK.lookup (envK, k)
      in aux_live_ld_aK_aP (memo, aK, aP, acc) end
      val acc = CVS.foldl handle_cvar acc ks
      in acc end

  fun live_ld memo (vars_opt, addrs, addrKs) = let
      val acc = (IntSet.empty, AKPS.empty, [])
      val acc =
          case vars_opt
           of SOME (lv, cv, env, envK, aP) => aux_live_ld_vars (memo, lv, cv, env, envK, aP, acc)
            | NONE => acc
      val acc = List.foldl (fn (a, acc) => aux_live_ld_a (memo, a, acc)) acc addrs
      val acc = List.foldl (fn ((aK, aP), acc) => aux_live_ld_aK_aP (memo, aK, aP, acc)) acc addrKs
      val (seen, seen_KP, ld_list) = acc
      in ld_list end

end
