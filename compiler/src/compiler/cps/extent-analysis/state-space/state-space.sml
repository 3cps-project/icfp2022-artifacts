(* state-space.sml
 *
 * Computes the abstract state space.
 *)

structure StateSpace : sig

  type t = {configs : Config.Set.set,
            store : Store.t,
            storeK : StoreK.t,
            storeP : StoreProxy.t,
            graph : Config.Set.set Config.Map.map,
            util_addrs : Transition.util_addrs,
            ldata_passed_to_unknown : Label.Set.set,
            cdata_passed_to_unknown : Label.Set.set}

  (* A "mathematically precise" state space computation that is expensive to compute.
     Compared against the quickly produced state space for correctness in 
     check-analysis.sml *)
  val stateSpaceMath : CPSInformation.t * Transition.util_addrs * CPS.comp_unit -> t
  (* A less "mathematically precise" state space computation that is faster to compute,
     but only uses some of the optimizations that the efficient method uses. *)
  val stateSpaceMath2 : CPSInformation.t * Transition.util_addrs * CPS.comp_unit -> t
                                                                                        
  (* Computes the state space of the program in a reasonably efficient manner *)
  val stateSpace : CPSInformation.t * Transition.util_addrs * CPS.comp_unit -> t

  type stats = {update_addr_count : int,
                update_addrP_count : int}
  (* Give some stats about the analysis computations *)
  val stats : unit -> stats

end = struct

  (* FIXME: refactor the internally tracked state space tuples to be records *)

  structure PInfo = CPSInformation
  structure LS = Label.Set
  structure AS = Addr.Set
  structure AT = Addr.Tbl
  structure APT = AddrProxy.Tbl

  structure T = Transition
  structure U = TransitionUtil
  structure ST = Stats

  structure DebugSS = DebugAnalysisStateSpace

  (* TODO: temporarily removing the graph from the state space, since
     it turns out to be expensive to compute and we don't use it for
     anything at the moment.
     All graphs will be the empty config map. *)
  (* To re-add the graph computations, uncomment all sections marked TODO:GRAPH *)

  (* counters to track how many / what kind of updates are going on *)
  local
      val grp = ST.Group.newWithPri ST.Group.root ("total-state-space", [2, 1])
      val newCntr = ST.Counter.new grp
  in
  val total_counter = newCntr ("steps")
  val update_addr_counter = newCntr ("update-addr-steps")
  val update_addrP_counter = newCntr ("update-addrP-steps")
  val new_config_counter = newCntr ("new-config-steps")
  val states_counter = newCntr ("configs")
  val prune_counter = newCntr ("prune")
  val pruneP_counter = newCntr ("pruneP")
  val tmp_counter = newCntr ("number store extensions")
  end (* local *)

  type stats = {update_addr_count : int,
                update_addrP_count : int}
  fun stats () = let
      val update_addr_count = ST.Counter.value update_addr_counter
      val update_addrP_count = ST.Counter.value update_addrP_counter
  in {update_addr_count=update_addr_count,
      update_addrP_count=update_addrP_count}
  end

  (* Local timers for profiling *)
  (*
  fun doTimer timer f =
      PhaseTimer.withTimer timer f ()
  val timerTrans = PhaseTimer.newPhase (Timers.timeExtAnalysisStateSpace, "transition")
  val timerUnknown = PhaseTimer.newPhase (Timers.timeExtAnalysisStateSpace, "unknown transition")
  val timerUpdate = PhaseTimer.newPhase (Timers.timeExtAnalysisStateSpace, "update")
  val timerUpdateConfigs = PhaseTimer.newPhase (timerUpdate, "update configs")
  val timerUpdateGraph = PhaseTimer.newPhase (timerUpdate, "update graph")
  val timerUpdateStoreK = PhaseTimer.newPhase (timerUpdate, "update storeK")
  val timerAddUpdate_a = PhaseTimer.newPhase (timerUpdate, "add update a")
  val timerAddUpdate_a_diff = PhaseTimer.newPhase (timerAddUpdate_a, "add update a diff")
  val timerAddUpdate_a_wljoin = PhaseTimer.newPhase (timerAddUpdate_a, "add update a wl join")
  val timerAddUpdate_aP = PhaseTimer.newPhase (timerUpdate, "add update aP")
  val timerUpdateStore = PhaseTimer.newPhase (timerAddUpdate_a, "update store")
  val timerUpdateStoreP = PhaseTimer.newPhase (timerAddUpdate_aP, "update storeP")
  *)

  type t = {configs : Config.Set.set,
            store : Store.t,
            storeK : StoreK.t,
            storeP : StoreProxy.t,
            graph : Config.Set.set Config.Map.map,
            util_addrs : Transition.util_addrs,
            ldata_passed_to_unknown : Label.Set.set,
            cdata_passed_to_unknown : Label.Set.set}

  fun ensureVertexExists (xi, graph) =
      (case Config.Map.find (graph, xi)
        of SOME _ => graph
         | NONE => Config.Map.insert (graph, xi, Config.Set.empty)
      (* end case **))

  fun addEdge xi (xi', graph) =
      Config.Map.insert (graph, xi, Config.Set.add (Config.Map.lookup (graph, xi), xi'))

  fun initialStateSpace (pinfo, cu as CPS.CU(f, l, xs0, ks0, e0)) = let
      val tenv0 = TEnv.empty
      val aP = U.allocP (l, tenv0, e0, tenv0)
      fun extend (x, (env, store_ext)) = let
          val a = U.alloc (x, tenv0, aP)
          val env = Env.extend (env, x, a)
          (* val store_ext = Store.extend (store_ext, a, Value.add_unknown (Value.empty ())) TODO *)
      in (env, store_ext) end
      val (env0, store0) = List.foldl extend (Env.empty, Store.empty ()) xs0
      fun extendK (k, (envK, storeK_ext)) = let
          val aK = U.allocK (k, tenv0, aP)
          val envK = EnvK.extend (envK, k, aK)
          val storeK_ext = StoreK.extend (storeK_ext, aK, ValueK.from_index (PInfo.k_index pinfo k))
      in (envK, storeK_ext) end
      val (envK0, storeK0) =
          List.foldl extendK (EnvK.empty, StoreK.empty ()) ks0
      val storeP0 = StoreProxy.extend (StoreProxy.empty (), aP, ValueProxy.unknown)
      val xi0 = Config.make (e0, env0, envK0, tenv0, aP)
      val r0 = Config.Set.singleton xi0
      val graph0 = Config.Map.empty
      (* TODO:GRAPH *)
      (* val graph0 = ensureVertexExists (xi0, graph0) *)
      val ldata_passed_to_unknown0 = LS.empty
      val cdata_passed_to_unknown0 = LS.empty
  in (r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0) end

  (* Begins with the initial state, and continually computes a new
     state space by re-propagating every configuration, until a
     fixpoint is reached. *)
  fun stateSpaceMath (pinfo, utilAddrs, cu) = let
      (* joins store_ext into store, reporting if there was any change *)
      fun store_join ((a, d), (store, anyChange)) = 
          case Store.find (store, a)
           of NONE => (Store.extend (store, a, Value.copy d), true)
            | SOME d' => let
                val d = Value.difference (d, d')
            in if Value.isEmpty d
               then (store, anyChange)
               else (Store.extend (store, a, d), true)
            end
      (* joins storeK_ext into storeK, reporting if there was any change *)
      fun storeK_join ((aK, dK), (storeK, anyChange)) = 
          case StoreK.find (storeK, aK)
           of NONE => (StoreK.extend (storeK, aK, dK), true)
            | SOME dK' => 
              case ValueK.compare (dK, dK')
               of EQUAL => (storeK, anyChange)
                | _ => (StoreK.extend (storeK, aK, dK), true)
      (* joins storeP_ext into storeP, reporting if there was any change *)
      fun storeP_join ((aP, dP), (storeP, anyChange)) = 
          case StoreProxy.find (storeP, aP)
           of NONE => (StoreProxy.extend (storeP, aP, dP), true)
            | SOME dP' => let
                val dP = ValueProxy.difference (dP, dP')
            in if ValueProxy.isEmpty dP
               then (storeP, anyChange)
               else (StoreProxy.extend (storeP, aP, dP), true)
            end
      val graph_compare = Config.Map.collate Config.Set.compare
      fun handle_xi (xi, (state_space, changed)) = let
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = state_space
          val (store_changed, storeK_changed, storeP_changed) = changed
          val (next_configs, store_exts, storeK_exts, storeP_exts, ds_passed_to_unknown, dKs_passed_to_unknown) =
              T.trans (pinfo, fn _ => (), fn _ => (), fn _ => (), utilAddrs, xi, store, storeK, storeP)
          val trans = (next_configs, store_exts, storeK_exts, storeP_exts)
          val (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown) =
              T.passed_to_unknown (pinfo, fn _ => (), fn _ => (), fn _ => (), ds_passed_to_unknown, dKs_passed_to_unknown,
                                         store, storeK, storeP,
                                         ldata_passed_to_unknown, cdata_passed_to_unknown,
                                         trans)
          (* TODO:GRAPH *)
          (*
          val graph = ensureVertexExists (xi, graph)
          val graph = List.foldl ensureVertexExists graph next_configs
          val graph = List.foldl (addEdge xi) graph next_configs
          *)
          val configs = Config.Set.addList (configs, next_configs)
          val (store, store_changed) = List.foldl store_join (store, store_changed) store_exts
          val (storeK, storeK_changed) = List.foldl storeK_join (storeK, storeK_changed) storeK_exts
          val (storeP, storeP_changed) = List.foldl storeP_join (storeP, storeP_changed) storeP_exts
          val state_space = (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown)
          val changed = (store_changed, storeK_changed, storeP_changed)
      in (state_space, changed) end
      fun fixpoint state_space = let
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = state_space
          val (state_space', (store_changed, storeK_changed, storeP_changed)) =
              Config.Set.foldl handle_xi (state_space, (false, false, false)) (#1 state_space)
          val (configs', store', storeK', storeP', graph', ldata_passed_to_unknown', cdata_passed_to_unknown') = state_space'
          fun r_changed () = Config.Set.numItems configs' <> Config.Set.numItems configs
          fun ldata_passed_to_unknown_changed () = Label.Set.numItems ldata_passed_to_unknown' <> Label.Set.numItems ldata_passed_to_unknown
          fun cdata_passed_to_unknown_changed () = Label.Set.numItems cdata_passed_to_unknown' <> Label.Set.numItems cdata_passed_to_unknown
          fun compare_edges (xi, edges, anyChange) =
              anyChange orelse (Config.Set.numItems edges <> Config.Set.numItems (Config.Map.lookup (graph', xi)))
          fun graph_changed () = (Config.Map.numItems graph <> Config.Map.numItems graph') orelse (Config.Map.foldli compare_edges false graph)
          fun check_same (msg, changed, compare) = if (case compare of EQUAL => not changed | ord => changed) then () else raise (Fail msg)
          fun do_checks () = let
              val () = check_same ("r", r_changed (), Config.Set.compare (configs, configs'))
              (* val () = check_same ("store", store_changed, Store.compare (store, store')) *)
              (* val () = check_same ("storeK", storeK_changed, StoreK.compare (storeK, storeK')) *)
              (* val () = check_same ("storeP", storeP_changed, StoreProxy.compare (storeP, storeP')) *)
              val () = check_same ("graph", graph_changed (), graph_compare (graph, graph'))
              val () = check_same ("ldata_unknown", ldata_passed_to_unknown_changed (), Label.Set.compare (ldata_passed_to_unknown, ldata_passed_to_unknown'))
              val () = check_same ("cdata_unknown", cdata_passed_to_unknown_changed (), Label.Set.compare (cdata_passed_to_unknown, cdata_passed_to_unknown'))
          in () end
      in
          (* do_checks(); *)
          if store_changed orelse storeK_changed orelse storeP_changed
             orelse (r_changed ())
             orelse (ldata_passed_to_unknown_changed ())
             orelse (cdata_passed_to_unknown_changed ())
             orelse (graph_changed ())
          then fixpoint state_space'
          else state_space
      end
      val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = fixpoint (initialStateSpace (pinfo, cu))
  in {configs=configs,
      store=store,
      storeK=storeK, 
      storeP=storeP,
      graph=graph, 
      util_addrs=utilAddrs,
      ldata_passed_to_unknown=ldata_passed_to_unknown,
      cdata_passed_to_unknown=cdata_passed_to_unknown}
  end

  structure Config_Indices =
  struct
    type t = Config.t * int list

    fun compare ((xi1, l1), (xi2, l2)) =
        case List.collate Int.compare (l1, l2)
         of EQUAL => Config.compare (xi1, xi2)
          | ord => ord

    fun same (x1, x2) =
        case compare (x1, x2)
         of EQUAL => true
          | _ => false

    fun hash (xi, lst) = Config.hash xi

    local
        structure Key = struct type ord_key = t val compare = compare end
        structure HashKey = struct type hash_key = t val sameKey = same val hashVal = hash end
    in
    structure Set = RedBlackSetFn (Key)
    structure Map = RedBlackMapFn (Key)
    structure MSet = MyHashSetFn (HashKey)
    structure Tbl = HashTableFn (HashKey)
    end
  end

  (* Begins with the initial state, and continually computes a new
     state space by re-propagating the configurations until a fixpoint
     is reached. Like the efficient method, it only propagates
     configurations that we know are changed by updated addresses.
     Unlike the efficient method, it does not use the specialized
     propagation functions. *)
  fun fixpointMath2 (pinfo, utilAddrs, r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0) = let
      val addr_tbl = AT.mkTable (100, Fail "addr_tbl")
      val addrP_tbl = APT.mkTable (100, Fail "addrP_tbl")
      fun add_a xi a =
          case AT.find addr_tbl a
           of NONE => AT.insert addr_tbl (a, Config.Set.singleton xi)
            | SOME set => (AT.insert addr_tbl (a, Config.Set.add (set, xi)))
      fun add_aP xi (aP, lst) =
          case APT.find addrP_tbl aP
           of NONE => APT.insert addrP_tbl (aP, Config.Set.singleton xi)
            | SOME set => (APT.insert addrP_tbl (aP, Config.Set.add (set, xi)))

      fun handle_passed_to_unknown (xi, result, transResult) = let
          val (next_configs, store_exts, storeK_exts, storeP_exts, ds_passed_to_unknown, dKs_passed_to_unknown) = transResult
          val trans = (next_configs, store_exts, storeK_exts, storeP_exts)
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = result
          val (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown) =
              T.passed_to_unknown (pinfo, add_a xi, add_a xi, add_aP xi, ds_passed_to_unknown, dKs_passed_to_unknown,
                                         store, storeK, storeP, ldata_passed_to_unknown, cdata_passed_to_unknown,
                                         trans)
          val result = (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) 
          val trans = (next_configs, store_exts, storeK_exts, storeP_exts) 
      in (result, trans) end

      fun update (xi, wl, result, transResult) = let
          val (next_configs, store_exts, storeK_exts, storeP_exts) = transResult
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = result

          fun update_graph () = let
              val graph = ensureVertexExists (xi, graph)
              val graph = List.foldl ensureVertexExists graph next_configs
              val graph = List.foldl (addEdge xi) graph next_configs
          in graph end
          (* TODO:GRAPH *)
          (* val graph = update_graph () *)
                                    
          fun update_configs () = let
              fun handle_config (xi, (configs, wl)) =
                  if Config.Set.member (configs, xi)
                  then (configs, wl)
                  else (Config.Set.add (configs, xi), Config.Set.add (wl, xi))
              val (configs, wl) = List.foldl handle_config (configs, wl) next_configs
          in (configs, wl) end
          val (configs, wl) = update_configs ()

          fun update_storeK () = let
              fun storeK_join ((aK, dK), storeK) =
                  StoreK.extend (storeK, aK, dK) 
              val storeK = List.foldl storeK_join storeK storeK_exts
          in storeK end
          val storeK = update_storeK ()

          fun update_with_a_d ((a, d), (wl, store)) = 
              case Store.find (store, a)
               of SOME d' => let
                   val d = Value.difference (d, d')
               in if Value.isEmpty d
                  then (wl, store)
                  else let
                      val to_xi = AT.lookup addr_tbl a
                      val wl = Config.Set.union (wl, to_xi)
                      val store = Store.extend (store, a, d)
                  in (wl, store) end
               end
                | NONE => (AT.insert addr_tbl (a, Config.Set.empty);
                           (wl, Store.extend (store, a, Value.copy d)))
          fun update_store () = let
              val res = (wl, store)
              val res = List.foldl update_with_a_d res store_exts
          in res end
          val (wl, store) =
              update_store ()

          fun update_with_aP_dP ((aP, dP), (wl, storeP)) = 
              case StoreProxy.find (storeP, aP)
               of SOME dP' => let
                   val dP = ValueProxy.difference (dP, dP')
               in if ValueProxy.isEmpty dP
                  then (wl, storeP)
                  else let
                      val to_xi = APT.lookup addrP_tbl aP
                      val wl = Config.Set.union (wl, to_xi)
                      val storeP = StoreProxy.extend (storeP, aP, dP)
                  in (wl, storeP) end
               end
                | NONE => (APT.insert addrP_tbl (aP, Config.Set.empty); (wl, StoreProxy.extend (storeP, aP, dP)))
          fun update_storeP () = let
              val res = (wl, storeP)
              val res = List.foldl update_with_aP_dP res storeP_exts
          in res end
          val (wl, storeP) =
              update_storeP ()
          val result = (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown)
      in (wl, result) end

      (* handle one element from the wl worklist. *)
      fun handle_wl (xi, wl, result) = let
          val (_, store, storeK, storeP, _, _, _) = result
          val _ = ST.Counter.tick new_config_counter
          (*
          val _ = DebugSS.run (fn say => say ["new config: ", Config.toString xi, "\n"])
          *)
          fun doTrans () = T.trans (pinfo, add_a xi, add_a xi, add_aP xi, utilAddrs, 
                                    xi, store, storeK, storeP)
          val trans = doTrans ()
          val (result, trans) = handle_passed_to_unknown (xi, result, trans)
      in (fn () => update (xi, wl, result, trans)) () end

      fun lp (wl, result) = 
          if Config.Set.isEmpty wl
          then result
          else let
              val xi = Config.Set.minItem wl
              val wl = Config.Set.subtract (wl, xi)
          in lp (handle_wl (xi, wl, result)) end
      val wl = r0
      val result = lp (wl, (r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0))
  in result end

  fun stateSpaceMath2 (pinfo, utilAddrs, cu) = let
      val (r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0) = initialStateSpace (pinfo, cu)
      val state_space = fixpointMath2 (pinfo, utilAddrs, r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0)
      val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = state_space
  in {configs=configs,
      store=store,
      storeK=storeK, 
      storeP=storeP,
      graph=graph, 
      util_addrs=utilAddrs,
      ldata_passed_to_unknown=ldata_passed_to_unknown,
      cdata_passed_to_unknown=cdata_passed_to_unknown}
  end

  (* The idea behind the state space algorithm is that we track 
     and propagate changes, until we hit a fixpoint.
     To do this we track three worklists, which contain 
     - new configurations to be transitioned
     - configuration, address, value triples which represent 
       address updates to be propagated to a configuration.
       This is represented as a map.
     - Configuration, proxy address, index list, proxy value
       quadruples which represent proxy address updates to be
       propagated to a configuration.
       This is represented as a map.
     In order to track which configurations need to be updated when a
     change to an address is detected, we use functions add_a_primary,
     add_a_secondary, and add_aP.  When making a transition for the
     configuration xi, we apply add_a_parimary, add_a_secondary, and
     add_aP to xi, and hand the results off to the transition
     function. Then, in the transition function when a load from an
     address or proxy address (with a list of indices) occurs, the
     respective add function is applied, which adds the current
     configuration to that address's or proxy address's update set.
     The primary / secondary distinction is when there is more than
     one possible "type" of load.  For example, when updating a
     function call, if the function position is updated, the new
     closures can spawn new configurations, whereas if an argument is
     updated, then the update just needs to be propagated to existing
     known calls. 
     Specialized propagation functions are used to minimize the amount
     of bindings, configurations, etc. that are known to not provide
     any new information (or any information that won't be produced by
     other worklist elements).

     TODO: I would like to use hash tables for these since insertion /
     deletion is probably a bit faster, but there is no "get an
     arbitrary element" function available. *)
  fun fixpoint (pinfo, utilAddrs, r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0) = let
      val addr_primary_tbl = AT.mkTable (100, Fail "addr_primary_tbl")
      val addr_secondary_tbl = AT.mkTable (100, Fail "addr_secondary_tbl")
      val addrP_tbl = APT.mkTable (100, Fail "addrP_tbl")
      fun add_a_primary xi a =
          case AT.find addr_primary_tbl a
           of NONE => let
               val set = Config.MSet.mkEmpty 10
           in AT.insert addr_primary_tbl (a, set);
              Config.MSet.add (set, xi);
              ()
           end
            | SOME set => (Config.MSet.add (set, xi); ())
      fun add_a_secondary xi a =
          case AT.find addr_secondary_tbl a
           of NONE => let
               val set = Config.MSet.mkEmpty 10
           in AT.insert addr_secondary_tbl (a, set);
              Config.MSet.add (set, xi);
              ()
           end
            | SOME set => (Config.MSet.add (set, xi); ())
      fun add_aP xi (aP, lst) =
          case APT.find addrP_tbl aP
           of NONE => let
               val set = Config_Indices.MSet.mkEmpty 10
           in APT.insert addrP_tbl (aP, set);
              Config_Indices.MSet.add (set, (xi, lst));
              ()
           end
            | SOME set => (Config_Indices.MSet.add (set, (xi, lst)); ())

      fun handle_passed_to_unknown (xi, result, transResult) = let
          val (next_configs, store_exts, storeK_exts, storeP_exts, ds_passed_to_unknown, dKs_passed_to_unknown) = transResult
          val trans = (next_configs, store_exts, storeK_exts, storeP_exts)
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = result
          fun do_unknown () =
              T.passed_to_unknown (pinfo, add_a_primary xi, add_a_secondary xi, add_aP xi, ds_passed_to_unknown, dKs_passed_to_unknown,
                                         store, storeK, storeP, ldata_passed_to_unknown, cdata_passed_to_unknown,
                                         trans)
          val (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown) =
          (* doTimer timerUnknown do_unknown *)
              do_unknown ()
          val result = (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) 
          val trans = (next_configs, store_exts, storeK_exts, storeP_exts) 
      in (result, trans) end

      (* Update the worklists with a transition result. *)
      fun update (wl_update_a, wl_update_aP, wl, result, transResult) = let
          val (next_configs, store_exts, storeK_exts, storeP_exts) = transResult
          val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = result

          (* TODO:GRAPH *)
          (* 
          val graph = ensureVertexExists (xi, graph)
          fun update_graph () = let
              val graph = List.foldl ensureVertexExists graph next_configs
              val graph = List.foldl (addEdge xi) graph next_configs
          in graph end
          val graph = doTimer timerUpdateGraph update_graph 
          *)
                                    
          (* add any new configurations to the seen set and the work list. *)
          fun update_configs () = let
              fun handle_config (xi, (configs, wl)) =
                  if Config.Set.member (configs, xi)
                  then (configs, wl)
                  else (Config.Set.add (configs, xi), xi :: wl)
              val (configs, wl) = List.foldl handle_config (configs, wl) next_configs
          in (configs, wl) end
          (* val (configs, wl) = doTimer timerUpdateConfigs update_configs *)
          val (configs, wl) = update_configs ()

          (* add new storeK bindings to the tracked storeK *)
          fun update_storeK () = let
              fun storeK_join ((aK, dK), storeK) =
                  StoreK.extend (storeK, aK, dK) 
              val storeK = List.foldl storeK_join storeK storeK_exts
          in storeK end
          (* val storeK = doTimer timerUpdateStoreK update_storeK *)
          val storeK = update_storeK ()

          (* Add new store bindings to the tracked store. If the new
             store bindings would not add anything, then ignore
             them. Otherwise, add them to the store and add the
             address to the address worklist, joining with any
             previous entry in the worklist. Additionally, we ensure
             that the addr tables are defined on all addresses in the
             store. FIXME: not currently true for initial bindings. *)
          fun update_with_a_d ((a, d), (wl_update_a, store)) = let
              fun extend d = let
                  fun extend_store () = Store.extend (store, a, d)
                  val _ = ST.Counter.tick tmp_counter
              in (* doTimer timerUpdateStore extend_store *)
                  extend_store ()
              end
              (*
              val _ = DebugSS.run (fn say => say ["attempting to update ", Addr.toString a, " with ", Value.toString d, "\n"])
              *)
          in
              case Store.find (store, a)
               of SOME d' => let
                   (*
                   val _ = DebugSS.run (fn say => say ["with diff ", " \\ ", Value.toString d', "\n"])
                   *)
                   fun value_diff () =
                       Value.difference (d, d')
                   val d = (* doTimer timerAddUpdate_a_diff value_diff *)
                       value_diff ()
                       
               in if Value.isEmpty d
                  then (wl_update_a, store)
                  else let
                      (*
                      val _ = DebugSS.run (fn say => say ["extending", Addr.toString a, " with ", Value.toString d, "\n"])
                      *)
                      fun update_wl_update_a () =
                          case Addr.Map.find (wl_update_a, a)
                           of SOME d' => Addr.Map.insert (wl_update_a, a, Value.join (d', d))
                            | NONE => Addr.Map.insert (wl_update_a, a, Value.copy d)
                      (* val wl_update_a = doTimer timerAddUpdate_a_wljoin update_wl_update_a *)
                      val wl_update_a = update_wl_update_a ()
   
                      val store = extend d
                  in (wl_update_a, store) end
               end
                | NONE => (AT.insert addr_primary_tbl (a, Config.MSet.mkEmpty 10);
                           AT.insert addr_secondary_tbl (a, Config.MSet.mkEmpty 10);
                           (wl_update_a, extend (Value.copy d)))
          end
          fun update_store () = let
              val res = (wl_update_a, store)
              val res = List.foldl update_with_a_d res store_exts
          in res end
          (* val (wl_update_a, store) = doTimer timerAddUpdate_a update_store *)
          val (wl_update_a, store) = update_store ()

          (* Add new storeP bindings to the tracked storeP. If the new
             storeP bindings would not add anything, then ignore
             them. Otherwise, add them to the storeP and add the
             address to the proxy address worklist, joining with any
             previous entry in the worklist. Additionally, we ensure
             that the addr tables are defined on all addresses in the
             store. FIXME: not currently true for the initial binding. *)
          fun update_with_aP_dP ((aP, dP), (wl_update_aP, storeP)) = let
              fun extendP dP = let
                  fun extend_storeP () = StoreProxy.extend (storeP, aP, dP)
              in (* doTimer timerUpdateStoreP extend_storeP *)
                  extend_storeP ()
              end
          in
              case StoreProxy.find (storeP, aP)
               of SOME dP' => let 
                   val dP = ValueProxy.difference (dP, dP')
               in
                   if ValueProxy.isEmpty dP
                   then (wl_update_aP, storeP)
                   else let
                       val wl_update_aP =
                           case AddrProxy.Map.find (wl_update_aP, aP)
                            of SOME dP' => AddrProxy.Map.insert (wl_update_aP, aP, ValueProxy.join (dP', dP))
                             | NONE => AddrProxy.Map.insert (wl_update_aP, aP, dP)
                       val storeP = extendP dP
                   in (wl_update_aP, storeP) end
               end
                | NONE => (APT.insert addrP_tbl (aP, Config_Indices.MSet.mkEmpty 10);
                           (wl_update_aP, extendP dP))
          end
          fun update_storeP () = let
              val res = (wl_update_aP, storeP)
              val res = List.foldl update_with_aP_dP res storeP_exts
          in res end
          (* val (wl_update_aP, storeP) = doTimer timerAddUpdate_aP update_storeP *)
          val (wl_update_aP, storeP) = update_storeP ()

          val result = (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown)
      in (wl_update_a, wl_update_aP, wl, result) end

      (* Handle one element from the wl_update_a worklist, doing primary changes. *)
      fun handle_wl_update_a_primary ((xi, update_a, update_d), (wl_update_a, wl_update_aP, wl, result)) = let
          val (_, store, storeK, storeP, _, _, _) = result
          val _ = ST.Counter.tick update_addr_counter
          (*
          val _ = DebugSS.run (fn say => say ["Update addr: ", Config.toString xi,
                                            " with ", Addr.toString update_a,
                                            " -> ", Value.toString update_d, "\n"])
          *)
          fun doTrans () = T.transUpdate_a_primary (pinfo, add_a_primary xi, add_a_secondary xi, add_aP xi, utilAddrs, 
                                                    xi, store, storeK, storeP, update_a, update_d)
          (* val trans = doTimer timerTrans doTrans *)
          val trans = doTrans ()
          val (result, trans) = handle_passed_to_unknown (xi, result, trans)
          fun do_update () = update (wl_update_a, wl_update_aP, wl, result, trans)
      in (* doTimer timerUpdate do_update *)
          do_update ()
      end

      (* Handle one element from the wl_update_a worklist, doing secondary changes. *)
      fun handle_wl_update_a_secondary ((xi, update_a, update_d), (wl_update_a, wl_update_aP, wl, result)) = let
          val (_, store, storeK, storeP, _, _, _) = result
          val _ = ST.Counter.tick update_addr_counter
          (*
          val _ = DebugSS.run (fn say => say ["Update addr2: ", Config.toString xi,
                                            " with ", Addr.toString update_a,
                                            " -> ", Value.toString update_d, "\n"])
          *)
          fun doTrans () = T.transUpdate_a_secondary (pinfo, add_a_primary xi, add_a_secondary xi, add_aP xi, utilAddrs, 
                                                      xi, store, storeK, storeP, update_a, update_d)
          (* val trans = doTimer timerTrans doTrans *)
          val trans = doTrans ()
          val (result, trans) = handle_passed_to_unknown (xi, result, trans)
          fun do_update () = update (wl_update_a, wl_update_aP, wl, result, trans)
      in (* doTimer timerUpdate do_update *)
          do_update ()
      end

      (* Handle one element from the wl_update_aP worklist. *)
      fun handle_wl_update_aP ((xi, update_aP, update_lst, update_dP), (wl_update_a, wl_update_aP, wl, result)) = let
          val (_, store, storeK, storeP, _, _, _) = result
          val _ = ST.Counter.tick update_addrP_counter
          (*
          val _ = DebugSS.run (fn say => say ["Update addrP: ", Config.toString xi,
                                            " with ", AddrProxy.toString update_aP,
                                            " -> ", ValueProxy.toString update_dP, "\n"])
          *)
          fun doTrans () = T.transUpdate_aP (pinfo, add_a_primary xi, add_a_secondary xi, add_aP xi, utilAddrs, 
                                             xi, store, storeK, storeP, update_aP, update_lst, update_dP)
          (* val trans = doTimer timerTrans doTrans *)
          val trans = doTrans ()
          val (result, trans) = handle_passed_to_unknown (xi, result, trans)
          fun do_update () = update (wl_update_a, wl_update_aP, wl, result, trans)
      in (* doTimer timerUpdate do_update *)
          do_update ()
      end

      (* Handle one element from the wl worklist. *)
      fun handle_wl (xi, wl_update_a, wl_update_aP, wl, result) = let
          val (_, store, storeK, storeP, _, _, _) = result
          val _ = ST.Counter.tick new_config_counter
          (*
          val _ = DebugSS.run (fn say => say ["new config: ", Config.toString xi, "\n"])
          *)
          fun doTrans () = T.trans (pinfo, add_a_primary xi, add_a_secondary xi, add_aP xi, utilAddrs, 
                                    xi, store, storeK, storeP)
          (* val trans = doTimer timerTrans doTrans *)
          val trans = doTrans ()
          val (result, trans) = handle_passed_to_unknown (xi, result, trans)
          fun do_update () = update (wl_update_a, wl_update_aP, wl, result, trans)
      in (* doTimer timerUpdate do_update *)
          do_update ()
      end

      fun lp (wl_update_a, wl_update_aP, wl, result) = let
          (* Try to use the proxy address worklist. *)
          fun do_aP next =
              (case AddrProxy.Map.firsti wl_update_aP
                of SOME (aP, dP) => let
                    val xi_indices = AddrProxy.Tbl.lookup addrP_tbl aP
                    val (wl_update_aP, _) = AddrProxy.Map.remove (wl_update_aP, aP)
                in lp (Config_Indices.MSet.fold (fn ((xi, indices), res) => handle_wl_update_aP ((xi, aP, indices, dP), res))
                                                (wl_update_a, wl_update_aP, wl, result) xi_indices) end
                 | NONE => next ())
          (* Try to use the address worklist. *)
          fun do_a next = 
              (case Addr.Map.firsti wl_update_a
                of SOME (a, d) => let
                    val xis_primary = AT.lookup addr_primary_tbl a
                    val xis_secondary = AT.lookup addr_secondary_tbl a
                    val (wl_update_a, _) = Addr.Map.remove (wl_update_a, a)
                    val next = (wl_update_a, wl_update_aP, wl, result)
                    val next = Config.MSet.fold (fn (xi, res) => handle_wl_update_a_secondary ((xi, a, d), res)) next xis_secondary
                    val next = Config.MSet.fold (fn (xi, res) => handle_wl_update_a_primary ((xi, a, d), res)) next xis_primary
                in lp next end
                 | NONE => next ())
          (* Try to use the configuration worklist. *)
          fun do_xi next =
              (case wl
                of xi :: wl => lp (handle_wl (xi, wl_update_a, wl_update_aP, wl, result))
                 | [] => next ())
          (* Finished *)
          fun done () =
              result
      (* It seems that this order is the best. the AddrProxy versus
         Addr worklists can be swapped around, but the configuration
         worklist should always go last. This is because handling the
         joins of Values / ProxyValues earlier is propagated to any
         new configurations. *)
      in do_aP (fn () => do_a (fn () => do_xi done)) end
      (* in do_a (fn () => do_aP (fn () => do_xi done)) end *)

      val wl = Config.Set.listItems r0
      val result = (Config.Set.empty, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0)
      val trans = (Config.Set.listItems r0, [], [], [])
      val wl_update_a = Addr.Map.empty
      val wl_update_aP = AddrProxy.Map.empty
      val wl = []
      fun do_update () = update (wl_update_a, wl_update_aP, wl, result, trans)
      (* val result = lp (doTimer timerUpdate do_update) *)
      val result = lp (do_update ()) 
      val _ = ST.Counter.bump (
              total_counter,
              ST.Counter.value update_addr_counter
              + ST.Counter.value update_addrP_counter
              + ST.Counter.value new_config_counter)
      val _ = ST.Counter.bump (states_counter, Config.Set.numItems (#1 result))
  in result end

  fun stateSpace (pinfo, utilAddrs, cu) = let
      val (r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0) = initialStateSpace (pinfo, cu)
      val state_space = fixpoint (pinfo, utilAddrs, r0, store0, storeK0, storeP0, graph0, ldata_passed_to_unknown0, cdata_passed_to_unknown0)
      val (configs, store, storeK, storeP, graph, ldata_passed_to_unknown, cdata_passed_to_unknown) = state_space
  in {configs=configs,
      store=store,
      storeK=storeK, 
      storeP=storeP,
      graph=graph, 
      util_addrs=utilAddrs,
      ldata_passed_to_unknown=ldata_passed_to_unknown,
      cdata_passed_to_unknown=cdata_passed_to_unknown}
  end

end
