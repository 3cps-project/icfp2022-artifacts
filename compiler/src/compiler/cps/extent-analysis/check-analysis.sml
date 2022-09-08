(* check-analysis.sml
 *
 * checks the various components of the analysis for correctness
 *)

structure CheckAnalysis : sig

  (* val checkAnalysisStateSpace : CPSInformation.t * (Addr.t Label.Map.map) * CPS.comp_unit * StateSpace.t -> unit *)
  (* val checkAnalysiss : CPSInformation.t * CPS.comp_unit * AnalysisInformation.t * AnalysisInformation.t -> unit *)

  val check : CPSInformation.t * Transition.util_addrs * CPS.comp_unit * StateSpace.t * AnalysisInformation.t * AnalysisInformation.t -> unit

end = struct

  structure PInfo = CPSInformation

  val good = {fg=SOME ANSIText.green, bg=NONE, bf=true, ul=false}
  val bad = {fg=SOME ANSIText.red, bg=NONE, bf=true, ul=false}

  (* checks the given state space against a "mathematically precise"
     state space calculation if Ctl.checkAnalysisStateSpace is
     enabled. Reports whether the components are the same and if not,
     what the differences are. *)
  fun checkAnalysisStateSpace (pinfo, utilAddrs, cu, state_space : StateSpace.t) = let
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space
      val ldata_passed_to_unknown = #ldata_passed_to_unknown state_space
      val graph = #graph state_space
  in
      PhaseTimer.withTimer Timers.timeExtAnalysisStateSpaceCheck
      CheckAnalysisStateSpace.run
          (fn say => let
               (* the "mathematically precise" state space *)
               val _ = Verbose.say ["  Generating State Space ... "]
               val state_space' = StateSpace.stateSpaceMath (pinfo, utilAddrs, cu)
               val _ = Verbose.say ["done\n"]
               val configs' = #configs state_space'
               val store' = #store state_space'
               val storeK' = #storeK state_space'
               val storeP' = #storeP state_space'
               val ldata_passed_to_unknown' = #ldata_passed_to_unknown state_space'
               val graph' = #graph state_space'
               val _ = DumpAnalysis.dumpStateSpace ("True state-space", state_space')
               fun same ord = case ord of EQUAL => ANSIText.fmt (good, "correct") | _ => ANSIText.fmt (bad, "incorrect")
               fun same_bool b = if b then ANSIText.fmt (good, "correct") else ANSIText.fmt (bad, "incorrect")

               (* differences between the produced configurations *)
               val missing_configs = Config.Set.listItems (Config.Set.difference (configs', configs))
               val extra_configs = Config.Set.listItems (Config.Set.difference (configs, configs'))

               (* differences between the stores *)
               fun addr_diff store (a, d, acc) = case Store.find (store, a) of SOME _ => acc | NONE => a :: acc
               val missing_addrs = Store.foldi (addr_diff store) [] store'
               val extra_addrs = Store.foldi (addr_diff store') [] store
               fun add_addr_value (a, d, acc) = if Value.isEmpty d then acc else (a, d) :: acc
               fun value_diff store (a, d, acc) = case Store.find (store, a) of SOME d' => add_addr_value (a, Value.difference (d, d'), acc) | NONE => acc
               val missing_values = Store.foldi (value_diff store) [] store'
               val extra_values = Store.foldi (value_diff store') [] store

               (* differences between the continuation stores *)
               fun addrK_diff storeK (aK, dK, acc) = case StoreK.find (storeK, aK) of SOME _ => acc | NONE => aK :: acc
               val missing_addrKs = StoreK.foldi (addrK_diff storeK) [] storeK'
               val extra_addrKs = StoreK.foldi (addrK_diff storeK') [] storeK
               fun add_addrK_cloK (aK, cloKs, acc) = if CloK.Set.isEmpty cloKs then acc else (aK, cloKs) :: acc
               fun valueKs_diff storeK (aK, dK, acc) =
                   case StoreK.find (storeK, aK) 
                    of SOME dK' => 
                       (case (dK, dK')
                         of (ValueK.CLOK cloKs, ValueK.CLOK cloKs') => 
                            add_addrK_cloK (aK, CloK.Set.difference (cloKs, cloKs'), acc)
                          | (ValueK.INDEX index1, ValueK.INDEX index2) => 
                            if index1 = index2
                            then acc
                            else raise Fail "check analysis impossible"
                          | _ => raise Fail "check analysis impossible")
                     | NONE => acc
               val missing_cloKs = StoreK.foldi (valueKs_diff storeK) [] storeK'
               val extra_cloKs = StoreK.foldi (valueKs_diff storeK') [] storeK 

               (* differences between the proxy stores *)
               fun addrP_diff storeP (aP, dP, acc) = case StoreProxy.find (storeP, aP) of SOME _ => acc | NONE => aP :: acc
               val missing_addrPs = StoreProxy.foldi (addrP_diff storeP) [] storeP'
               val extra_addrPs = StoreProxy.foldi (addrP_diff storeP') [] storeP
               fun add_addrP_valueP (aP, dP, acc) = if ValueProxy.isEmpty dP then acc else (aP, dP) :: acc
               fun valueP_diff storeP (aP, dP, acc) = case StoreProxy.find (storeP, aP) of SOME dP' => add_addrP_valueP (aP, ValueProxy.difference (dP, dP'), acc) | NONE => acc
               val missing_valuePs = StoreProxy.foldi (valueP_diff storeP) [] storeP'
               val extra_valuePs = StoreProxy.foldi (valueP_diff storeP') [] storeP

               (* differences between the graphs *)
               fun vert_diff graph (xi, _, acc) = case Config.Map.find (graph, xi) of SOME _ => acc | NONE => xi :: acc
               val missing_vertices = Config.Map.foldli (vert_diff graph) [] graph'
               val extra_vertices = Config.Map.foldli (vert_diff graph') [] graph
               fun add_edge_diff (xi, xis, acc) = Config.Set.foldl (fn (xi', acc) => (xi, xi') :: acc) acc xis
               fun edge_diff graph (xi, xis, acc) = case Config.Map.find (graph, xi) of SOME xis' => add_edge_diff (xi, Config.Set.difference (xis, xis'), acc) | NONE => acc
               val missing_edges = Config.Map.foldli (edge_diff graph) [] graph'
               val extra_edges = Config.Map.foldli (edge_diff graph') [] graph

               (* util print and toString *)
               fun say_same (name, x1, x2, comp) = say [name, ": ", same (comp (x1, x2)), "\n"];
               fun say_any  (name, b) = say [name, ": ", same_bool b, "\n"];
               fun say_counts (name, stuff1, stuff2, count) = say [name, ": analysis ", Int.toString (count stuff1), " math ", Int.toString (count stuff2), "\n"]
               fun say_list (name, lst : 'a list, f : 'a -> string) = if not (List.null lst) then say [name, ": ", String.concatWithMap " " f lst, "\n"] else ()
               fun addr_value_toString (a, d) = "(" ^ (Addr.toString a) ^ " " ^ (Value.toString d) ^ ")"
               fun addrK_cloKs_toString (aK, cloKs) = "(" ^ (AddrK.toString aK) ^ " " ^ (String.concatWithMap " " CloK.toString (CloK.Set.listItems cloKs)) ^ ")"
               fun addrP_valueP_toString (aP, dP) = "(" ^ (AddrProxy.toString aP) ^ " " ^ (ValueProxy.toString dP) ^ ")"
               fun edge_toString (xi, xi') = "(" ^ (Config.toString xi) ^ " " ^ (Config.toString xi') ^ ")"
           in
               say [Int.toString (Config.Set.numItems configs), "\n"];
               say [Int.toString (Config.Set.numItems configs'), "\n"];
               say ["---- State Space Check ----", "\n"];
               say_same ("configs", configs, configs', Config.Set.compare);
               (* say_counts ("num configs", configs, configs', Config.Set.numItems); *)
               say_list ("missing configs", missing_configs, Config.toString);
               say_list ("extra configs", extra_configs, Config.toString);

               say_any  ("cont store", ((List.null missing_addrs) andalso (List.null extra_addrs) andalso (List.null missing_values) andalso (List.null extra_values)));
               say_list ("extra addrs", extra_addrs, Addr.toString);
               say_list ("missing values", missing_values, addr_value_toString);
               say_list ("extra values", extra_values, addr_value_toString);

               say_any  ("cont store", ((List.null missing_addrKs) andalso (List.null extra_addrKs) (*andalso (List.null missing_valueKs) andalso (List.null extra_valueKs)*)));
               say_list ("missing addrKs", missing_addrKs, AddrK.toString);
               say_list ("extra addrKs", extra_addrKs, AddrK.toString);
               say_list ("missing cloKs", missing_cloKs, addrK_cloKs_toString);
               say_list ("extra cloKs", extra_cloKs, addrK_cloKs_toString);

               say_any  ("cont store", ((List.null missing_addrPs) andalso (List.null extra_addrPs) andalso (List.null missing_valuePs) andalso (List.null extra_valuePs)));
               say_list ("missing addrPs", missing_addrPs, AddrProxy.toString);
               say_list ("extra addrPs", extra_addrPs, AddrProxy.toString);
               say_list ("missing valuePs", missing_valuePs, addrP_valueP_toString);
               say_list ("extra valuePs", extra_valuePs, addrP_valueP_toString);

               say_same ("graph", graph, graph', Config.Map.collate Config.Set.compare);
               say_list ("missing vertices", missing_vertices, Config.toString);
               say_list ("extra vertices", extra_vertices, Config.toString);
               say_list ("missing edges", missing_edges, edge_toString);
               say_list ("extra edges", extra_edges, edge_toString);

               say_same ("ldata passed to unknown", ldata_passed_to_unknown, ldata_passed_to_unknown', Label.Set.compare);
               (* say_counts ("num ldata passed to unknown", ldata_passed_to_unknown, ldata_passed_to_unknown', Label.Set.numItems); *)
               ()
           end)
  end

  (* checks and compares the given analysis information against an
     interpreter, i.e. the ground truth if the interpreter is enabled *)
  fun checkAnalysis (pinfo, cu, ainfo_syntax, ainfo) =
      if true (*CPSInterpreter.enabled () *)
      then (Verbose.say ["  Analysis Information Check ... "];
            PhaseTimer.withTimer Timers.timeExtCheck
                                 CPSInterpreter.interpretAndCheck (pinfo, cu, ainfo_syntax, ainfo);
            Verbose.say ["done\n"])
      else ()

  (* Runs the 3CPS interpreter to check for errors *)
  fun run3CPSInterpreter (pinfo, cu, ainfo_syntax, ainfo) =
      if ThreeCPSInterpreter.enabled ()
      then (Verbose.say ["  3CPS Interpreter ... "];
            PhaseTimer.withTimer Timers.time3CPSInterpreter
                                 ThreeCPSInterpreter.interpret (pinfo, cu, ainfo_syntax, ainfo);
            Verbose.say ["done\n"])
      else ()

  (* checks the analysis state space as well as
     the information produced by the analyses. *)
  fun check (pinfo, utilAddrs, cu, state_space, ainfo, ainfo_syntax) =
      (checkAnalysisStateSpace (pinfo, utilAddrs, cu, state_space);
       checkAnalysis (pinfo, cu, ainfo_syntax, ainfo);
       run3CPSInterpreter (pinfo, cu, ainfo_syntax, ainfo);
       ())

end

