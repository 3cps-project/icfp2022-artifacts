(* analysis.sml
 *
 * The analysis which improves (determines) the extent oracle among other information.
 *)

structure ExtentAnalysis : sig

  (* the information collected by the analysis *)
    datatype t = Info of {
        ainfo : AnalysisInformation.t, (* analysis information *)
        ainfoSyntax : AnalysisInformation.t, (* analysis information (from syntactic analyses) *)
        pinfo : CPSInformation.t, (* Program information *)
        utilAddrs : Transition.util_addrs,
        stateSp : StateSpace.t
      }

    val analyze : CPS.comp_unit -> t

    val check : CPS.comp_unit * t -> unit
                                         
    val getPromotionResults : unit -> {lvar : PromotionDump.t, ldata : PromotionDump.t}

  end = struct

    structure C = CPS
    structure PInfo = CPSInformation
    structure AInfo = AnalysisInformation

    val lvarPromotionResults = ref PromotionDump.empty
    val ldataPromotionResults = ref PromotionDump.empty
    fun getPromotionResults () = {lvar = !lvarPromotionResults, ldata = !ldataPromotionResults}

    datatype t = Info of {
        ainfo : AInfo.t,
        ainfoSyntax : AInfo.t,
        pinfo : PInfo.t,
        utilAddrs : Transition.util_addrs,
        stateSp : StateSpace.t
      }

  (* set the internal extent content of lvars and cvars to that
   * given by the analysis information
   *)
    fun updateVarExtents ainfo = (
          LVar.Map.appi
            (fn (x, extent) => ExtentSet.setAndJoinLVarExtent(x, extent))
            (AInfo.lvarExtents ainfo)
  (*;
        CVar.Map.appi
            (fn (k, extent) => ExtentSet.setAndJoinCVarExtent(k, extent))
            (AInfo.cvarExtents ainfo) *))

  (* creates a map from each instance of creating a side effecty
   * data structure to an address useable during analysis
   *)
    (* TODO: want to use the types at state-space time *)
    fun create_sideEffectVars (C.CU(_, lam_lab0, _, _, e), pinfo) = let
        fun f (l, map) = let
            val x = LVar.newTmp ("_ref", CPSTypes.TyScheme ([], CPSTypes.TupleTy []), Extent.HEAP)
        in Label.Map.insert (map, l, x) end
    in List.foldl f Label.Map.empty (PInfo.side_effect_labels pinfo) end

    fun create_tyAddrs (C.CU(_, lam_lab0, _, _, e)) = let
        val tenv = TEnv.empty
        val aP = TransitionUtil.allocP (lam_lab0, tenv, e, tenv)
        fun new name = LVar.newTmp (name, CPSTypes.TyScheme ([], CPSTypes.TupleTy []), Extent.HEAP)
        val a_unit = TransitionUtil.alloc (new "_unit", tenv, aP)
        val a_int = TransitionUtil.alloc (new "_int", tenv, aP)
        val a_real = TransitionUtil.alloc (new "_real", tenv, aP)
        val a_char = TransitionUtil.alloc (new "_char", tenv, aP)
        val a_string = TransitionUtil.alloc (new "_string", tenv, aP)
        val a_word = TransitionUtil.alloc (new "_word", tenv, aP)
    in {a_unit=a_unit, a_int=a_int, a_real=a_real,
        a_char=a_char, a_string=a_string, a_word=a_word}
    end

    fun create_utilAddrs (cu, pinfo) = let
        val sideEffectVars = create_sideEffectVars (cu, pinfo)
        val tyAddrs = create_tyAddrs cu
    in {sideEffectVars=sideEffectVars, tyAddrs=tyAddrs} end



  (* Runs the various information determining procedures to produce analysis information *)
    fun determine (pinfo, utilAddrs, cu, stateSpace, ainfo) = let
          val _ = DebugAnalysisResults.say ["start abstract gc\n"]
          fun doAbstractGC () = Live.make (pinfo, stateSpace)
          val liveMemo = PhaseTimer.withTimer
                             Timers.timeExtAnalysisAbstractGC
                             doAbstractGC ()
          val _ = DebugAnalysisResults.say ["end abstract gc\n"]

          val analysis_space = {
              utilAddrs=utilAddrs,
              pinfo=pinfo,
              cu=cu,
              liveMemo=liveMemo,
              state_space=stateSpace
          }

          fun doPhase (ainfo, name, determiner, timer) = let
              val _ = DebugAnalysisResults.say ["start determine " ^ name ^ "\n"]
              val ainfo = PhaseTimer.withTimer timer determiner ainfo
              val _ = DebugAnalysisResults.say ["end determine " ^ name ^ "\n"]
          in ainfo end

          fun determineExtentCrit ainfo =
              DetermineExtentCriteria.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "extent criteria",
                               determineExtentCrit,
                               Timers.timeExtAnalysisDetermineExt)

          fun determineUniqCrit ainfo =
                DetermineUniquenessCriteria.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "uniqueness criteria",
                               determineUniqCrit,
                               Timers.timeExtAnalysisDetermineUniq)

          fun determineFunFlow ainfo =
                DetermineFunFlow.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "function flow",
                               determineFunFlow,
                               Timers.timeExtAnalysisDetermineFunFlow)

          fun determineTupleFlow ainfo =
                DetermineTupleFlow.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "tuple flow",
                               determineTupleFlow,
                               Timers.timeExtAnalysisDetermineTupleFlow)

          fun determineDataFlow ainfo =
                DetermineDataFlow.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "data flow",
                               determineDataFlow,
                               Timers.timeExtAnalysisDetermineDataFlow)

          fun determineCallWebs ainfo =
                DetermineCallWebs.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "call webs",
                               determineCallWebs,
                               Timers.timeExtAnalysisDetermineCallWebs)

          fun determineUnknownFlow ainfo =
                DetermineUnknownFlow.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "unknown flow",
                               determineUnknownFlow,
                               Timers.timeExtAnalysisDetermineUnknownFlow)

(*
          fun determineRelativePop ainfo =
                DetermineRelativePop.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "relative pop",
                               determineRelativePop,
                               Timers.timeExtAnalysisDetermineRelativePop)

          fun determineContinuationOrder ainfo =
                DetermineContinuationOrder.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "continuation order",
                               determineContinuationOrder,
                               Timers.timeExtAnalysisDetermineContinuationOrder)
*)

    (*
          fun determineDisplayPass ainfo =
                DetermineDisplayPass.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "display pass",
                               determineDisplayPass,
                               Timers.timeExtAnalysisDetermineDisplay)

    *)

                              (*
          fun determineEnvMatch ainfo =
                DetermineEnvironmentMatch.determine (analysis_space, ainfo)
          val ainfo = doPhase (ainfo, "environment match",
                               determineEnvMatch,
                               Timers.timeExtAnalysisDetermineEnvMatch)
*)

          in ainfo end (* determine *)

    fun ainfo_syntax pinfo cu = let
        val ainfo = AInfo.info pinfo cu
        fun add_lvar (x, acc) = LVar.Map.insert(acc, x, ExtentSet.extentOfLVar x)
        val lvarExtents = List.foldl add_lvar LVar.Map.empty (PInfo.lvars pinfo)
        val ainfo = AInfo.with_lvarExtents (ainfo, lvarExtents)
        val {user=callWebs, cont=callWebsK} = DetermineSyntacticCallWebs.callWebs (cu, {add_unknown=true})
        val ainfo = AInfo.with_callWebs (ainfo, callWebs)
        val ainfo = AInfo.with_callWebsK (ainfo, callWebsK)
    in ainfo end


  (* analyzes the CPS.
   * Determines and sets extent information for the lvars and cvars of
   * the program.
   *)
    fun analyze cu = let
        val () = SyntacticExtentAnalysis.analyze cu
        fun getPInfo () = PInfo.info cu
        val pinfo = PhaseTimer.withTimer Timers.timePInfo getPInfo ()

        val () = PhaseTimer.start Timers.timeExtAnalysis
        (*
        fun printTy x =
            Debug.say ["[", LVar.toString x,
                       "  \t:\t", CPSTypeUtil.tySchemeToString (LVar.typeOf x), "]", "\n"]
        fun printCTy k =
            Debug.say ["[", CVar.toString k,
                       "  \t:\t", CPSTypeUtil.ctyToString (CVar.typeOf k), "]", "\n"]

          val _ = List.app printTy (PInfo.lvars pinfo)
          val _ = List.app printCTy (PInfo.cvars pinfo)
        *)
        (* the type checker needs to be revised to handle the new primops, but this change
         * will also require the unification of the word, int, and char types into
         * a single CPS type. [JHR; 2021-02-16]
         *)
        (* val _ = CPSTypeChecker.check cu *)
        val () = CPSInvariants.check (cu, pinfo)
        val ainfo = AInfo.info pinfo cu
        val utilAddrs = create_utilAddrs (cu, pinfo)
        val () = Verbose.say ["\n  Generating State Space ... "]
        fun getStateSpace () = StateSpace.stateSpace (pinfo, utilAddrs, cu)
        val stateSpace = PhaseTimer.withTimer
                             Timers.timeExtAnalysisStateSpace
                             getStateSpace ()
        val () = Verbose.say ["done"]

        val () = DebugAnalysisStateSpace.run (fn say => say ["state space done\n"])

        val () = Verbose.say ["\n  Determining Information ... "]
        fun doDetermine () =
            determine (pinfo, utilAddrs, cu, stateSpace, ainfo)
        val ainfo = PhaseTimer.withTimer
                        Timers.timeExtAnalysisDetermine
                        doDetermine ()
        val ainfo = AnalysisInformationUtil.computeExtentMaps (cu, pinfo, ainfo)
        val () = PhaseTimer.stop Timers.timeExtAnalysis
        val ainfoSyntax = ainfo_syntax pinfo cu
        val () = DumpAnalysis.dumpExtents (pinfo, ainfoSyntax, ainfo)
        val () = DumpAnalysis.dumpExtentSummary (pinfo, ainfoSyntax, ainfo)
        val () = DumpAnalysis.dumpStateSpace ("Analysis state-space", stateSpace)
        val () = DumpAnalysis.dumpAnalysisSummary (pinfo, stateSpace)
        val () = lvarPromotionResults :=
                 (PromotionDump.get (PInfo.lvars pinfo,
                                     fn x => LVar.Map.lookup (#lvarExtents ainfoSyntax, x),
                                     fn x => LVar.Map.lookup (#lvarExtents ainfo, x),
                                     fn x => 1))
        val () = ldataPromotionResults :=
                 (PromotionDump.get (PInfo.ldata pinfo,
                                     fn x => Label.Map.lookup (#ldataExtents ainfoSyntax, x),
                                     fn x => Label.Map.lookup (#ldataExtents ainfo, x),
                                     fn x => 1))
    in
        Info{
            ainfo = ainfo, ainfoSyntax = ainfoSyntax,
            pinfo = pinfo, utilAddrs = utilAddrs,
            stateSp = stateSpace
        }
    end

    fun check (cu, Info{ainfo, ainfoSyntax, pinfo, utilAddrs, stateSp}) = (
          (* updateVarExtents ainfo; *)
        CheckAnalysis.check (pinfo, utilAddrs, cu, stateSp, ainfo, ainfoSyntax)
    )

  end
