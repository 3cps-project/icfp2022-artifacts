(* timers.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Timers =
  struct

    val timeCompiler = PhaseTimer.newTimer "compiler"

  (* front-end timers *)
    val timeFront = PhaseTimer.newPhase (timeCompiler, "front end")
    val timeParser = PhaseTimer.newPhase (timeFront, "parser")
    val timeTypechecker = PhaseTimer.newPhase (timeFront, "typechecker")
    val timeMatchComp = PhaseTimer.newPhase (timeFront, "pattern-match compilation")
    val timeSimplify = PhaseTimer.newPhase (timeFront, "simplify")
    val timeSimpleOpt = PhaseTimer.newPhase (timeFront, "simple optimization")

  (* CPS timers *)
    val timeCPS  = PhaseTimer.newPhase (timeCompiler, "CPS")
    val timeConvert = PhaseTimer.newPhase (timeCPS, "CPS conversion")
    val timeSynOptimizeCPS = PhaseTimer.newPhase (timeCPS, "Syntactic CPS optimization")
    val timeAnalysis = PhaseTimer.newPhase (timeCPS, "CPS analysis")
    val timeOptimizeCPS = PhaseTimer.newPhase (timeCPS, "CPS optimization")

  (* CPS program information timers *)
    val timePInfo  = PhaseTimer.newPhase (timeAnalysis, "Program Information")

  (* Analysis timers *)
    val timeExtAnalysis =
          PhaseTimer.newPhase (timeAnalysis, "extent analysis")
    val timeExtAnalysisStateSpaceCheck =
          PhaseTimer.newPhase (timeCompiler, "extent state space check")
    val timeExtAnalysisStateSpace =
          PhaseTimer.newPhase (timeExtAnalysis, "extent state space")
    val timeExtAnalysisDetermine =
          PhaseTimer.newPhase (timeExtAnalysis, "analysis information determinations")

    val timeExtAnalysisAbstractGC =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "perform abstract gc")

    val timeExtAnalysisDetermineCallWebs =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine call webs")
    val timeExtAnalysisDetermineFunFlow =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine function flow")
    val timeExtAnalysisDetermineTupleFlow =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine tuple flow")
    val timeExtAnalysisDetermineDataFlow =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine data flow")
    val timeExtAnalysisDetermineUnknownFlow =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine unknown flow")
    val timeExtAnalysisDetermineUniq =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine uniqueness criteria")
    val timeExtAnalysisDetermineExt =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine extent criteria")
    val timeExtAnalysisDetermineDisplay =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine display pass")
    val timeExtAnalysisDetermineEnvMatch =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine environment match pass")
    val timeExtAnalysisDetermineRelativePop =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine relative pop")
    val timeExtAnalysisDetermineContinuationOrder =
          PhaseTimer.newPhase (timeExtAnalysisDetermine, "determine continuation order")

    val timeExtCheck =
          PhaseTimer.newPhase (timeCompiler, "extent check")
    val time3CPSInterpreter =
          PhaseTimer.newPhase (timeCompiler, "3CPS interpreter")



  end
