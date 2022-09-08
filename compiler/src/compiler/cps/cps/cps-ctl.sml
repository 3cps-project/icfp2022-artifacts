(* cps-ctl.sml
 *
 * NOTE: it is not clear that a functor is the best way to
 * provide this mechanism, since there are no type or structure
 * dependencies involved.
 *
 * Also, the functor definition should be in the compiler/common directory.
 *)

functor ControlWrapper (

    val c : bool Controls.control
    val prefix_opt : string option

  ) : sig

  (* Print some messages to the log if c is active, with the prefix, if it exists *)
    val say : string list -> unit

  (* Provide a function that takes say and returns unit, and run it only if c is active *)
    val run : ((string list -> unit) -> unit) -> unit

  end = struct

    fun say msgs = if Controls.get c
          then (case prefix_opt
             of SOME prefix => Log.msg(prefix :: " " :: msgs)
             | NONE => Log.msg msgs)
          else ()

    fun run f =  if Controls.get c
          then f say
          else ()

  end

structure DumpCPSInformation = ControlWrapper (
    val c = Ctl.dumpCPSInformation
    val prefix_opt = SOME "[Dump CPS Info]")

structure DumpExtents = ControlWrapper (
    val c = Ctl.dumpExtents
    val prefix_opt = SOME "[Extents]")

structure DumpExtentSummary = ControlWrapper (
    val c = Ctl.dumpExtentSummary
    val prefix_opt = SOME "[Extent Summary]")

structure DumpInterpreterSummary = ControlWrapper (
    val c = Ctl.dumpInterpreterSummary
    val prefix_opt = SOME "[Alloc  Summary]")

structure DumpAllocationSummary = ControlWrapper (
    val c = Ctl.dumpAllocationSummary
    val prefix_opt = SOME "[Alloc  Summary]")

structure DumpAnalysisStateSpace = ControlWrapper (
    val c = Ctl.dumpAnalysisStateSpace
    val prefix_opt = SOME "[Dump Analysis State Space]")

structure DumpAnalysisSummary = ControlWrapper (
    val c = Ctl.dumpAnalysisSummary
    val prefix_opt = SOME "[Dump Analysis Summary]")

structure DumpOptimizationSummary = ControlWrapper (
    val c = Ctl.dumpOptimizationSummary
    val prefix_opt = SOME "[Dump Optimization Summary]")

structure DumpInterpreterSummary = ControlWrapper (
    val c = Ctl.dumpInterpreterSummary
    val prefix_opt = SOME "[Dump Interpreter]")

structure DebugAnalysisStateSpace = ControlWrapper (
    val c = Ctl.debugAnalysisStateSpace
    val prefix_opt = SOME "[Debug Analysis State Space]")

structure DebugAnalysisResults = ControlWrapper (
    val c = Ctl.debugAnalysisResults
    val prefix_opt = SOME "[Debug Analysis Results]")

structure CheckAnalysisStateSpace = ControlWrapper (
    val c = Ctl.checkAnalysisStateSpace
    val prefix_opt = SOME "[Check Analysis State Space]")

structure CheckAnalysisResults = ControlWrapper (
    val c = Ctl.checkAnalysisResults
    val prefix_opt = SOME "[Check Analysis Results]")

structure CheckCPS = ControlWrapper (
    val c = Ctl.checkCPS
    val prefix_opt = SOME "[Check CPS]")


(* BQ: for when I need some temporary misc debugging and don't want to
   use one of the other stuctures, since they enable other printing *)
structure Debug = ControlWrapper (
    val c = Controls.genControl {
            name = "debug",
            pri = [1, 1],
            obscurity = 1,
            help = "debug",
            default = true
        }
    val prefix_opt = SOME "[DEBUG]")


structure Verbose =
  struct

  (* messages in verbose mode *)
    fun say msgs = if Controls.get Ctl.verbose
          then TextIO.output(TextIO.stdErr, concat msgs)
          else ()

  end
