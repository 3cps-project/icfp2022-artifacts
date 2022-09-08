(* ctl.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * TODO: move to using a control registry to manage most of the
 * debugging, etc. controls.
 *)

structure Ctl : sig

  (* the top-level registery of the compiler *)
    val topRegistry : ControlRegistry.registry

  (* miscellaneous controls *)
    val warnings : bool Controls.control
    val enableLog : bool Controls.control
    val jsonStats : bool Controls.control
    val collectStats : bool Controls.control
    val verbose : bool Controls.control
    val logTiming : bool Controls.control
    val enableColor : bool Controls.control
    val logControls : bool Controls.control list

  (* controls for optimizations *)
    val simpleUncurry : bool Controls.control
    val simpleInline : bool Controls.control
    val simpleTyContract : bool Controls.control
    val simpleFixFix : bool Controls.control
    val simpleOpt : bool Controls.control
    val varAnalysis : bool Controls.control
    val joinConts : bool Controls.control
    val syntacticOptimizeCPS : bool Controls.control
    val optimizeCPS : bool Controls.control
    val optimizeControls : bool Controls.control list

  (* controls for invariant checking of IRs and analyses *)
    val checkControls : bool Controls.control list
    val checkSimple : bool Controls.control
    val checkCPS : bool Controls.control
    val checkAnalysisStateSpace : bool Controls.control
    val checkAnalysisResults : bool Controls.control
    val checkAnalysisExtentResults : bool Controls.control
    val checkAll : bool Controls.control

  (* controls for dumping IRs and other information *)
    val dumpPT : bool Controls.control
    val dumpAST : bool Controls.control
    val showASTTypes : bool Controls.control
    val dumpSimple : bool Controls.control
    val showSimpleTypes : bool Controls.control
    val dumpCPS : bool Controls.control
    val dumpCPSWithLabels : bool Controls.control
    val dumpCPSCoverage : bool Controls.control
    val dumpOptimizedCPS : bool Controls.control
    val dumpCPSInformation : bool Controls.control
    val dumpExtents : bool Controls.control
    val dumpExtentSummary : bool Controls.control
    val dumpAllocationSummary : bool Controls.control
    val dumpAnalysisStateSpace : bool Controls.control
    val dumpAnalysisSummary : bool Controls.control
    val dumpOptimizationSummary : bool Controls.control
    val dumpInterpreterSummary : bool Controls.control
    val dumpControls : bool Controls.control list
    val dumpAll : bool ref

  (* controls for debugging *)
    val debugUnify : bool Controls.control
    val debugTypeChk : bool Controls.control
    val debugPatChk : bool Controls.control
    val debugOverloads : bool Controls.control
    val debugMatch : bool Controls.control
    val debugVarAnalysis : bool Controls.control
    val debugSimpleOpt : bool Controls.control
    val debugFixFix : bool Controls.control
    val debugSimpleFreeVars : bool Controls.control
    val debugAnalysisStateSpace : bool Controls.control
    val debugAnalysisResults : bool Controls.control
    val debugControls : bool Controls.control list

  (* after the controls have been set from the command line, we use this function
   * to enable logging if any of the dump or check options have been selected.
   *)
    val resolve : unit -> unit

  end = struct

    structure C = Controls
    structure CReg = ControlRegistry

    val topRegistry = CReg.new {help = "smlc controls"}

  (* create a boolean control and add it to the registry *)
    fun newBoolCtl arg = let
          val ctl = C.genControl arg
          in
             CReg.register topRegistry {
                ctl = Controls.stringControl ControlUtil.Cvt.bool ctl,
                envName = NONE
              };
            ctl
          end

  (* main compiler controls *)
    val warnings = C.genControl {
            name = "warnings",
            pri = [1, 5],
            obscurity = 5,
            help = "disable compiler warnings about source file",
            default = true
          }

  (* information controls *)
    val enableLog = C.genControl {
            name = "log",
            pri = [1, 1],
            obscurity = 5,
            help = "output compiler debugging message to a log file",
            default = false
          }
    val jsonStats = C.genControl {
            name = "json",
            pri = [1, 2],
            obscurity = 5,
            help = "output a JSON file with statistics and timings",
            default = false
          }
    val collectStats = C.genControl {
            name = "stats",
            pri = [1, 2],
            obscurity = 5,
            help = "collect and report statistics about optimizations, etc.",
            default = false
          }
    val verbose = C.genControl {
            name = "verbose",
            pri = [1, 3],
            obscurity = 5,
            help = "print messages to stderr as each compiler stage starts and ends",
            default = false
        }
    val logTiming = C.genControl {
            name = "timing",
            pri = [1, 4],
            obscurity = 5,
            help = "record the compiler times in the log file",
            default = false
        }
    val enableColor = C.genControl {
            name = "color",
            pri = [1, 5],
            obscurity = 6,
            help = "enable ANSI colors in the diagnostic output",
            default = false
          }

    val logControls : bool Controls.control list = [
            logTiming, jsonStats, enableColor
          ]

  (* controls for optimizations *)
    val simpleOpt = C.genControl {
            name = "simple-opt",
            pri = [2, 0, 0],
            obscurity = 5,
            help = "disable all optimization of Simple AST",
            default = true
          }
    val simpleTyContract = C.genControl {
            name = "simple-type-opt",
            pri = [2, 0, 1],
            obscurity = 5,
            help = "disable type specialization of Simple AST",
            default = true
          }
    val simpleFixFix = C.genControl {
            name = "simple-fix-fix",
            pri = [2, 0, 2],
            obscurity = 5,
            help = "split recursive function bindings",
            default = true
          }
    val simpleUncurry = C.genControl {
            name = "simple-uncurry",
            pri = [2, 0, 3],
            obscurity = 5,
            help = "disable uncurrying optimization of Simple AST",
            default = true
          }
    val simpleInline = C.genControl {
            name = "simple-inline",
            pri = [2, 0, 4],
            obscurity = 5,
            help = "disable expansive inlining of Simple AST",
            default = true
          }
    val varAnalysis = C.genControl {
            name = "var-analysis",
            pri = [2, 1, 0],
            obscurity = 5,
            help = "disable Simple AST variable analysis",
            default = true
          }
    val joinConts = C.genControl {
            name = "join-conts",
            pri = [2, 1, 0],
            obscurity = 5,
            help = "disable using continuations to represent join functions",
            default = true
          }
    val syntacticOptimizeCPS = C.genControl {
            name = "syntactic-cps-optimizations",
            pri = [2, 1, 1],
            obscurity = 5,
            help = "perform syntax-based optimizations (as opposed to analysis-based) on the CPS before analysis",
            default = false
          }
    val optimizeCPS = C.genControl {
            name = "cps-optimizations",
            pri = [2, 1, 1],
            obscurity = 5,
            help = "perform analysis-based optimizations on the CPS",
            default = false
          }
    val useBanerjeeForSyntactic = C.genControl {
            name = "use-banerjee-for-syntactic",
            pri = [2, 1, 2],
            obscurity = 5,
            help = "use the results of the Banerjee analysis for the syntactic annotations",
            default = false
          }

    val optimizeControls : bool Controls.control list = [
            simpleOpt, simpleUncurry, simpleInline, simpleFixFix, varAnalysis, joinConts,
            syntacticOptimizeCPS, optimizeCPS, useBanerjeeForSyntactic
          ]

  (* controls for invariant-checking various IRs *)
    val checkAll = C.genControl {
            name = "check-all",
            pri = [3, 0],
            obscurity = 5,
            help = "enable all internal validity checks",
            default = false
          }
    val checkSimple = C.genControl {
            name = "check-simple",
            pri = [3, 2],
            obscurity = 5,
            help = "check the validity of the Simple AST IR",
            default = true
          }
    val checkCPS = C.genControl {
            name = "check-cps",
            pri = [3, 3],
            obscurity = 5,
            help = "check the validity of the CPS IR",
            default = false
          }
    val checkAnalysisStateSpace = C.genControl {
            name = "check-analysis-state-space",
            pri = [3, 4],
            obscurity = 5,
            help = "check that the state space is correct",
            default = false
          }
    val checkAnalysisResults = C.genControl {
            name = "check-analysis-results",
            pri = [3, 6],
            obscurity = 5,
            help = "check everything but variable extents and dump related information to the log file",
            default = false
          }
    val checkAnalysisExtentResults = C.genControl {
            name = "check-analysis-extent-results",
            pri = [3, 6],
            obscurity = 5,
            help = "check the variable extents and dump related information to the log file",
            default = false
          }
    val baseCheckControls : bool Controls.control list = [
            checkSimple, checkCPS, checkAnalysisStateSpace, checkAnalysisResults, checkAnalysisExtentResults
          ]
    val checkControls : bool Controls.control list =  [
            checkSimple, checkCPS, checkAnalysisStateSpace, checkAnalysisResults, checkAnalysisExtentResults,
            checkAll
          ]

  (* controls for printing various IRs *)
    val dumpPT = C.genControl {
            name = "dump-pt",
            pri = [4, 0],
            obscurity = 5,
            help = "dump the parse tree to the log file",
            default = false
          }
    val dumpAST = C.genControl {
            name = "dump-ast",
            pri = [4, 1],
            obscurity = 5,
            help = "dump the AST to the log file",
            default = false
          }
    val showASTTypes = C.genControl {
            name = "show-ast-types",
            pri = [4, 1, 1],
            obscurity = 5,
            help = "show types when dumping AST",
            default = false
          }
    val dumpSimple = C.genControl {
            name = "dump-simple",
            pri = [4, 2],
            obscurity = 5,
            help = "dump the SimpleAST to the log file",
            default = false
          }
    val showSimpleTypes = C.genControl {
            name = "show-simple-types",
            pri = [4, 2, 1],
            obscurity = 5,
            help = "show types when dumping Simple AST",
            default = false
          }
    val dumpCPS = C.genControl {
            name = "dump-cps",
            pri = [4, 3],
            obscurity = 5,
            help = "dump the CPS to the log file",
            default = false
          }
    val dumpCPSWithLabels = C.genControl {
            name = "dump-cps-with-labels",
            pri = [4, 3],
            obscurity = 6,
            help = "dump the CPS with labels to the log file",
            default = false
          }
    val dumpCPSCoverage = C.genControl {
            name = "dump-cps-coverage",
            pri = [4, 3],
            obscurity = 6,
            help = "dump the CPS to the log file, highlighting expressions that were not reached via interpretation",
            default = false
          }
    val dumpOptimizedCPS = C.genControl {
            name = "dump-optimized-cps",
            pri = [4, 3],
            obscurity = 7,
            help = "dump the optimized CPS to the log file",
            default = false
          }
    val dumpCPSInformation = newBoolCtl {
            name = "dump-cps-info",
            pri = [5, 8],
            obscurity = 5,
            help = "dump debug info about the CPS information module to the log file",
            default = false
          }
    val dumpCPSInformationTiming = newBoolCtl {
            name = "dump-cps-info-timing",
            pri = [5, 9],
            obscurity = 5,
            help = "dump timing results for the CPS information phase to the log file",
            default = false
          }
    val dumpExtents = C.genControl {
            name = "dump-extents",
            pri = [5, 10],
            obscurity = 5,
            help = "dump all of the variable extents to the log file",
            default = false
        }
    val dumpExtentSummary = C.genControl {
            name = "dump-extent-summary",
            pri = [5, 11],
            obscurity = 5,
            help = "dump the extent promotion information to the log file",
            default = false
        }
    val dumpAllocationSummary = C.genControl {
            name = "dump-allocation-summary",
            pri = [5, 12],
            obscurity = 5,
            help = "dump the allocations due to extent promotions to the log file",
            default = false
        }
    val dumpAnalysisStateSpace = newBoolCtl {
            name = "dump-analysis-state-space",
            pri = [5, 13],
            obscurity = 5,
            help = "dump the analysis state space used for extent analysis, etc. to the log file",
            default = false
          }
    val dumpAnalysisSummary = newBoolCtl {
            name = "dump-analysis-summary",
            pri = [5, 14],
            obscurity = 5,
            help = "dump summary information about the CPS analyses to the log file",
            default = false
          }
    val dumpOptimizationSummary = newBoolCtl {
            name = "dump-optimization-summary",
            pri = [5, 15],
            obscurity = 5,
            help = "dump summary information about the CPS optimization passes to the log file",
            default = false
          }
    val dumpInterpreterSummary = newBoolCtl {
            name = "dump-interpreter-summary",
            pri = [5, 16],
            obscurity = 5,
            help = "dump summary information about the interpreter run to the log file",
            default = false
          }
    val dumpBanerjee = newBoolCtl {
            name = "dump-banerjee",
            pri = [5, 17],
            obscurity = 5,
            help = "run the Banerjee and dump the related information",
            default = false
          }
    val baseDumpControls = [
            dumpPT, dumpAST, dumpSimple, dumpCPS, dumpCPSWithLabels, dumpCPSCoverage,
            dumpCPSInformation, dumpExtents, dumpExtentSummary, dumpAllocationSummary,
            dumpAnalysisStateSpace, dumpAnalysisSummary, dumpOptimizationSummary, dumpInterpreterSummary, dumpBanerjee
          ]
    val timeCPSInformation = newBoolCtl {
            name = "time-cps-info",
            pri = [5, 14],
            obscurity = 5,
            help = "time the CPS information module to the log file",
            default = false
          }
    val dumpControls = [
            dumpPT, dumpAST, showASTTypes, dumpSimple, showSimpleTypes,
            dumpCPS, dumpCPSWithLabels, dumpCPSCoverage, dumpOptimizedCPS,
            dumpCPSInformation, dumpExtents, dumpExtentSummary, dumpAllocationSummary,
            dumpAnalysisStateSpace, dumpAnalysisSummary, dumpOptimizationSummary, dumpInterpreterSummary, dumpBanerjee,
            timeCPSInformation
          ]
    val dumpAll = ref false

  (* controls for debugging *)
    val debugUnify = newBoolCtl {
            name = "debug-unify",
            pri = [5, 1],
            obscurity = 5,
            help = "debug unification",
            default = false
          }
    val debugTypeChk = newBoolCtl {
            name = "debug-ty-chk",
            pri = [5, 2],
            obscurity = 5,
            help = "debug type checking",
            default = false
          }
    val debugPatChk = newBoolCtl {
            name = "debug-pat-chk",
            pri = [5, 3],
            obscurity = 5,
            help = "debug pattern checking",
            default = false
          }
    val debugOverloads = newBoolCtl {
            name = "debug-overloads",
            pri = [5, 4],
            obscurity = 5,
            help = "debug overload resolution",
            default = false
          }
    val debugMatch = newBoolCtl {
            name = "debug-match-comp",
            pri = [5, 5],
            obscurity = 5,
            help = "debug pattern-match compilation",
            default = false
          }
    val debugSimpleOpt = newBoolCtl {
            name = "debug-simple-opt",
            pri = [5, 6],
            obscurity = 5,
            help = "debug optimization of Simple AST",
            default = false
          }
    val debugFixFix = newBoolCtl {
            name = "debug-fix-fix",
            pri = [5, 6, 1],
            obscurity = 5,
            help = "debug splitting of recursive function bindings",
            default = false
          }
    val debugSimpleFreeVars = newBoolCtl {
            name = "debug-simple-free-vars",
            pri = [5, 6, 2],
            obscurity = 5,
            help = "debug the free-variable analysis for the Simple AST",
            default = false
          }
    val debugVarAnalysis = newBoolCtl {
            name = "debug-var-analysis",
            pri = [5, 6, 3],
            obscurity = 5,
            help = "debug syntactic variable analysis",
            default = false
          }
    val debugAnalysisStateSpace = newBoolCtl {
            name = "debug-analysis-state-space",
            pri = [5, 8],
            obscurity = 5,
            help = "debug state space generation and dump related information to the log file",
            default = false
          }
    val debugAnalysisResults = newBoolCtl {
            name = "debug-analysis-results",
            pri = [5, 9],
            obscurity = 5,
            help = "debug the results of the extent analysis, etc. and dump related information to the log file",
            default = false
          }
    val debugControls = [
            debugUnify, debugPatChk, debugTypeChk, debugOverloads, debugMatch,
            debugSimpleOpt, debugFixFix, debugSimpleFreeVars, debugVarAnalysis,
            debugAnalysisStateSpace, debugAnalysisResults
          ]

    fun resolve () = (
          if !dumpAll
            then List.app (fn ctl => C.set(ctl, true)) baseDumpControls
            else ();
          if C.get checkAll
            then List.app (fn ctl => C.set(ctl, true)) baseCheckControls
            else ();
          if C.get debugSimpleOpt
            then C.set(checkSimple, true)
            else ();
          if not(C.get enableLog)
          andalso List.exists C.get (baseDumpControls @ debugControls)
            then C.set (enableLog, true)
            else ();
          if C.get dumpCPSWithLabels
            then Controls.set (dumpCPS, true)
            else ();
          (* we don't want to enable the first dump of CPS, but we do want to dump with labels *)
          if C.get dumpCPSCoverage
            then Controls.set (dumpCPSWithLabels, true)
            else ())

  end
