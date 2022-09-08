(* main.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Driver for 3-CPS SML compiler.
 *)

structure Main : sig

    val main : (string * string list) -> OS.Process.status

    val doFile : string * string * string -> unit

  end = struct

    structure PT = PhaseTimer
    structure Tm = Timers

    fun err s = TextIO.output (TextIO.stdErr, s)

    fun outFileName (outDir, outBase, ext) = OS.Path.joinDirFile {
            dir = outDir,
            file = OS.Path.joinBaseExt { base = outBase, ext = SOME ext }
          }

  (* messages in verbose mode *)
    fun verbosePrint msg = if Controls.get Ctl.verbose
          then TextIO.output(TextIO.stdErr, concat msg)
          else ()

  (* conditional printing of intermediate forms *)
    fun dump ctl output phase prog = if Controls.get ctl
          then output (Log.outstream(), "After " ^ phase, prog)
          else ()

    fun dumpCPS ctl = dump ctl PrintCPS.output
    val dumpOptimizedCPS = dump Ctl.dumpOptimizedCPS PrintCPS.output

    val cpsConvert = PT.withTimer Tm.timeConvert Convert.transform
    val extentAnalysis = PT.withTimer Tm.timeAnalysis ExtentAnalysis.analyze

    (*
    fun syntacticOptimizeCPS cps = if Controls.get Ctl.syntacticOptimizeCPS
          then let
            val _ = verbosePrint ["Syntactic CPS optimizations ... "]
            fun doSynOptimizeCPS () = let
                  val webs = DetermineSyntacticCallWebs.callWebs (cps, {add_unknown=true})
                  val cps = CPSArgumentFlattening.transform (cps, webs)
                  val _ = dumpCPS Ctl.dumpCPS "CPS optimized (syntactic)" cps
                  (* val cps = CPSContraction.contract cps *)
                  in
                    cps
                  end
            val cps = PT.withTimer Tm.timeSynOptimizeCPS doSynOptimizeCPS ()
            val _ = verbosePrint ["done\n"]
            in
              cps
            end
          else cps

    fun optimizeCPS (cps, info) = if Controls.get Ctl.optimizeCPS
          then let
            val _ = verbosePrint ["CPS optimizations ... "]
            val cps = PT.withTimer Tm.timeOptimizeCPS CPSOpt.transform (cps, info)
            val _ = verbosePrint ["done\n"]
            val _ = verbosePrint ["Secondary extent analysis ... "]
            val info = extentAnalysis cps
            val _ = verbosePrint ["done\n"]
            val _ = PT.withTimer Tm.timeExtCheck ExtentAnalysis.check (cps, info)
            val _ = dumpOptimizedCPS "CPS optimized" cps
            in
              (cps, info)
            end
          else (cps, info)
    *)
    fun optimizeCPS cps = if Controls.get Ctl.optimizeCPS
          then let
            val _ = verbosePrint ["CPS optimizations ... "]
            val cps = PT.withTimer Tm.timeSynOptimizeCPS CPSOpt.transform cps
            val _ = dumpCPS Ctl.dumpCPS "CPS optimization" cps
            val _ = verbosePrint ["done\n"]
          in cps end
          else cps 

    fun doFile (srcFile, outDir, outBase) = BackTrace.monitor (
          fn () => let
              val _ = PT.start Tm.timeCompiler
              val simple = FrontEnd.doFile srcFile
              val _ = verbosePrint ["CPS conversion ... "]
              val _ = PT.start Tm.timeCPS
              val cps = cpsConvert simple
              val _ = dumpCPS Ctl.dumpCPS "CPS conversion" cps
              val _ = verbosePrint ["done\n"]
              val cps = optimizeCPS cps
              (* val cps = syntacticOptimizeCPS cps *)
              val _ = verbosePrint ["Extent analysis ... "]
              val info = extentAnalysis cps
              val _ = verbosePrint ["done\n"]
              val _ = PT.withTimer Tm.timeExtCheck ExtentAnalysis.check (cps, info)
              val _ = dumpCPS Ctl.dumpCPSCoverage "Expression coverage" cps
              val _ = verbosePrint ["done\n"]
              (* val (cps, info) = optimizeCPS (cps, info) *)
              val _ = PT.stop Tm.timeCPS
(* TODO: additional phases *)
              in
                PT.stop Tm.timeCompiler
              end)

    fun usage (cmd, long) = TextIO.output(TextIO.stdErr, Options.usage (cmd, long))

    fun handleExn Error.ERROR = OS.Process.failure
      | handleExn exn = (
          err (concat [
              "uncaught exception ", General.exnName exn,
              " [", General.exnMessage exn, "]\n"
            ]);
          List.app (fn s => err (concat ["  raised at ", s, "\n"])) (SMLofNJ.exnHistory exn);
          OS.Process.failure)

    fun main (name: string, args: string list) = let
          val {help, srcFile, outDir, outBase} =
                (Options.parseCmdLine args)
                  handle Options.Usage msg => (
                    err(concat["Error: ", msg, "\n"]);
                    usage (name, false);
                    OS.Process.exit OS.Process.failure)
          in
            Ctl.resolve();
            case help
             of SOME long => (usage (name, long); OS.Process.success)
              | NONE => (let
                  val logging = Controls.get Ctl.enableLog
                  in
                    if logging
                      then Log.init(outFileName(outDir, outBase, "log"))
                      else ();
                    doFile (srcFile, outDir, outBase);
                    if Controls.get Ctl.jsonStats
                      then JSONOutput.dump {
                          source = srcFile,
                          outFile = outFileName(outDir, outBase, "json")
                        }
                    else if Controls.get Ctl.collectStats
                      then (
                        if (not logging)
                          then Log.init(outFileName(outDir, outBase, "stats"))
                          else ();
                        Stats.Group.report (Log.outstream(), Stats.Group.root);
                        if (not logging)
                          then (
                            Log.msg ["\n"];
                            Log.reportTiming Tm.timeCompiler)
                          else ())
                      else ();
                    if Controls.get Ctl.logTiming
                      then Log.reportTiming Tm.timeCompiler
                      else ();
                    OS.Process.success
                  end handle exn => handleExn exn)
            (* end case *)
          end

  end
