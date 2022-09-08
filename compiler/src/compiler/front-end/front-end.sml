(* front-end.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure FrontEnd : sig

    exception InternalError

    val doFile : string -> SimpleAST.comp_unit

  end = struct

    exception InternalError

  (* messages in verbose mode *)
    fun verbosePrint msg = if Controls.get Ctl.verbose
          then TextIO.output(TextIO.stdErr, concat msg)
          else ()

  (* check for errors and report them if there are any *)
    fun checkForErrors errS =
          if Error.anyErrors errS
            then raise Error.ERROR
            else ()

  (* conditional printing of intermediate forms *)
    fun dump ctl output phase prog = if Controls.get ctl
          then output (Log.outstream(), "After " ^ phase, prog)
          else ()

    val dumpPT = dump Ctl.dumpPT PrintPT.output "parsing"
    val dumpAST = dump Ctl.dumpAST PrintAST.output

    val chkSimple = CheckSimpleAST.check

  (* compiler front end (parsing, typechecking, and simplification *)
    fun frontEnd (errS, file) = let
          val _ = if OS.FileSys.access(file, [OS.FileSys.A_READ])
                then ()
                else (
                  Error.error (errS, [
                      "source file \"", file, "\" does not exist or is not readable\n"
                    ]);
                  raise Error.ERROR)
        (***** PARSING *****)
          val _ = verbosePrint["parsing ... "]
          val parseTree = PhaseTimer.withTimer Timers.timeParser (fn () => let
                val inS = TextIO.openIn file
                val pt = Parser.parseFile (errS, inS)
                in
                  TextIO.closeIn inS;
                  checkForErrors errS;
                  valOf pt
                end) ()
          val _ = verbosePrint["done\n"]
          val _ = dumpPT parseTree
        (***** BINDING CHECK *****)
          val _ = verbosePrint["binding check ... "]
(* NOTE: for now we count this phase as part of typechecking *)
          val _ = PhaseTimer.start Timers.timeTypechecker
          val bt = Binding.check (errS, parseTree)
          val _ = PhaseTimer.stop Timers.timeTypechecker
          val _ = verbosePrint["done\n"];
        (***** TYPECHECKING *****)
          val _ = verbosePrint["type checking ... "]
          val _ = PhaseTimer.start Timers.timeTypechecker
          val ast = Typechecker.check (errS, bt)
          val _ = PhaseTimer.stop Timers.timeTypechecker
          val _ = verbosePrint["done\n"];
          val _ = checkForErrors errS
          val _ = dumpAST "typechecking" ast
        (***** PATTERN-MATCH COMPILATION *****)
          val _ = verbosePrint["compiling pattern matches ... "]
          val _ = PhaseTimer.start Timers.timeMatchComp
          val ast = MatchComp.transform ast
          val _ = PhaseTimer.stop Timers.timeMatchComp
          val _ = verbosePrint["done\n"];
          val _ = dumpAST "pattern-match compilation" ast
        (***** SIMPLIFY *****)
          val _ = verbosePrint["simplifying AST ... "]
          val _ = PhaseTimer.start Timers.timeSimplify
          val simple = Simplify.transform ast
          val _ = PhaseTimer.stop Timers.timeSimplify
          val _ = verbosePrint["done\n"];
          val _ = chkSimple ("simplify", simple)
        (***** OPTIMIZATION OF SIMPLE AST *****)
          val _ = verbosePrint["optimizing Simple AST ... "]
          val _ = PhaseTimer.start Timers.timeSimpleOpt
          val simple = SimpleOpt.transform simple
          val _ = PhaseTimer.stop Timers.timeSimpleOpt
          val _ = verbosePrint["done\n"];
          val _ = chkSimple ("simple-opt", simple)
          in
            simple
          end

  (* a wrapper around the front-end that handles the Error.ERROR exception and reports
   * the error messages.
   *)
    fun doFile srcFile = let
          val _ = PhaseTimer.start Timers.timeFront
          val errStrm = Error.mkErrStream srcFile
          fun finish () = (
                PhaseTimer.stop Timers.timeFront;
                if Error.anyErrors errStrm orelse Error.anyWarnings errStrm
                  then Error.report (TextIO.stdErr, errStrm)
                  else ())
          in
            (frontEnd (errStrm, srcFile) handle exn => (finish (); raise exn))
            before finish()
          end

  end
