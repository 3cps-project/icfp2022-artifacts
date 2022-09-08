(* options.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Options : sig

  (* raised if parsing command-line args hits an error (e.g., missing option, syntax, ...).
   * The string is an error message.
   *)
    exception Usage of string

  (* parse the command-line args *)
    val parseCmdLine : string list -> {
            help : bool option,         (* "-h" and "--help" ==> SOME false; "-H" ==> SOME true. *)
            srcFile : string,           (* source file *)
            outDir : string,            (* output directory *)
            outBase : string            (* stem of output file *)
          }

  (* return a usage message.  The boolean controls whether all options should be
   * included (true ==> long; false ==> short).
   *)
    val usage : string * bool -> string

  end = struct

    structure G = GetOpt
    structure P = OS.Path

    exception Usage of string

  (* option flags that are set by getOpt *)
    val helpFlg = ref(NONE : bool option)       (* SOME false -- short help; SOME true -- long help *)
    val outputOpt : string option ref = ref NONE

  (* make a command-line option description from a boolean control *)
    fun mkOpt ctl = let
          val name = if Controls.get ctl
                then "disable-" ^ Controls.name ctl
                else Controls.name ctl
          in
            Controls.mkOptionFlag {ctl = ctl, short = "", long = SOME name}
          end

    fun setFlag (flg, value) = G.NoArg(fn () => (flg := value))

  (* the short list of options, which does not include the compiler controls *)
    val optionList = [
            { short = "h", long = ["help"],
              desc = setFlag (helpFlg, SOME false),
              help = "print command-line options"
            },
            { short = "H", long = [],
              desc = setFlag (helpFlg, SOME true),
              help = "print all command-line options (including compiler controls)"
            },
            { short = "o", long = ["output"],
              desc = G.ReqArg(fn s => outputOpt := SOME s, "file"),
              help = "specify the executable file name"
            },
            mkOpt Ctl.warnings,
            mkOpt Ctl.enableLog,
            mkOpt Ctl.collectStats,
            mkOpt Ctl.verbose
          ]

  (* create the list of options that control compiler internals *)
    val ctlOptions = let
          val logControls = List.map mkOpt Ctl.logControls @ [
                  { short = "", long = ["log-ticks"],
                    desc = setFlag (Stats.logTicks, false),
                    help = "log each optimization tick as it is recorded"
                  }
                ]
          val optimizeFlags = List.map mkOpt Ctl.optimizeControls
          val dumpFlags = List.map mkOpt Ctl.dumpControls @ [
                  { short = "", long = ["dump-all"],
                    desc = setFlag (Ctl.dumpAll, true),
                    help = "dump out all intermediate representations to the log file"
                  }
                ]
          val debugFlags = List.map mkOpt Ctl.debugControls
          val checkFlags = List.map mkOpt Ctl.checkControls
          in
            optimizeFlags @ logControls @ checkFlags @ dumpFlags @ debugFlags
          end

    fun parseCmdLine [] = { help = SOME false, srcFile = "", outDir = "", outBase = "" }
      | parseCmdLine args = let
          val (opts, files) = G.getOpt {
                  argOrder = G.RequireOrder,
                  options = optionList @ ctlOptions,
                  errFn = fn s => raise Usage s
                } args
        (* figure out filename pieces *)
          val srcFile =
                if isSome(!helpFlg)
                  then ""
                  else (case files
                     of [] => raise Usage "missing file argument"
                      | [f] => f
                      | _ => raise Usage "too many files"
                    (* end case *))
          val (outDir, outBase) =  (case !outputOpt
                 of NONE => let
                      val {dir, file} = P.splitDirFile srcFile
                      in
                        case P.splitBaseExt file
                         of {base, ext=SOME "sml"} => (dir, base)
                          | _ => (dir, file)
                        (* end case *)
                      end
                  | SOME outFile => let
                      val {dir, file} = P.splitDirFile outFile
                      in
                        (dir, file)
                      end
                (* end case *))
          in {
            help = !helpFlg,
            srcFile = srcFile,
            outDir = outDir,
            outBase = outBase
          } end

    fun usage (cmd, long) = let
          val hdr = concat[
                  "usage: ", cmd, " [options] file.sml\n",
                  "  Options:"
                ]
          in
            if long
              then G.usageInfo {header = hdr, options = optionList @ ctlOptions}
              else G.usageInfo {header = hdr, options = optionList}
          end

  end
