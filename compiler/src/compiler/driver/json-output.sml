(* json-output.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Support for dumping various statistics about the compilation
 * to a JSON file.
 *)

structure JSONOutput : sig

    val dump : { source : string, outFile : string } -> unit

  end = struct

    fun intToJSON n = JSON.INT(IntInf.fromInt n)

  (* record the date *)
    fun dateToJSON () = let
          val date = Date.fromTimeLocal(Time.now())
          fun num (label, get) = (label, intToJSON(get date))
          val month = (case Date.month date
                 of Date.Jan => JSON.INT 1
                  | Date.Feb => JSON.INT 2
                  | Date.Mar => JSON.INT 3
                  | Date.Apr => JSON.INT 4
                  | Date.May => JSON.INT 5
                  | Date.Jun => JSON.INT 6
                  | Date.Jul => JSON.INT 7
                  | Date.Aug => JSON.INT 8
                  | Date.Sep => JSON.INT 9
                  | Date.Oct => JSON.INT 10
                  | Date.Nov => JSON.INT 11
                  | Date.Dec => JSON.INT 12
                (* end case *))
          in
            JSON.OBJECT[
                num("year", Date.year),
                ("month", month),
                num("day", Date.day),
                num("hour", Date.hour),
                num("minute", Date.minute),
                num("second", Date.second)
              ]
          end

  (* convert the command line options to a JSON array *)
    fun optionsToJSON () = JSON.ARRAY(List.map JSON.STRING (CommandLine.arguments()))

    (* apparently it can't see PromotionDump (.t), so define the type locally *)
    type promotion = {
        HtoH : int, HtoS : int, HtoR : int, HtoSR : int,
        StoH : int, StoS : int, StoR : int, StoSR : int,
        RtoH : int, RtoS : int, RtoR : int, RtoSR : int,
        SRtoH : int, SRtoS : int, SRtoR : int, SRtoSR : int
      }

    (* Obtain the counts of promotion for each promotion type *)
    fun promotionsToJSON () = let
          val {lvar=lvStoA, ldata=ldStoA} = ExtentAnalysis.getPromotionResults ()
          val {lvar=lvAtoT, ldata=ldAtoT} = CPSInterpreter.getPromotionResults ()
          fun toJSON (promotions : promotion) = JSON.OBJECT[
                  ("H -> H", intToJSON (#HtoH promotions)),
                  ("H -> S", intToJSON (#HtoS promotions)),
                  ("H -> R", intToJSON (#HtoR promotions)),
                  ("H -> SR", intToJSON (#HtoSR promotions)),
                  ("S -> S", intToJSON (#StoS promotions)),
                  ("S -> SR", intToJSON (#StoSR promotions)),
                  ("R -> R", intToJSON (#RtoR promotions)),
                  ("R -> SR", intToJSON (#RtoSR promotions)),
                  ("SR -> SR", intToJSON (#SRtoSR promotions))
                ]
          in [
            ("promotions", JSON.OBJECT[
                ("syntactic-to-analysis", JSON.OBJECT[
                    ("lvars", toJSON lvStoA),
                    ("data", toJSON ldStoA)
                  ]),
                ("analysis-to-true", JSON.OBJECT[
                    ("lvars", toJSON lvAtoT),
                    ("ldata", toJSON ldAtoT)
                  ])
              ])
          ] end

    (* Obtain the counts of allocations for each promotion type *)
    fun allocationsToJSON () = let
          val {lvar=lvStoA, ldata=ldStoA} = ThreeCPSInterpreter.getAllocationResults ()
          fun toJSON (allocations : promotion) = JSON.OBJECT[
                  ("H -> H", intToJSON (#HtoH allocations)),
                  ("H -> S", intToJSON (#HtoS allocations)),
                  ("H -> R", intToJSON (#HtoR allocations)),
                  ("H -> SR", intToJSON (#HtoSR allocations)),
                  ("S -> S", intToJSON (#StoS allocations)),
                  ("S -> SR", intToJSON (#StoSR allocations)),
                  ("R -> R", intToJSON (#RtoR allocations)),
                  ("R -> SR", intToJSON (#RtoSR allocations)),
                  ("SR -> SR", intToJSON (#SRtoSR allocations))
                ]
          in [
            ("allocations", JSON.OBJECT[
                ("syntactic-to-analysis", JSON.OBJECT[
                    ("lvars", toJSON lvStoA),
                    ("data", toJSON ldStoA)
                  ])
              ])
          ] end

  (* build a JSON object for the extents *)
    fun extentsToJSON () = let
          val (extents, criteria) = CPSInterpreter.getResults ()
          fun infoToJSON (label, proj) = let
                val {stk, reg} = proj extents
                in
                  (label, JSON.OBJECT[
                      ("stk", intToJSON stk),
                      ("reg", intToJSON reg)
                    ])
                end
          fun critToJSON (label, proj1, proj2, proj3) =
                (label, JSON.OBJECT[
                    ("rel_ext", intToJSON (proj1 criteria)),
                    ("uniq_crit", intToJSON (proj2 criteria)),
                    ("ext_crit", intToJSON (proj3 criteria))
                  ])
          in [
            ("extents", JSON.OBJECT[
                ("lvars", JSON.OBJECT[
                    ("total", intToJSON (#totalLVars extents)),
                    infoToJSON ("syntactic", #syntacticLVars),
                    infoToJSON ("analysis", #analysisLVars),
                    infoToJSON ("true", #trueLVars)
                  ]),
                ("ldata", JSON.OBJECT[
                    ("total", intToJSON (#totalLData extents)),
                    infoToJSON ("syntactic", #syntacticLData),
                    infoToJSON ("analysis", #analysisLData),
                    infoToJSON ("true", #trueLData)
                  ])
              ]),
            ("criteria", JSON.OBJECT[
                ("lvars", JSON.OBJECT[
                    ("total", intToJSON (#total_criteria_lvar_pairs criteria)),
                    critToJSON ("analysis",
                      #analysis_rel_ext_lvar_pairs,
                      #analysis_uniq_crit_lvar_pairs,
                      #analysis_ext_crit_lvar_pairs),
                    critToJSON ("true",
                      #true_rel_ext_lvar_pairs,
                      #true_uniq_crit_lvar_pairs,
                      #true_ext_crit_lvar_pairs)
                  ]),
                ("ldata", JSON.OBJECT[
                    ("total", intToJSON (#total_criteria_ldata_pairs criteria)),
                    critToJSON ("analysis",
                      #analysis_rel_ext_ldata_pairs,
                      #analysis_uniq_crit_ldata_pairs,
                      #analysis_ext_crit_ldata_pairs),
                    critToJSON ("true",
                      #true_rel_ext_ldata_pairs,
                      #true_uniq_crit_ldata_pairs,
                      #true_ext_crit_ldata_pairs)
                  ])
              ])
          ] end

  (* dump statistics to a JSON file *)
    fun dump {source, outFile} = let
          val obj = JSON.OBJECT([
                  ("source", JSON.STRING source),
                  ("date", dateToJSON()),
                  ("options", optionsToJSON()),
                  ("compiler-stats", Stats.Group.toJSON Stats.Group.root),
                  ("timing", PhaseTimer.toJSON Timers.timeCompiler)
                ] @ (extentsToJSON ()) 
                  @ (promotionsToJSON ())
                  @ (allocationsToJSON ()))
          val outS = TextIO.openOut outFile
          in
            JSONPrinter.print' {pretty = true, strm = outS} obj;
            TextIO.closeOut outS
          end

  end

