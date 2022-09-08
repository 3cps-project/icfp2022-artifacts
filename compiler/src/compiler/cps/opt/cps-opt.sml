(* cps-opt.sml
 *
 * a file to group optimizations performed on the CPS IR
 *)

structure CPSOpt : sig

    val transform : CPS.comp_unit -> CPS.comp_unit

(* FIXME: the optimizer ought to be responsible for calling the analysis *)
    val transform_analysis : CPS.comp_unit * ExtentAnalysis.t -> CPS.comp_unit
  end = struct

    structure AInfo = AnalysisInformation

    (* keep doing passes until you've gone through each without changing *)
    fun cycle (cu, passes0) = let
        val max = List.length passes0
        fun lp (cu, passes, count) =
            if count = max
            then cu
            else (case passes
                  of (pass, msg)::passes =>
                     (case pass cu
                       of SOME cu => (DumpOptimizationSummary.say [msg, "\n"];
                                      lp (cu, passes, 0))
                        | NONE => lp (cu, passes, count + 1))
                   | [] => lp (cu, passes0, count))
    in lp (cu, passes0, 0) end

    fun transform (cu) = let
        val passes = [(CPSSimpleArityRaising.raise_arities, "simple raised arities!"),
                      (CPSSimpleArgumentElimination.eliminate_arguments, "simple eliminated arguments!"),
                      (CPSRedundantSelection.redundant_selection, "redundant-selected!"),
                      (CPSContraction.contract, "contracted!"),
                      (CPSPropagateMoves.propagate_moves, "propagated moves!")]
        val cu = cycle (cu, passes)
        val () = SyntacticExtentAnalysis.analyze cu
        val _ = DumpCPSOpt.dump ()
    in cu end

    fun transform_analysis (cu, ExtentAnalysis.Info info) = let
        val ainfo = #ainfo info
        val webs = {user = AInfo.callWebs ainfo, cont = AInfo.callWebsK ainfo}
        val cu = CPSArgumentFlattening.transform (cu, webs)
        val cu = transform cu
    in cu end

  end
