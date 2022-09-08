(* simple-opt.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Some simple optimizations for the SimpleAST representation.  These include
 * simple contraction and let denesting.
 *)

structure SimpleOpt : sig

    val transform : SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST

  (* messages in verbose mode *)
    fun verbosePrint msg = if Controls.get Ctl.verbose
          then TextIO.output(TextIO.stdErr, concat["  simple-opt: ", msg])
          else ()

    fun denest (S.CU fb) =
          CheckSimpleAST.check ("denesting", S.CU(SimpleOptUtil.denestFB fb))

    fun fixfix (info, prog) =
          CheckSimpleAST.checkWithCensus info
            ("fix-fix", FixFix.transform prog)

    fun contractTys (info, prog) =
          CheckSimpleAST.checkWithCensus info
            ("type contraction", ContractTypes.transform (info, prog))

    fun uncurry (info, prog) =
          CheckSimpleAST.checkWithCensus info
            ("uncurrying", Uncurry.transform (info, prog))

    fun inline (info, prog) =
          CheckSimpleAST.checkWithCensus info
            ("inlining", Inline.transform (info, prog))

    fun transform prog = if Controls.get Ctl.simpleOpt
          then let
          (* denest lets *)
	    val _ = verbosePrint "denesting\n"
            val prog = denest prog
          (* compute census info *)
	    val _ = verbosePrint "census\n"
            val info = Census.analyze prog
          (* run contraction *)
	    val _ = verbosePrint "contraction\n"
            val prog = Contract.transform (info, prog)
          (* fix recursive function bindings by splitting into minimal components *)
            val prog = if Controls.get Ctl.simpleFixFix
                  then (
                    verbosePrint "fix-fix\n";
                    fixfix (info, prog))
                  else prog
          (* type specialization *)
            val prog = if Controls.get Ctl.simpleTyContract
                  then (
		    verbosePrint "contract types\n";
		    contractTys (info, prog))
                  else prog
          (* reassociate data constructors *)
	    val _ = verbosePrint "reassociate\n"
            val prog = Reassoc.transform (info, prog)
          (* uncurrying *)
	    val _ = verbosePrint "uncurry\n"
            val prog = if Controls.get Ctl.simpleUncurry
                  then uncurry (info, prog)
                  else prog
          (* expansive inlining *)
	    val _ = verbosePrint "inlining\n"
            val prog = if Controls.get Ctl.simpleInline
                  then inline (info, prog)
                  else prog
          (* final contraction *)
	    val _ = verbosePrint "contraction\n"
            val prog = Contract.transform (info, prog)
            in
              prog
            end
          else denest prog  (* always apply denesting *)

  end
