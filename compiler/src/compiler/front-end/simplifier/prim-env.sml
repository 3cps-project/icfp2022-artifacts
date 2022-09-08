(* prim-env.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * TODO: we should provide a mechanism to expand out some primitive operators
 * into functions (e.g., array operations need to test for out-of-bounds and
 * division should test for divide by zero). We could also introduce join
 * points for common exception-raising (which we currently do during the
 * conversion to CPS).
 *)

structure PrimEnv : sig

    datatype prim_bind
      = Pure of PrimOp.pure
      | Arith of PrimOp.arith
      | Getter of PrimOp.getter
      | Setter of PrimOp.setter
      | Test of PrimOp.test
      | EqTest of bool          (* equality test; true means "=" and false means "<>" *)
      | NotPrim

    val lookup : Var.t -> prim_bind

  end = struct

    structure P = PrimOp
    structure Tgt = Target

    datatype prim_bind
      = Pure of PrimOp.pure
      | Arith of PrimOp.arith
      | Getter of PrimOp.getter
      | Setter of PrimOp.setter
      | Test of PrimOp.test
      | EqTest of bool
      | NotPrim

  (* utility functions for constructing numeric primops at specific precisions *)
    fun mkILt sz = Test(P.ICmp(P.Test.ILt, sz))
    fun mkILte sz = Test(P.ICmp(P.Test.ILte, sz))
    fun mkIGt sz = Test(P.ICmp(P.Test.IGt, sz))
    fun mkIGte sz = Test(P.ICmp(P.Test.IGte, sz))
    fun mkULt sz = Test(P.ICmp(P.Test.ULt, sz))
    fun mkULte sz = Test(P.ICmp(P.Test.ULte, sz))
    fun mkUGt sz = Test(P.ICmp(P.Test.UGt, sz))
    fun mkUGte sz = Test(P.ICmp(P.Test.UGte, sz))
    fun mkFLt sz = Test(P.FCmp(P.Test.FLt, sz))
    fun mkFLte sz = Test(P.FCmp(P.Test.FLte, sz))
    fun mkFGt sz = Test(P.FCmp(P.Test.FGt, sz))
    fun mkFGte sz = Test(P.FCmp(P.Test.FGte, sz))
    fun zext (from, to) = Pure(P.ZExt{from=from, to=to})
    fun sext (from, to) = Pure(P.SExt{from=from, to=to})
    fun mkNumOp rator = Pure(P.NumOp(rator, Tgt.intBits))
    fun mkIntOp rator = Arith(P.IntOp(rator, Tgt.intBits))
    fun mkFltOp rator = Pure(P.NumOp(rator, Tgt.realBits))
    fun mkMathOp rator = Pure(P.MathOp(rator, Tgt.realBits))

    val lookup = let
          val tbl = Var.Tbl.mkTable (128, Fail "prim-env")
          val ins = Var.Tbl.insert tbl
          val find = Var.Tbl.find tbl
          in
            List.app ins [
              (* array operations *)
                (PrimVar.array0, Pure P.Array0),
                (PrimVar.array_alloc, Pure P.ArrayAlloc),
                (PrimVar.array_length, Pure P.ArrayLength),
                (PrimVar.array_sub, Getter P.ArraySub),
                (PrimVar.array_update, Setter P.ArrayUpdate),
              (* character operations *)
                (PrimVar.char_lt, mkULt Tgt.charBits),
                (PrimVar.char_lte, mkULte Tgt.charBits),
                (PrimVar.char_gte, mkUGte Tgt.charBits),
                (PrimVar.char_gt, mkUGt Tgt.charBits),
                (PrimVar.char_ord, zext(Tgt.charBits, Tgt.intBits)),
              (* integer operations *)
                (PrimVar.int_add, mkIntOp P.Arith.IAdd),
                (PrimVar.int_sub, mkIntOp P.Arith.ISub),
                (PrimVar.int_mul, mkIntOp P.Arith.IMul),
                (PrimVar.int_div, mkIntOp P.Arith.IDiv),
                (PrimVar.int_mod, mkIntOp P.Arith.IMod),
                (PrimVar.int_neg, mkIntOp P.Arith.INeg),
                (PrimVar.int_lt, mkILt Tgt.intBits),
                (PrimVar.int_lte, mkILte Tgt.intBits),
                (PrimVar.int_gte, mkIGte Tgt.intBits),
                (PrimVar.int_gt, mkIGt Tgt.intBits),
              (* word operations *)
                (PrimVar.word_add, mkNumOp P.Pure.WAdd),
                (PrimVar.word_sub, mkNumOp P.Pure.WSub),
                (PrimVar.word_mul, mkNumOp P.Pure.WMul),
                (PrimVar.word_div, mkNumOp P.Pure.WDiv),
                (PrimVar.word_mod, mkNumOp P.Pure.WMod),
                (PrimVar.word_neg, mkNumOp P.Pure.WNeg),
                (PrimVar.word_lt, mkULt Tgt.intBits),
                (PrimVar.word_lte, mkULte Tgt.intBits),
                (PrimVar.word_gte, mkUGte Tgt.intBits),
                (PrimVar.word_gt, mkUGt Tgt.intBits),
                (PrimVar.word_andb_fn, mkNumOp P.Pure.Andb),
(* TODO
                (PrimVar.word_fromInt_fn, Pure P.Copy),
*)
                (PrimVar.word_lshift_fn, mkNumOp P.Pure.LShift),
                (PrimVar.word_orb_fn, mkNumOp P.Pure.Orb),
                (PrimVar.word_notb_fn, mkNumOp P.Pure.Notb),
                (PrimVar.word_rshift_fn, mkNumOp P.Pure.RShift),
                (PrimVar.word_rshiftl_fn, mkNumOp P.Pure.RShiftL),
(* TODO
                (PrimVar.word_toInt_fn, Arith P.Testu),
                (PrimVar.word_toIntX_fn, Test P.Copy),
*)
                (PrimVar.word_xorb_fn, mkNumOp P.Pure.XOrb),
              (* real operations *)
                (PrimVar.real_add, mkFltOp P.Pure.FAdd),
                (PrimVar.real_sub, mkFltOp P.Pure.FSub),
                (PrimVar.real_mul, mkFltOp P.Pure.FMul),
                (PrimVar.real_div, mkFltOp P.Pure.FDiv),
                (PrimVar.real_neg, mkFltOp P.Pure.FNeg),
                (PrimVar.real_lt, mkFLt Tgt.realBits),
                (PrimVar.real_lte, mkFLte Tgt.realBits),
                (PrimVar.real_gte, mkFGte Tgt.realBits),
                (PrimVar.real_gt, mkFGt Tgt.realBits),
              (* string operations *)
                (PrimVar.string_lt, Test P.SLt),
                (PrimVar.string_lte, Test P.SLte),
                (PrimVar.string_gte, Test P.SGte),
                (PrimVar.string_gt, Test P.SGt),
                (PrimVar.string_append, Pure P.SAppend),
                (PrimVar.string_implode, Pure P.Implode),
                (PrimVar.string_size, Pure P.StrSize),
                (PrimVar.string_str, Pure P.CharToStr),
                (PrimVar.string_sub, Arith P.StrSub),
              (* ref operation *)
                (PrimVar.ref_ref, Pure P.Ref),
                (PrimVar.ref_assign, Setter P.Assign),
                (PrimVar.ref_deref, Getter P.Deref),
              (* conversion operations *)
                (PrimVar.cvt_floor, Arith(P.Floor{from=Tgt.realBits, to=Tgt.intBits})),
                (PrimVar.cvt_real, Pure(P.IntToReal{from=Tgt.intBits, to=Tgt.realBits})),
              (* predefined I/O operations *)
                (PrimVar.io_print, Setter P.Print),
              (* predefined Math functions *)
                (PrimVar.math_acos, mkMathOp P.Pure.ACos),
                (PrimVar.math_asin, mkMathOp P.Pure.ASin),
                (PrimVar.math_atan, mkMathOp P.Pure.ATan),
                (PrimVar.math_atan2, mkMathOp P.Pure.ATan2),
                (PrimVar.math_cos, mkMathOp P.Pure.Cos),
                (PrimVar.math_exp, mkMathOp P.Pure.Exp),
                (PrimVar.math_ln, mkMathOp P.Pure.Ln),
                (PrimVar.math_pow, mkMathOp P.Pure.Pow),
                (PrimVar.math_sin, mkMathOp P.Pure.Sin),
                (PrimVar.math_sqrt, mkMathOp P.Pure.Sqrt),
                (PrimVar.math_tan, mkMathOp P.Pure.Tan),
              (* other operators *)
(*
                (PrimVar.list_append, Arith P.xxx),
*)
              (* polymorphic equality *)
                (PrimVar.poly_eq, EqTest true),
                (PrimVar.poly_neq, EqTest false)
              ];
            fn x => (case find x
               of SOME rator => rator
                | NONE => NotPrim
              (* end case *))
          end

  end
