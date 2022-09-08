(* prim-eval.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Evaluation functions that implement the arithmetic primop
 * semantics.  We put these here to localize the implementation
 * across multiple interpreters and optimizers.
 *
 * Assumptions:
 *    - integers and words are represented by IntInf.int
 *    - numeric precisions are represented as int values
 *    - the division/modulo operators are never called with a zero divisor
 *    - reals are represented by Real.real
 *)

structure PrimEval : sig

  (* this exception is raised when an argument is invalid in a way
   * that is incorrect for the IR semantics.
   *)
    exception Domain of string

  (* represents the size of arguments in bits *)
    type prec = int

  (* pure operations; these do not raise exceptions *)
    val uadd : prec * IntInf.int * IntInf.int -> IntInf.int
    val usub : prec * IntInf.int * IntInf.int -> IntInf.int
    val umul : prec * IntInf.int * IntInf.int -> IntInf.int
    val udiv : prec * IntInf.int * IntInf.int -> IntInf.int
    val umod : prec * IntInf.int * IntInf.int -> IntInf.int
    val uneg : prec * IntInf.int -> IntInf.int
    val andb : prec * IntInf.int * IntInf.int -> IntInf.int
    val orb  : prec * IntInf.int * IntInf.int -> IntInf.int
    val xorb : prec * IntInf.int * IntInf.int -> IntInf.int
    val notb : prec * IntInf.int -> IntInf.int
    val lshift : prec * IntInf.int * IntInf.int -> IntInf.int
    val rshift : prec * IntInf.int * IntInf.int -> IntInf.int
    val rshiftl : prec * IntInf.int * IntInf.int -> IntInf.int
    val fadd : prec * real * real -> real
    val fsub : prec * real * real -> real
    val fmul : prec * real * real -> real
    val fdiv : prec * real * real -> real
    val fneg : prec * real -> real
    val iiadd : IntInf.int * IntInf.int -> IntInf.int
    val iisub : IntInf.int * IntInf.int -> IntInf.int
    val iimul : IntInf.int * IntInf.int -> IntInf.int
    val iineg : IntInf.int -> IntInf.int
    val zext : {from : prec, to : prec} * IntInf.int -> IntInf.int
    val sext : {from : prec, to : prec} * IntInf.int -> IntInf.int
    val trunc : {from : prec, to : prec} * IntInf.int -> IntInf.int
    val int2real : {from : prec, to : prec} * IntInf.int -> real

  (* trapping arithmetic operations; these raise Overflow when the
   * result is too large for the specified precision.
   *)
    val iadd : prec * IntInf.int * IntInf.int -> IntInf.int
    val isub : prec * IntInf.int * IntInf.int -> IntInf.int
    val imul : prec * IntInf.int * IntInf.int -> IntInf.int
    val idiv : prec * IntInf.int * IntInf.int -> IntInf.int
    val imod : prec * IntInf.int * IntInf.int -> IntInf.int
    val iquot : prec * IntInf.int * IntInf.int -> IntInf.int
    val irem : prec * IntInf.int * IntInf.int -> IntInf.int
    val ineg : prec * IntInf.int -> IntInf.int
    val floor : {from : prec, to : prec} * real -> IntInf.int

  (* comparisons *)
    val ult : prec * IntInf.int * IntInf.int -> bool
    val ule : prec * IntInf.int * IntInf.int -> bool
    val uge : prec * IntInf.int * IntInf.int -> bool
    val ugt : prec * IntInf.int * IntInf.int -> bool
    val ilt : prec * IntInf.int * IntInf.int -> bool
    val ile : prec * IntInf.int * IntInf.int -> bool
    val ige : prec * IntInf.int * IntInf.int -> bool
    val igt : prec * IntInf.int * IntInf.int -> bool
    val flt : prec * real * real -> bool
    val fle : prec * real * real -> bool
    val fge : prec * real * real -> bool
    val fgt : prec * real * real -> bool
    val feq : prec * real * real -> bool
    val fne : prec * real * real -> bool

  end = struct

    structure CA = ConstArith

    exception Domain of string

  (* represents the size of arguments in bits *)
    type prec = int

    fun pow2 w = IntInf.<<(1, Word.fromInt w)

  (* pure operations; these do not raise exceptions *)
    val uadd = CA.uAdd
    val usub = CA.uSub
    val umul = CA.uMul
    fun udiv (_, 0, _) = raise Domain "udiv by zero"
      | udiv (sz, a, b) = CA.uDiv(sz, a, b)
    fun umod (_, 0, _) = raise Domain "umod by zero"
      | umod (sz, a, b) = CA.uMod(sz, a, b)
    val uneg = CA.uNeg
    val andb = CA.bAnd
    val orb = CA.bOr
    val xorb = CA.bXor
    val notb = CA.bNot
    val lshift = CA.uShL
    val rshift = CA.sShR
    val rshiftl = CA.uShR
(* since we only have 64-bit reals, we just do the arithmetic w/o
 * checking the precision
 *)
    fun fadd (_, a, b) = Real.+(a, b)
    fun fsub (_, a, b) = Real.-(a, b)
    fun fmul (_, a, b) = Real.*(a, b)
    fun fdiv (_, a, b) = Real./(a, b)
    fun fneg (_, a) = Real.~ a
    val iiadd = IntInf.+
    val iisub = IntInf.-
    val iimul = IntInf.*
    val iineg = IntInf.~
    fun zext ({from, to}, a) =
	  if (to < from)
	    then raise Domain "zext"
	  else if (from = to) orelse (a >= 0)
	    then a
	    else CA.uNarrow(from, a)
    fun sext ({from, to}, a) =
	  if (to < from)
	    then raise Domain "sext"
	  else if (from = to) orelse (a < 0)
	    then a
	    else CA.toSigned (from, a)
    fun trunc ({from, to}, a) = if (to < from)
	  then raise Domain "trunc"
	  else CA.toUnsigned (to, a)
    fun int2real ({from, to}, a) = Real.fromLargeInt a

  (* trapping arithmetic operations; these raise Overflow when the
   * result is too large for the specified precision.
   *)
    val iadd = CA.sAdd
    val isub = CA.sSub
    val imul = CA.sMul
    fun idiv (_, 0, _) = raise Domain "idiv by zero"
      | idiv (sz, a, b) = CA.sDiv(sz, a, b)
    fun imod (_, 0, _) = raise Domain "imod by zero"
      | imod (sz, a, b) = CA.sMod(sz, a, b)
    fun iquot (_, 0, _) = raise Domain "iquot by zero"
      | iquot (sz, a, b) = CA.sQuot(sz, a, b)
    fun irem (_, 0, _) = raise Domain "irem by zero"
      | irem (sz, a, b) = CA.sRem(sz, a, b)
    val ineg = CA.sNeg
    fun floor ({from, to}, x) = let
	  val n = Real.toLargeInt IEEEReal.TO_NEGINF x
	  in
	    CA.sNarrow(to, n)
	  end

  (* comparisons *)
    val ult = CA.uLess
    val ule = CA.uLessEq
    fun uge (sz, a, b) = CA.uLessEq(sz, b, a)
    fun ugt (sz, a, b) = CA.uLess(sz, b, a)
    fun ilt (_, a, b) = IntInf.<(a, b)
    fun ile (_, a, b) = IntInf.<=(a, b)
    fun ige (_, a, b) = IntInf.>=(a, b)
    fun igt (_, a, b) = IntInf.>(a, b)
    fun flt (_, a, b) = Real.<(a, b)
    fun fle (_, a, b) = Real.<=(a, b)
    fun fge (_, a, b) = Real.>=(a, b)
    fun fgt (_, a, b) = Real.>(a, b)
    fun feq (_, a, b) = Real.==(a, b)
    fun fne (_, a, b) = Real.!=(a, b)

  end
