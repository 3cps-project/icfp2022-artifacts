(* const-arith.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Glue together the constant arithmetic operations to support
 * trapping signed arithmetic and wrapping unsigned arithemtic.
 *)

structure ConstArith = ConstArithGlueFn (
    structure S = SignedTrappingArith
    structure U = UnsignedWrappingArith
    structure B = BitwiseConstArith
  )
