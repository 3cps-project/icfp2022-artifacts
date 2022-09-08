(* word-lit.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Word literals.
 *)

structure WordLit :> sig

    type t = IntInf.int

  (* equality, comparisons, and hashing functions *)
    val same : (t * t) -> bool
    val compare : (t * t) -> order
    val hash : t -> word

    val toString : t -> string

  end = struct

    type t = IntInf.int

  (* equality, comparisons, and hashing functions *)
    fun same (a : t, b) = (a = b)
    val compare = IntInf.compare
    fun hash i = Word.fromInt(IntInf.toInt(IntInf.andb(i, 0xfffffff)))

    fun toString i = "0wx" ^ IntInf.fmt StringCvt.HEX i

  end
