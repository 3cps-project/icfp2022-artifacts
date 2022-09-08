(* type-class.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Utility functions for dealing with type classes.
 *)

structure TypeClass =
  struct

  (* type classes for overloading *)
    datatype t
      = Any                             (* no constraint *)
      | Int                             (* integer types *)
      | Word                            (* word types *)
      | Real                            (* real types *)
      | Num                             (* integer, word, and real types *)
      | Order                           (* numbers + {char, string} *)

    fun toString Any = "ANY"
      | toString Int = "INT"
      | toString Word = "WORD"
      | toString Real = "REAL"
      | toString Num = "NUM"
      | toString Order = "ORDER"

  end
