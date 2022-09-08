(* target.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * A place to collect information about the "target" machine.
 *)

structure Target : sig

  (* the number of bits in the default char type *)
    val charBits : int

  (* the number of bits in the default int/word type *)
    val intBits : int

  (* the number of bits in the default real type *)
    val realBits : int

  end = struct

    val charBits = 8
    val intBits = 63    (* one bit for a tag *)
    val realBits = 64

  end
