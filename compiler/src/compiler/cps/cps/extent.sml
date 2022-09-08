(* extent.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The representation of variable extents.
 *)

structure Extent : sig

    datatype t = HEAP | STK | REG

  (* returns "^H", "^S", or "^R" *)
    val suffix : t -> string

    val join : t * t -> t

  end = struct

    datatype t = HEAP | STK | REG

    fun suffix HEAP = "^H"
      | suffix STK = "^S"
      | suffix REG = "^R"

    (* We have REG > STK > HEAP, as promotion is an "upwards" motion the lattice *)
    fun join (REG, _) = REG
      | join (_, REG) = REG
      | join (STK, _) = STK
      | join (_, STK) = STK
      | join (HEAP, HEAP) = HEAP

  end
