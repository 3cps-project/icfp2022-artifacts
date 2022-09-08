(* struct-sig.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure StructSig : sig

    type t

  end = struct

    datatype t = StrSig of {
        imports :
        exports :
      }

  end
