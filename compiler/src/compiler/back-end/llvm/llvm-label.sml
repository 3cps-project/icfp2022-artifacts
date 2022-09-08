(* llvm-label.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *)

structure LLVMLabel : sig

    type t

  (* generated a new label *)
    val new : string -> t

  (* return the label's name (does not include "%" prefix) *)
    val nameOf : t -> string

  end = struct

    structure Rep = LLVMRep

    datatype t = datatype Rep.label

    fun new name = Rep.Lab{name = name, id = Stamp.new()}

    fun nameOf (Rep.Lab{name, id}) = concat[name, "_", Stamp.toString id]

  end
