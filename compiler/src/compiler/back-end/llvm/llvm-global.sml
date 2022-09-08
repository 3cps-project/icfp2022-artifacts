(* llvm-global.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *)

structure LLVMGlobal : sig

    type t

  (* define a global with the given type.  Note that globals are identified
   * by name, so two calls to this function with the same string argument
   * should have the same type to avoid problems in the generated LLVM code.
   *)
    val new : string * LLVMType.t -> t

  (* return the name of the global (will include the "@" prefix) *)
    val nameOf : t -> string

  (* return the type of the global *)
    val typeOf : t -> LLVMType.t

  end = struct

    structure Rep = LLVMRep

    datatype t = datatype Rep.global

    fun new (name, ty) = Rep.Glob {
            name = Atom.atom("@" ^ name),
            ty = ty
          }

    fun nameOf (Glob{name, ...}) = Atom.toString name

    fun typeOf (Glob{ty, ...}) = ty

  end
