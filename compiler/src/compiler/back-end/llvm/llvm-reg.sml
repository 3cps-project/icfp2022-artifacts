(* llvm-reg.sml
 *
 * COPYRIGHT (c) 2016 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure LLVMReg : sig

    type t

    val newNamed : string * LLVMType.t -> t

    val new : LLVMType.t -> t

    val typeOf : t -> LLVMType.t

    val toString : t -> string

  end = struct

    structure Rep = LLVMRep

    datatype t = datatype Rep.reg

    val cnt = ref 1

    fun newNamed (name, ty) = let
          val id = !cnt
          in
            cnt := id + 1;
            Reg{name = name, ty = ty, id = id}
          end

  (* we need the "r" prefix to avoid the requirement that registers be defined in
   * numeric order.
   *)
    fun new ty = newNamed ("r", ty)

    fun typeOf (Reg{ty, ...}) = ty

    fun toString (Reg{name, id, ...}) = concat["%", name, Int.toString id]

  end
