(* simple-exn.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Support for the `exn` type.
 *)

structure SimpleExn : sig

  (* the exception type *)
    val tyc : SimpleTypes.tycon

  (* create a new exception constructor. *)
    val new : (string * SimpleTypes.ty option) -> SimpleTypes.dcon

  (* is this dcon an exception constructor? *)
    val isExn : SimpleTypes.dcon -> bool

  end = struct

  (* we use an abstract type constructor to represent the exception type *)
    val tyc = SimpleTyCon.newAbsTyc ("exn", [])

    fun new (name, argTy) = SimpleTypes.DCon{
            stamp = Stamp.new(),
            name = name,
            owner = tyc,
            argTy = argTy,
            props = PropList.newHolder()
          }

    fun isExn (SimpleTypes.DCon{owner, ...}) = SimpleTyCon.same(owner, tyc)

  end
