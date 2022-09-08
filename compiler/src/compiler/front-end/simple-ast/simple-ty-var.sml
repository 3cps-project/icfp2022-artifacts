(* simple-ty-var.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure SimpleTyVar : sig

    type t = SimpleTypes.tyvar

  (* create a new type variable *)
    val new : unit -> SimpleTypes.tyvar

  (* unique string representation of type variable *)
    val toString : SimpleTypes.tyvar -> string

  (* return true if two type variables are the same (i.e., have the same stamp) *)
    val same : SimpleTypes.tyvar * SimpleTypes.tyvar -> bool

  (* finite sets and maps on type variables *)
    structure Set : ORD_SET where type Key.ord_key = SimpleTypes.tyvar
    structure Map : ORD_MAP where type Key.ord_key = SimpleTypes.tyvar

  end = struct

    datatype t = datatype SimpleTypes.tyvar

    fun new () = TVar(Stamp.new())

    fun toString (TVar stamp) = "'tv" ^ Stamp.toString stamp

    fun same (TVar a, TVar b) = Stamp.same(a, b)
    fun compare (TVar a, TVar b) = Stamp.compare(a, b)

    structure Map = RedBlackMapFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Set = RedBlackSetFn (
      struct
        type ord_key = t
        val compare = compare
      end)

  end
