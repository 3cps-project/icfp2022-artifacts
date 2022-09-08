(* cps-ty-var.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSTyVar : sig

    datatype t = TVar of Stamp.t

    val new : unit -> t

    val toString : t -> string

    val same : t * t -> bool
    val compare : t * t -> order
    val hash : t -> word

  (* finite maps on type variables *)
    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t = TVar of Stamp.t

    fun new () = TVar(Stamp.new())

    fun toString (TVar id) = "'" ^ Stamp.toString id

    fun same (TVar id1, TVar id2) = Stamp.same(id1, id2)

    fun compare (TVar a, TVar b) = Stamp.compare(a, b)

    fun hash (TVar a) = Stamp.hash a

    structure Key = struct type ord_key = t val compare = compare end
    structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure Tbl = HashTableFn (HashKey)
                                  

  end
