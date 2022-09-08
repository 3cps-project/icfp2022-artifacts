(* id.sml
 *
 * Ids or counters for allocating in the interpreter.
 *)

structure CId (* :> sig

  type t
  val special : t
  val initial : t
  val succ : t -> t

  val toString : t -> string
                          
  val same : (t * t) -> bool
  val compare : t * t -> order
  val hash : t -> word

  structure Set : ORD_SET where type Key.ord_key = t
  structure Map : ORD_MAP where type Key.ord_key = t
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
  structure MSet : HASH_SET where type Key.hash_key = t

end *) = struct

  type t = int

  val special = ~1
  val initial = 0
  fun succ i = i+1

  fun toString i = "id" ^ (Int.toString i)

  fun same (i, j) = i = j

  fun compare (i, j) = Int.compare (i, j)
  fun hash i = Word.fromInt i

  structure Key = struct type ord_key = t val compare = compare end
  structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure Tbl = HashTableFn (HashKey)
  structure MSet = HashSetFn (HashKey)

end
