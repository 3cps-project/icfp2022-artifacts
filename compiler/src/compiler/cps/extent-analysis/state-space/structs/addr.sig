(* addr.sig
 *
 * The interface to abstract addresses
 *)

signature ADDR =
  sig

    type t
    type var
    type info

    val alloc : var * info -> t

    val toString : t -> string

    val same : (t * t) -> bool
    val compare : t * t -> order
    val hash : t -> word

    val index : t -> word
    val fromIndex : word -> t

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end
