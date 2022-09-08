(* label.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Labels for program points.
 *)

structure Label : sig

    type t

    val new : unit -> t

    val toString : t -> string

    val compare : t * t -> order
    val same : t * t -> bool
    val hash : t -> word

    val newFlag : unit -> {getFn : t -> bool, setFn : t * bool -> unit}
    val newProp : (t -> 'a) -> {
            clrFn : t -> unit,
            getFn : t -> 'a,
            peekFn : t -> 'a option,
            setFn : t * 'a -> unit
          }

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t = L of {
        stamp : Stamp.t,
        props : PropList.holder
      }

    fun new () = L{stamp = Stamp.new(), props = PropList.newHolder()}

    fun toString (L{stamp, ...}) = "L" ^ Stamp.toString stamp

    fun compare (L{stamp=a, ...}, L{stamp=b, ...}) = Stamp.compare(a, b)
    fun same (L{stamp=a, ...}, L{stamp=b, ...}) = Stamp.same(a, b)
    fun hash (L{stamp, ...}) = Stamp.hash stamp

    fun newFlag () = PropList.newFlag (fn (L{props, ...}) => props)
    fun newProp initProp = PropList.newProp (fn (L{props, ...}) => props, initProp)

    structure Key =
      struct
        type ord_key = t
        val compare = compare
      end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)

    structure Tbl = HashTableFn (struct
        type hash_key = t
        val hashVal = hash
        val sameKey = same
      end)

  end
