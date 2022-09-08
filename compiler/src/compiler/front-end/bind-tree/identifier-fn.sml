(* identifier-fn.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Functor for generating unique classes of identifiers.
 *)

functor IdentifierFn () : sig

    type t

  (* define a new variable that is bound at the specified location.  Use use UNKNOWN
   * for externally defined identifiers.
   *)
    val new : Atom.atom * Error.location -> t

    val nameOf : t -> string
    val toString : t -> string

    val locOf : t -> Error.location

    val compare : t * t -> order
    val same : t * t -> bool

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t

  end = struct

    datatype t = ID of {
        name : string,
        stamp : Stamp.t,
        loc : Error.location
      }

    fun new (name, loc) = ID{name = Atom.toString name, stamp = Stamp.new(), loc = loc}

    fun nameOf (ID{name, ...}) = name

    fun toString (ID{name, stamp, ...}) = name ^ Stamp.toString stamp

    fun locOf (ID{loc, ...}) = loc

    fun compare (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = Stamp.compare(id1, id2)

    fun same (ID{stamp = id1, ...}, ID{stamp = id2, ...}) = Stamp.same(id1, id2)

    structure Set = RedBlackSetFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Map = RedBlackMapFn (
      struct
        type ord_key = t
        val compare = compare
      end)

  end
