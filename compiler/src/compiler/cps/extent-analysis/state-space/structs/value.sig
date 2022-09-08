(* value-base.sig
 *
 * common base interface to Value and ValueK structures
 *)

signature VALUE_BASE =
  sig

    type t

    val isEmpty : t -> bool

    val join : t * t -> t

    val difference : t * t -> t

    (* val compare : t * t -> order *)

    val toString : t -> string

  (*
    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
*)
  end
