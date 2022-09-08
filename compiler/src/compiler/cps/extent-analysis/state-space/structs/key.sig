
signature KEY = sig

    type t

    val same : t * t -> bool
    val compare : t * t -> order
    val hash : t -> word

    val toString : t -> string

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

end

signature GENERAL = sig

    type t

    val compare : t * t -> order
    val toString : t -> string

end
