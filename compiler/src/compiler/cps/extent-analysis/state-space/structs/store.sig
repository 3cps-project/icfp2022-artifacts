(* store.sig
 *
 * Signature for abstract stores.
 *)

signature STORE = sig

    type t
    type addr
    type value

    val empty : unit -> t
    val lookup : t * addr -> value
    val find : t * addr -> value option
    val extend : t * addr * value -> t

    val appi : (addr * value -> unit) -> t -> unit
    val foldi : (addr * value * 'a -> 'a) -> 'a -> t -> 'a

    val toString : t -> string

end

