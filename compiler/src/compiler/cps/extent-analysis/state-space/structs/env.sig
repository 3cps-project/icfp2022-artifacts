(* env.sig
 *
 * Abstract environment signature.
 *)

signature ENV =
  sig

    type t
    type var
    type addr

    val empty : t

    val toString : t -> string

    val lookup : t * var -> addr
    val find : t * var -> addr option
    val extend : t * var * addr -> t

    val foldli : (var * addr * 'a -> 'a) -> 'a -> t -> 'a

    val compare : t * t -> order
    val same : t * t -> bool
    val hash : t -> word

  end

