(* string.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Basis Library extensions to List that MLton does not support yet.
 * See https://github.com/SMLFamily/BasisLibrary/wiki/2015-003d-STRING
 *)

signature STRING_EXT =
  sig

    include STRING

    val concatWithMap : string -> ('a -> string) -> 'a list -> string

    val implodeRev : char list -> string

  end

structure StringExt : STRING_EXT =
  struct

    open String

    fun concatWithMap sep fmt xs = let
          fun lp ([], strs) = String.concat(List.rev strs)
            | lp (x::xs, strs) = lp (xs, fmt x :: sep :: strs)
          in
            case xs
             of [] => ""
              | [x] => fmt x
              | x::xr => lp (xr, [fmt x])
            (* end case *)
          end

    fun implodeRev chrs = implode(List.rev chrs)

  end
