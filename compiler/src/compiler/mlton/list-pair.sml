(* list-pair.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Basis Library extensions to ListPair that MLton does not support yet.
 * See https://github.com/SMLFamily/BasisLibrary/wiki/2015-003c-ListPair
 *)

signature LIST_PAIR_EXT =
  sig

    include LIST_PAIR

    val appiEq : (int * 'a * 'b -> unit) -> 'a list * 'b list -> unit

  end

structure ListPairExt : LIST_PAIR_EXT =
  struct

    open ListPair

    fun appiEq f (xs, ys) = let
          fun appf (_, [], []) = ()
            | appf (i, x::xr, y::yr) = (
                f (i, x, y);
                appf (i+1, xr, yr))
            | appf _ = raise UnequalLengths
          in
            appf (0, xs, ys)
          end

  end
