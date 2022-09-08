(* good22.sml
 *
 * test of implcitly bound type variables.
 *)

fun app (f : 'a -> unit) xs = let
      fun appf [] = ()
        | appf (x::xr) = (f x; appf xr)
      in
        appf xs
      end

val _ = app print ["abc", "def"];

