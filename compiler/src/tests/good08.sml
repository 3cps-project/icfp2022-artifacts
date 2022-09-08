(* good08.sml *)

fun map f xs = (case xs
       of [] => []
        | x::xr => f x :: map f xr
      (* end case *));

val xs = map sqrt [1.0, 2.0, 3.0];

