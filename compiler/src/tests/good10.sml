(* good10.sml
 *
 * test exceptions
 *)

exception Foo

fun prod xs = let
      fun lp xs = (case xs of [] => 1 | 0::_ => raise Foo | x::xr => x * lp xr)
      in
        lp xs handle _ => 0
      end;

val result1 = prod [1, 2, 3, 4];

val result2 = prod [1, 2, 0, 4];

val result = result1 + result2
