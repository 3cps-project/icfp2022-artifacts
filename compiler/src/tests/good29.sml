(* good29.sml
 *
 * Test of uncurrying and type contraction.
 *)

fun foldl f acc [] = acc
  | foldl f acc (x::xs) = foldl f (f(x, acc)) xs

val res1 = foldl (op +) 0 [1, 2, 3];
val res2 = foldl (op *) 1.0 [1.0, 2.0, 3.0];
val res = real res1 + res2;
