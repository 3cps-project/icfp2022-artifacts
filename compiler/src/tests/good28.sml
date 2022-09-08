(* good28.sml
 *
 * test polymorphic equality
 *)

fun member x [] = false
  | member x (y::ys) = (x = y) orelse member x ys

val res = member 1 [2, 3, 4, 1] orelse member "hi" ["hello", "world"];

