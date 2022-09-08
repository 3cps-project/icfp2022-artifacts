(* good30.sml
 *
 * Test of argument flattening
 *)

fun f (x, y) =
    (x + 1, y + 1)

val (a, b) = f (1, 2)
val (c, d) = f (a, b)
