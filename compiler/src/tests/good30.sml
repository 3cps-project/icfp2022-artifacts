(* good30.sml
 *
 * Test of mutually recursive functions
 *)

fun f x =
    if x = 0
    then x
    else g (x - 1)

and g y =
    if y = 0
    then y
    else f (y - 1)

val res = f 100
