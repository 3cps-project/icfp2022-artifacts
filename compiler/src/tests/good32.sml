(* good32.sml
 *
 * Test of polymorphism
 *)

fun h (f : 'a -> 'b, x : 'a) =
    f x

fun g (f : 'a -> 'b, x : 'a) =
    h (h, (f, x))

val f = h

val x = g (fn x => (fn y => y, x), 1)
val y = g (fn x => x, 1)
