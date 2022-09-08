(* good32.sml
 *
 * Test of polymorphism in data structures
 *)


datatype 'a t = A of 'a * ('a t) | B 

fun f (x : 'a) (y : 'b) = x

fun g n =
    if n = 0
    then B
    else A (f n, g (n - 1))
           
fun h (x : 'a) =
    A (f x, B)

val x = f f
val y = h f
