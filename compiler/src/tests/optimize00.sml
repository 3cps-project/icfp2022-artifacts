
fun r x = r (x + 1)

val y = r 1

val x = #1 ((fn x => g x, x) y)

(* should optimize to 

val x = g y

*)
