
datatype ('a, 'b) t = in1 of 'a | in2 of 'b

fun g' x = g' x

fun g'' x = g'' x

fun g x = g x

val x = g' (g ((fn x => case x of in1 x1 => (x1, x3) 
                               |  in2 x2 => g'' x) y))

(* should not have nested continuations, i.e.
   should "linearize" the body of val x *)
