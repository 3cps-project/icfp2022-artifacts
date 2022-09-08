
fun f x = let
    val a = 1
    val b = 2
    val g = fn x => a
    val h = fn y => b
    val c = ref g
    val _ = c := h
in !c end

val x = (f 1) 3
