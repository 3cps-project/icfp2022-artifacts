
fun f (x) = let
    val a = 1
    val y = if x
            then 1
            else 2
    val z = if x
            then 3
            else 4
in a + y + z end

val x = f(true) 
