exception Break of int -> int

fun f (x : int) : int = let
    fun g (y : int) : int = let
        val w = (fn (v : int) => x)
    in raise Break w end
    val z = g 2
in z + 3 end

val k = f 1 handle Break h => h 2
