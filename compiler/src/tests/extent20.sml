exception Break of int -> int

fun f (x : int) : int = let
    fun g (y : int) = x
in raise Break g end

val k = f 1 handle Break h => h 2
