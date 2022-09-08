
fun f x = let
    val g = fn x => 1
    val c = ref g
    fun i j = let
        val h = fn y => j
        val _ = c := h
    in 3 end
    val i2 = i 2
    val k1 = (! c) 0
    val i3 = i 3
    val k2 = (! c) 0
in k1 + k2 end

val x = f 1
