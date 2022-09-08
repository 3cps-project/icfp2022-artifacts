
val x = let
    fun f x y = x
    val a = f 1
    val b = f 2
    val c = a 3
    val d = b 4
in c + d end
              
