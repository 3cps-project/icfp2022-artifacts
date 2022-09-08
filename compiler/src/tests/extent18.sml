
(* This example can help simulate cross-module compilation since we have a function that can leave the compilation context *)

exception Break of int -> int

fun f (x : int, w : int) : int = let
    fun g (y : int) = let
        fun h (z : int) : int =
            raise Break (fn _ => w)
    in h y end
    fun a (b : int) = x
    val c = g 1
    val d = g 2
    val e = a 3
in a 10 end

val aaa = f (11, 12)
val bbb = f (13, 14)
