(* safe-space.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * This is an example from the "Efficient and Safe-for-Space Closure
 * Conversion" paper by Zhong Shao and Andrew Appel (TOPLAS 2000).
 *)

exception Empty

fun hd l = (case l of [] => raise Empty | x::_ => x)

val N = 10000

fun f (v, w, x, y, z) = let
      fun g () = let
            val u = hd v
            fun h () = let
                  fun i () = w+x+y+z+3
                  in
                    (i, u)
                  end
            in
              h
            end
      in
        g
      end;

fun big n = if n < 1 then nil else n :: big(n-1);

fun loop (n, res) =
      if (n < 1)
        then res
        else let
          val s = f (big N, 0, 0, 0, 0) ()
          in
            loop (n-1, s::res)
          end

(*
val result = loop (N, [])
*)
val result = loop (5, [])

