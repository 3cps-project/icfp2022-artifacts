(* good21.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Test analysis with mutual recursive functions
 *)

fun f x y z = if (x < y) then g (x+1) z y else y+z

and g a b c = let
  val w = f (a-1) (2*b) c
  in
    if (w < a) then b else c
  end;

val result = f 1 2 3;
