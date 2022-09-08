(* tak.pml
 *
 *  Sequential Tak function
 *)

structure Takeuchi = struct

  fun tak (x, y, z) = if y < x
        then tak(
             tak(x-1, y, z),
             tak(y-1, z, x),
             tak(z-1, x, y)
           )
        else z

end;

(*
val result = Takeuchi.tak (40, 20, 11);
*)
val result = Takeuchi.tak (10, 5, 11);

