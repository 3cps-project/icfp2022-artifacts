(* test the handling of non-exahustive bindings and nested patterns in bindings *)
datatype ('a, 'b) t = A of 'a * 'b;

fun f () = let
    val w = 1
    val 1 = w
    val A(A(x, y), z) = A(A(1, 2), 3)
    in
      x+y+z+w
    end
