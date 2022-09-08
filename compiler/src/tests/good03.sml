(* test for pattern-match compilationfrom LeFessant and Maranget *)
datatype t = Nil | One of int | Cons of int * t;

fun f1 arg = (case arg
       of (Nil, a) => 1
        | (b, Nil) => 2
        | (One c, d) => 3
        | (e, One f) => 4
        | (Cons(_, _), Cons(_, _)) => 5
      (* end case *));

val _ = f1(One 5, Nil)
