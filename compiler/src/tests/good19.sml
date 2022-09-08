datatype s_tree
  = Leaf of string
  | Interior of string * s_tree * s_tree;

fun append (l1, l2) = (case l1 of [] => l2 | (x::xs) => x :: append(xs, l2))

fun leaves t =
     (case t
       of Leaf s => t::nil
(*
        | Interior (s, t1, t2) => leaves t1 @ leaves t2
*)
        | Interior (s, t1, t2) => append(leaves t1, leaves t2)
     (* end case *));

fun max (a, b) = if b < a then a else b;

fun height t =
     (case t
       of Leaf _ => 1
        | Interior (_, t1, t2) => 1 + max (height t1, height t2)
     (* end case *));

fun allStrings t =
     (case t
       of Leaf s => [s]
        | Interior (s, t1, t2) => s :: append(allStrings t1, allStrings t2)
(*
        | Interior (s, t1, t2) => s :: allStrings t1 @ allStrings t2
*)
     (* end case *));

val noms = Interior ("Arthur",
                     Leaf "Bud",
                     Interior ("Cab",
                               Interior ("Donald",
                                         Leaf "Ennis",
                                         Leaf "Fenwick"),
                               Leaf "Guy"));

val _ = "tree"
