(* good25.sml
 *
 *)

structure Main =
  struct

    datatype t = A | B

    fun f x = (case x
           of (A, A, _, _, _, _, _, _, _, _) => 0
            | (_, _, A, A, _, _, _, _, _, _) => 1
            | (_, _, _, _, A, A, _, _, _, _) => 2
            | (_, _, _, _, _, _, A, A, _, _) => 3
            | (_, _, _, _, _, _, _, _, A, A) => 4
            | (A, B, A, B, A, B, A, B, A, B) => ~1
          (* end case *))

  end

