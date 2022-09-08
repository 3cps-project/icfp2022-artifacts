(* test of curried functions *)

fun exists f xs = let
      fun existsf xs = (case xs
             of [] => false
              | (x::xr) => f x orelse existsf xr
            (* end case *))
      in
        existsf xs
      end

fun compose f g x = f (g x)

val x = exists (fn x => false) [1, 2, 3, 4, 5]
val f = compose (fn x => x) (fn y => y)
