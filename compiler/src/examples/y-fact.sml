(* y-fact.sml
 *
 * Factorial implemented using a "Y" combinator.
 *)

structure Fact = struct

  fun y f x = let
        fun g x = y f x
        in
          f g x
        end;

  fun factY fact n = if n = 0 then 1 else n * fact (n - 1);

  val fact = y factY

end;

val result = (Fact.fact 2) + (Fact.fact 3);
