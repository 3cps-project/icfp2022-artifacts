(* good26.sml
 *
 * Test the treatment of polymorphic bindings.
 *)

val res = let
      val (x, y) = (nil, nil)
      in
        (1 :: x, false :: x) :: y
      end;

val z = (case res of ([a], [b])::_ => a | _ => 2)

