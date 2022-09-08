(* binding.sml
 *
 * The type of bindings.
 *)

structure Binding = struct

  type t = LVar.t * Addr.t

  fun compare ((x1, a1), (x2, a2)) = 
      LVar.compare (x1, x2)
      (* NOTE:0CFA *)
      (*
      (case LVar.compare (x1, x2)
        of EQUAL => Addr.compare (a1, a2)
         | order => order
      (* end case *))
      *)

  fun toString (x, a) = "|" ^ (LVar.toString x) ^ "." ^ (Addr.toString a) ^ "|"

  local
      structure Key = struct type ord_key = t val compare = compare end
  in
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  end

end
