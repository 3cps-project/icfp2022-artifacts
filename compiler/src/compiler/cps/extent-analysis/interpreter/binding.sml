(* binding.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Concrete bindings.
 *)

structure CBinding =
struct

  type t = LVar.t * CAddr.t
                        
  fun compare ((x, a), (y, b)) =
      (case LVar.compare (x, y)
        of EQUAL => CAddr.compare (a, b)
         | order => order
      (* end case *))
          
  fun same ((x, a), (y, b)) = LVar.same (x, y) andalso CAddr.same (a, b)
  fun hash (x, a) = CAddr.hash a

  local
      structure Key = struct type ord_key = t val compare = compare end
  in
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure Tbl = HashTableFn (struct
                                type hash_key = t
                                val hashVal = hash
                                val sameKey = same
                                end)
  end
  
  fun toString (x, a) = "{" ^ (LVar.toString x) ^ "," ^ (CAddr.toString a) ^ "}"
                                                                                 
end

