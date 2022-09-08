(* frame.sml
 *
 * A frame type for the interpreter to track allocations.
 *)

structure Frame :> sig

  type t

  val make : Label.t * CId.t -> t
                 
  val toString : t -> string
  val compare : t * t -> order
  val label : t -> Label.t
  val same : t * t -> bool
  val hash : t -> word
                          
  structure Set : ORD_SET where type Key.ord_key = t
  structure Map : ORD_MAP where type Key.ord_key = t
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

end = struct

  datatype t = Frame of Label.t * CId.t

  fun make (lab, id) = Frame (lab, id)
  fun label (Frame (lab, _)) = lab
                              
  fun toString (Frame (lab, _)) = "frm over " ^ (Label.toString lab)
  fun compare (Frame (_, id1), Frame (_, id2)) = CId.compare (id1, id2)
  fun same (Frame (_, id1), Frame (_, id2)) = CId.same (id1, id2)
  fun hash (Frame (_, id)) = CId.hash id

  structure Key = struct type ord_key = t val compare = compare end
                      
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure Tbl = HashTableFn (struct
                                type hash_key = t
                                val hashVal = hash
                                val sameKey = same
                                end)
   
end

