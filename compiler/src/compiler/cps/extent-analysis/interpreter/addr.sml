(* addr.sml
 *
 * The concrete address modules.
 *)

(* The interface to concrete addresses *)
signature CADDR =
  sig

    type t

    val alloc : CId.t -> t
    val id : t -> CId.t

    val toString : t -> string

    val same : (t * t) -> bool
    val compare : t * t -> order
    val hash : t -> word

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end

(* concrete addresses 
   contain the function level that they were created in *)
functor CIdFn () :> CADDR =
  struct

  type t = CId.t
                     
  fun id (id) = id
     
  fun alloc (id) = (id)
                         
  fun same (id1, id2) = CId.same (id1, id2)
  fun compare (id1, id2) = CId.compare (id1, id2)
  fun hash (id) = CId.hash id
                                 
  structure Key = struct type ord_key = t val compare = compare end
                      
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure Tbl = HashTableFn (struct
                                type hash_key = t
                                val hashVal = hash
                                val sameKey = same
                                end)
                              
  fun toString (a as (x)) = let
      val i = Word.toIntX (hash a)
      val bg = 4
      val fg = i mod 7
      val fg = if fg >= bg then fg+1 else fg
  in
      (* ANSIText.fmt ({fg=SOME fg, bg=SOME bg, bf=true, ul=true}, Int.toString i) *)
      "{" ^ (CId.toString x) ^ "}"
  end
                                     
end

(*
(* concrete addresses 
   contain the function level that they were created in *)
functor CIdFn () : CADDR =
  struct

  open CId

  fun level _ = Level.halt
  fun id id = id
     
  fun alloc (id, lev) = id
                         
end
*)      

structure CAddr :> CADDR = CIdFn()
structure CAddrK :> CADDR = CIdFn()

