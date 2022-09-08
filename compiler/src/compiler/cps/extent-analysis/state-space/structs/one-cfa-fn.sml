(* one-cfa-fn.sml
 *
 * A 1-CFA address allocator.
 *)
functor OneCFAFn (
    structure Var : CPS_VAR
    structure Track : sig
        type t
        val same : t * t -> bool
        val compare : t * t -> order
        val hash : t -> Word.word
        val toString : t -> string
    end
  ) :> ADDR
       where type var = Var.t
       where type info = Track.t
  = struct

    type var = Var.t

    type t = Var.t * Track.t

    type info = Track.t

    fun alloc (x, e) = (x, e)

    fun index _ = raise Fail "AddrProxy.index"
    fun fromIndex _ = raise Fail "AddrProxy.fromIndex"

    fun toString (x, e) = let
          val i = Word.toIntX (Var.hash x)
          val bg = 4
          val fg = i mod 7
          val fg = if fg >= bg then fg+1 else fg
          in
            ANSIText.fmt ({fg=SOME fg, bg=SOME bg, bf=true, ul=true}, (Var.toString x) ^ "/" ^ (Track.toString e))
          end

    fun same ((x1, e1), (x2, e2)) = Var.same (x1, x2) andalso Track.same (e1, e2)
    fun compare ((x1, e1), (x2, e2)) =
        case Var.compare (x1, x2)
         of EQUAL => Track.compare (e1, e2)
          | ord => ord
    (* TODO *)
    fun hash (x, e) = Var.hash x

    structure Key = struct type ord_key = t val compare = compare end
    structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    structure Set = RedBlackSetFn (Key)
    structure Map = RedBlackMapFn (Key)
    structure MSet = MyHashSetFn (HashKey)
    structure Tbl = HashTableFn (HashKey)

end
