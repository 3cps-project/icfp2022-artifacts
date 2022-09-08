(* TODO
 *
 *)

signature HASH_CONS_BASE = sig
    type t
    val same : t * t -> bool
    val hash : t -> word
    val toString : t -> string
end

signature HASH_CONS_SIG = sig

  structure B : HASH_CONS_BASE

  type t
  val get : t -> B.t
  val index : t -> word
  val fromIndex : word -> t
  val make : B.t -> t
  val reset : unit -> unit

  val toString : t -> string

  val compare : t * t -> order
  val same : t * t -> bool
  val hash : t -> word

  structure Set : ORD_SET where type Key.ord_key = t
  structure Map : ORD_MAP where type Key.ord_key = t
  structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t
  structure MSet : MY_MONO_HASH_SET where type Key.hash_key = t
end 

functor MyHashCons (structure Base : HASH_CONS_BASE) : HASH_CONS_SIG = struct

  structure B = Base

  type t = word

  structure BaseTbl = HashTableFn (struct type hash_key = Base.t val hashVal = Base.hash val sameKey = Base.same end)

  val current_index : word ref = ref (Word.fromInt 0)
  val index_tbl : word BaseTbl.hash_table = BaseTbl.mkTable (100, Fail "MyHashCons.index_tbl")
  val lookup_tbl : Base.t WordHashTable.hash_table = WordHashTable.mkTable (100, Fail "MyHashCons.lookup_tbl")

  fun make base =
      case BaseTbl.find index_tbl base
       of SOME n => n
        | NONE => let
            val n = ! current_index
        in
            current_index := Word.+ (n, Word.fromInt 1);
            BaseTbl.insert index_tbl (base, n);
            WordHashTable.insert lookup_tbl (n, base);
            n
        end

  fun index n = n
  fun fromIndex n = n

  fun get n =
      WordHashTable.lookup lookup_tbl n

  fun reset () = let
  in current_index := (Word.fromInt 0);
     BaseTbl.clear index_tbl;
     WordHashTable.clear lookup_tbl;
     ()
  end

  val compare = Word.compare
  fun same (n1 : word, n2 : word) = (n1 = n2)
  fun hash (n : word) = n

  structure Map = WordRedBlackMap
  structure Set = WordRedBlackSet
  structure Tbl = WordHashTable
  (* FIXME *)
  structure MSet = MyHashSetFn (struct type hash_key = t fun sameKey (a : word, b : word) = (a = b) fun hashVal (word : word) = word end)

  fun toString n = Base.toString (get n)

end

functor MyHashCons4 (structure Base : HASH_CONS_BASE) : HASH_CONS_SIG = struct

  structure B = Base

  type t = word * Base.t

  structure BaseTbl = HashTableFn (struct type hash_key = Base.t val hashVal = Base.hash val sameKey = Base.same end)

  val current_index : word ref = ref (Word.fromInt 0)
  val index_tbl : word BaseTbl.hash_table = BaseTbl.mkTable (100, Fail "MyHashCons.index_tbl")

  fun make base =
      case BaseTbl.find index_tbl base
       of SOME n => (n, base)
        | NONE => let
            val n = ! current_index
        in
            current_index := Word.+ (n, Word.fromInt 1);
            BaseTbl.insert index_tbl (base, n);
            (n, base)
        end

  fun index (n, base) = n
  fun fromIndex _ = raise Fail "MyHashCons.fromIndex"

  fun get (n, base) = base

  fun reset () = let
  in current_index := (Word.fromInt 0);
     BaseTbl.clear index_tbl;
     ()
  end

  fun compare ((n1, _), (n2, _)) = Word.compare (n1, n2)
  fun same ((n1 : word, _), (n2 : word, _)) = (n1 = n2)
  fun hash (n, _) = n
                                                
  structure Key = struct type ord_key = t val compare = compare end
  structure HashKey = struct type hash_key = t
                             fun sameKey (a1, a2) =
                                 case compare (a1, a2) of EQUAL => true | _ => false 
                             fun hashVal (n, base) = n end
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure Tbl = HashTableFn (HashKey)
  (* FIXME *)
  structure MSet = MyHashSetFn (struct type hash_key = t fun sameKey ((a : word, _), (b : word, _)) = (a = b) fun hashVal (word : word, _) = word end)

  fun toString (n, base) = Base.toString base

end
(*
functor MyHashCons2 (structure Base : HASH_CONS_BASE) : HASH_CONS_SIG = struct

  structure B = Base

  type t = Base.t HashCons.obj

  val tbl = HashCons.new {eq = Base.same}

  fun reset () = HashCons.clear tbl

  fun make n = HashCons.cons0 tbl (Base.hash n, n)

  val index = HashCons.tag
  fun fromIndex _ = raise Fail "MyHashCons.fromIndex"

  val get = HashCons.node

  val compare = HashCons.compare
  val same = HashCons.same
  fun hash ({nd, tag, hash} : t) = hash

  structure Key = struct type ord_key = t val compare = compare end
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  structure HashKey = struct type hash_key = t
                             fun sameKey (a1, a2) =
                                 case compare (a1, a2) of EQUAL => true | _ => false 
                             val hashVal = index end
  structure Tbl = HashTableFn (HashKey)

  fun toString n = Base.toString (get n)

end

functor MyHashCons3 (structure Base : HASH_CONS_BASE) : HASH_CONS_SIG = struct

  structure B = Base

  type t = word

  val tbl = HashCons.new {eq = Base.same}
  val nd_tbl : Base.t WordHashTable.hash_table = WordHashTable.mkTable (100, Fail "MyHashCons.nd_tbl")

  fun reset () = (HashCons.clear tbl; WordHashTable.clear nd_tbl)

  fun make n = let
      val {tag, nd, hash} = HashCons.cons0 tbl (Base.hash n, n)
  in WordHashTable.insert nd_tbl (tag, nd);
     tag
  end

  fun index tag = tag
  fun fromIndex tag = tag 

  fun get tag = WordHashTable.lookup nd_tbl tag

  fun toString n = Base.toString (get n)

  val compare = Word.compare
  fun same (n1 : word, n2 : word) = (n1 = n2)
  fun hash n = n

  structure Map = WordRedBlackMap
  structure Set = WordRedBlackSet
  structure Tbl = WordHashTable

end
*)
