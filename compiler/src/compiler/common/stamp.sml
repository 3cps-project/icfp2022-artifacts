(* stamp.sml
 *
 * COPYRIGHT (c) 2016 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Stamps are locally unique identifiers used in the compiler to
 * distinguish different types, variables, etc.  For a given compilation,
 * the stamp assigned to an object is guaranteed to be unique, although
 * an object may have different stamps assigned to it in different compiles.
 *)

structure Stamp :> sig

    type t

    val new : unit -> t

    val same : (t * t) -> bool
    val compare : (t * t) -> order
    val hash : t -> word

    val toString : t -> string

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    structure W = Word

    datatype t = STAMP of {
        id : Word.word
      }

    val cnt = ref 0w0

    fun new () = let val w = !cnt in cnt := w+0w1; STAMP{id = w} end

    fun same (STAMP{id, ...}, STAMP{id=id', ...}) = (id = id')
    fun compare (STAMP{id, ...}, STAMP{id=id', ...}) = W.compare(id, id')
    fun hash (STAMP{id, ...}) = id

    fun toString (STAMP{id, ...}) = StringCvt.padLeft #"0" 4 (W.toString id)

    structure Key =
      struct
        type ord_key = t
        val compare = compare
      end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)

    structure Tbl = HashTableFn (struct
        type hash_key = t
        val hashVal = hash
        val sameKey = same
      end)

  end
