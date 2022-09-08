(* literal.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Literal values.
 *)

structure Literal : sig

    datatype t
      = Int of IntegerLit.t             (* Int literals *)
      | Word of WordLit.t               (* Word (unsigned integer) literals *)
      | Real of FloatLit.t              (* Real literals *)
      | Char of char                    (* Character literals *)
      | String of string                (* uses UTF8 encoding *)

    val toString : t -> string

    val same : (t * t) -> bool
    val compare : (t * t) -> order
    val hash : t -> word

    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t
      = Int of IntegerLit.t             (* Int literals *)
      | Word of WordLit.t               (* Word (unsigned integer) literals *)
      | Real of FloatLit.t              (* Real literals *)
      | Char of char                    (* Character literals *)
      | String of string                (* uses UTF8 encoding *)

    fun toString (Int i) = IntegerLit.toString i
      | toString (Word i) = WordLit.toString i
      | toString (Real flt) = FloatLit.toString flt
      | toString (Char c) = concat["#\"", Char.toString c, "\""]
      | toString (String s) = concat["\"", String.toString s, "\""]

    fun same (Int i1, Int i2) = IntegerLit.same(i1, i2)
      | same (Word w1, Word w2) = WordLit.same(w1, w2)
      | same (Real f1, Real f2) = FloatLit.same(f1, f2)
      | same (Char c1, Char c2) = (c1 = c2)
      | same (String s1, String s2) = (s1 = s2)
      | same _ = false

    fun compare (Int i1, Int i2) = IntegerLit.compare(i1, i2)
      | compare (Word w1, Word w2) = WordLit.compare(w1, w2)
      | compare (Real f1, Real f2) = FloatLit.compare(f1, f2)
      | compare (Char c1, Char c2) = Char.compare(c1, c2)
      | compare (String s1, String s2) = String.compare(s1, s2)
      | compare (Int _, _) = LESS
      | compare (_, Int _) = GREATER
      | compare (Word _, _) = LESS
      | compare (_, Word _) = GREATER
      | compare (Real _, _) = LESS
      | compare (_, Real _) = GREATER
      | compare (Char _, _) = LESS
      | compare (_, Char _) = GREATER

  (* for hash codes, use the low-order 4 bits for a type code *)
    local
      val intCd = 0w5
      val wordCd = 0w7
      val realCd = 0w11
      val charCd = 0w13
      val stringCd = 0w17
      fun h (hash, base) = Word.<<(hash, 0w4) + base
    in
    fun hash (Int i) = h(IntegerLit.hash i, intCd)
      | hash (Word w) = h(IntegerLit.hash w, wordCd)
      | hash (Real f) = h(FloatLit.hash f, realCd)
      | hash (Char c) = h(Word.fromInt(ord c), charCd)
      | hash (String s) = h(HashString.hashString s, stringCd)
    end (* local *)

    structure Tbl = HashTableFn (
      struct
        type hash_key = t
        val hashVal = hash
        val sameKey = same
      end)

  end
