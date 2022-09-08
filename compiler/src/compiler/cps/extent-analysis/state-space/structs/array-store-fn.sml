(* array-store-fn.sml
 *
 * Functor for creating abstract store with arrays using the unique
 * hash-cons tags from addresses. Automatically resizes the store if 
 * an address outside of the range is given.
 * Provides extremely fast lookup.
 *)

(* Arraylist implementation of a store *)
functor ArrayStoreFn (
    structure Addr : ADDR
    structure Value : VALUE_BASE
  ) : STORE where type addr = Addr.t 
              and type value = Value.t
= struct

  type t = ((Value.t option) Array.array) ref
  type addr = Addr.t
  type value = Value.t

  fun empty () = ref (Array.array (100, NONE))

  fun resize (needSize, store) = let
      val arr = ! store
      val size = Array.length arr
      val new_size = Int.max (needSize + 1, size * 2)
      val new_arr = Array.array (new_size, NONE)
  in Array.copy {src = arr, dst = new_arr, di = 0};
     store := new_arr
  end

  fun lookup (store, a) = let
      val index = Word.toInt (Addr.index a)
  in case Array.sub (! store, index)
      of SOME d => d
       | NONE => (DebugAnalysisStateSpace.run (fn say => say [Addr.toString a, " not found!\n"]); raise Fail "ArrayStoreFn.lookup")
  end

  fun find (store, a) = let
      val index = Word.toInt (Addr.index a)
  in if index < Array.length (! store) then () else resize (index, store);
     Array.sub (! store, index)
  end

  fun extend (store, a, d) = let
      val index = Word.toInt (Addr.index a)
  in if index < Array.length (! store) then () else resize (index, store);
     case Array.sub (! store, index)
      of SOME old => Array.update (! store, index, SOME (Value.join (old, d)))
       | NONE => Array.update (! store, index, SOME d);
     store
  end

  fun appi f store = let
      fun f' (index, value_opt) =
          case value_opt
           of SOME value => f (Addr.fromIndex (Word.fromInt index), value)
            | NONE => ()
  in Array.appi f' (! store) end

  fun foldi f base store = let
      val f' = fn (index, value_opt, base) =>
                  case value_opt
                   of SOME value => f (Addr.fromIndex (Word.fromInt index), value, base)
                    | NONE => base
  in Array.foldli f' base (! store) end

  fun toString store = let
      fun toS (index, d_opt, acc) =
          case d_opt 
           of SOME d =>
              String.concat["(", (Addr.toString (Addr.fromIndex (Word.fromInt index))),
                            " => ", (Value.toString d), ")"] :: acc
            | NONE => acc
  in
      String.concat["(", String.concatWith " " (Array.foldri toS [] (! store)), ")"]
  end

end (* functor ArrayStoreFn *)
