(* unbounded-array.sml
 *
 * An array with unlimited indices (i.e. partial function from Int -> 'a)
 *)

(* Arraylist implementation of an unbounded array *)
structure UnboundedArray : sig

  type 'a t

  val empty : unit -> 'a t
  val load : 'a t * int -> 'a
  val store : 'a t * int * 'a -> unit
  val delete : 'a t * int -> unit
  val size : 'a t -> int

end = struct

  type 'a t = (('a option) Array.array) ref

  fun empty () = ref (Array.array (10, NONE))

  fun size array = (Array.length (! array))

  fun resize (needSize, array) = let
      val arr = ! array
      val size = Array.length arr
      val new_size = Int.max (needSize + 1, size * 2)
      val new_arr = Array.array (new_size, NONE)
  in Array.copy {src = arr, dst = new_arr, di = 0};
     array := new_arr
  end

  fun load (array, index) = 
      case Array.sub (! array, index)
       of SOME d => d
        | NONE => raise Fail ("UnboundedArray.lookup: index " ^ (Int.toString index) ^ " size " ^ (Int.toString (size array)))


  fun store (array, index, d) = 
      (if index < Array.length (! array) then () else resize (index, array);
       Array.update (! array, index, SOME d))


  fun delete (array, index) =
      Array.update (! array, index, NONE)

  fun toString array = let
      fun toS (index, d_opt, acc) =
          case d_opt 
           of SOME d =>
              String.concat["(", (Int.toString (index)),
                            " => ", (Value.toString d), ")"] :: acc
            | NONE => acc
  in
      String.concat["(", String.concatWith " " (Array.foldri toS [] (! array)), ")"]
  end

end (* struct UnboundedArray *)
