(* array-list-fn.sml
 *
 * TODO *)

functor ArrayListFn (
    structure Key : sig type t 
                        val index : t -> int 
                        val fromIndex : int -> t 
                    end
) : sig

  type 'a t  
  val empty : unit -> 'a t
  val lookup : 'a t * Key.t -> 'a
  val find : 'a t * Key.t -> 'a option
  val insert : 'a t * Key.t * 'a -> unit
  val appi : (Key.t * 'a -> unit) -> 'a t -> unit
  val foldi : (Key.t * 'a * 'b -> 'b) -> 'b -> 'a t -> 'b

end = struct

  type t = (('a option) Array.array) ref

  fun empty () = ref (Array.array (100, NONE))

  fun resize (needSize, arrlist) = let
      val arr = ! arrlist
      val size = Array.length arr
      val new_size = Int.max (needSize + 1, size * 2)
      val new_arr = Array.array (new_size, NONE)
  in Array.copy {src = arr, dst = new_arr, di = 0};
     arrlist := new_arr
  end

  fun lookup (arrlist, a) = let
      val index = Key.index a
  in case Array.sub (! arrlist, index)
      of SOME d => d
       | NONE => raise Fail "ArrayListFn.lookup"
  end

  fun find (arrlist, a) = let
      val index = Key.index a
  in if index < Array.length (! arrlist) then () else resize (index, arrlist);
     Array.sub (! arrlist, index)
  end

  fun extend (arrlist, a, d) = let
      val index = Key.index a
  in if index < Array.length (! arrlist) then () else resize (index, arrlist);
     case Array.sub (! arrlist, index)
      of SOME old => Array.update (! arrlist, index, SOME (Value.join (old, d)))
       | NONE => Array.update (! arrlist, index, SOME d);
     arrlist
  end

  fun appi f arrlist = let
      fun f' (index, value_opt) =
          case value_opt
           of SOME value => f (Key.fromIndex index, value)
            | NONE => ()
  in Array.appi f' (! arrlist) end

  fun foldi f base arrlist = let
      val f' = fn (index, value_opt, base) =>
                  case value_opt
                   of SOME value => f (Key.fromIndex index, value, base)
                    | NONE => base
  in Array.foldli f' base (! arrlist) end

end (* functor ArrayListFn *)
