(* map-store-fn.sml
 *
 * Functor for creating abstract store with finite maps.
 *)

functor MapStoreFn (
    structure Addr : ADDR
    structure Value : VALUE_BASE
  ) : STORE where type addr = Addr.t 
              and type value = Value.t
= struct

    type t = Value.t Addr.Map.map
    type addr = Addr.t
    type value = Value.t

    fun empty () = Addr.Map.empty

    fun toString store = let
        fun toS (a, d) = String.concat["(", (Addr.toString a), " => ", (Value.toString d), ")"]
    in
        String.concat["(", String.concatWithMap " " toS (Addr.Map.listItemsi store), ")"]
    end

    fun lookup (store, adr) = 
        case (Addr.Map.find (store, adr))
         of SOME v => v
          | NONE => raise Fail("StoreFn.find: " ^ Addr.toString adr)
    (* end case *)

    val find = Addr.Map.find

    fun extend (store, adr, value) =
        case Addr.Map.find (store, adr)
         of SOME old => Addr.Map.insert (store, adr, Value.join (old, value))
          | NONE => Addr.Map.insert (store, adr, value)
                                               
    val appi = Addr.Map.appi
    val foldi = Addr.Map.foldli

end (* functor MapStoreFn *)

