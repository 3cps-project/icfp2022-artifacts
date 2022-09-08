(* table-store-fn.sml
 *
 * Functor for creating abstract store with hash tables.
 *)

functor TableStoreFn (
    structure Addr : ADDR
    structure Value : VALUE_BASE
  ) : STORE where type addr = Addr.t 
              and type value = Value.t
= struct

    type t = Value.t Addr.Tbl.hash_table
    type addr = Addr.t
    type value = Value.t

    fun empty () = Addr.Tbl.mkTable (128, Fail "TableStoreFn.make")

    fun toString store = let
        fun toS (a, d) = String.concat["(", (Addr.toString a), " => ", (Value.toString d), ")"]
    in
        String.concat["(", String.concatWithMap " " toS (Addr.Tbl.listItemsi store), ")"]
    end

    fun lookup (store, adr) = 
        case (Addr.Tbl.find store adr)
         of SOME v => v
          | NONE => raise Fail("TableStoreFn.lookup: " ^ Addr.toString adr)
    (* end case *)

    fun find (store, adr) = Addr.Tbl.find store adr

    fun extend (store, adr, value) =
        (case find (store, adr)
          of SOME old => Addr.Tbl.insert store (adr, Value.join (old, value))
           | NONE => Addr.Tbl.insert store (adr, value);
         store)

    val appi = Addr.Tbl.appi
    val foldi = Addr.Tbl.foldi

end (* functor TableStoreFn *)

