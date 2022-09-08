(* store.sml
 *
 * Concrete stores.
 *)

functor CStoreFn (
    structure CAddr : CADDR
    structure CValue : CVALUE
  ) : sig

  type t
  type addr = CAddr.t
  type value = CValue.t
                   
  val makeEmpty : unit -> t
  val lookup : t * addr -> CValue.t
  val find : t * addr -> CValue.t option
  val extend : t * addr * CValue.t -> t
                             
  val toString : t -> string

  val appi : (addr * value -> unit) -> t -> unit
  val foldi : (addr * value * 'a -> 'a) -> 'a -> t -> 'a

end = struct

  type t = CValue.t CAddr.Map.map
  type addr = CAddr.t
  type value = CValue.t
                   
  fun makeEmpty () = CAddr.Map.empty
                  
  fun lookup (store, adr) = 
      case (CAddr.Map.find (store, adr))
       of SOME v => v
        | NONE => raise Fail("StoreFn.find: " ^ CAddr.toString adr)
  (* end case *)

  val find = CAddr.Map.find
                 
  val extend = CAddr.Map.insert
                   
  fun toString store = 
      "(" ^ (String.concatWithMap " " (fn (a, d) => "(" ^ (CAddr.toString a) ^ " => " ^ (CValue.toString d) ^ ")")
                                  (CAddr.Map.listItemsi store))
      ^ ")"
            
  val appi = CAddr.Map.appi
  val foldi = CAddr.Map.foldli

end (* functor CStoreFn *)

(*
(* concrete stores *)
functor CStoreFn (
    structure CAddr : CADDR
    structure CValue : CVALUE
  ) : sig

  type t
  type addr = CAddr.t
  type value = CValue.t
                   
  val makeEmpty : unit -> t
  val lookup : t * addr -> CValue.t
  val find : t * addr -> CValue.t option
  val extend : t * addr * CValue.t -> t
                             
  val toString : t -> string

  val appi : (addr * value -> unit) -> t -> unit
  val foldi : (addr * value * 'a -> 'a) -> 'a -> t -> 'a

end = struct

  type t = CValue.t CAddr.Tbl.hash_table
  type addr = CAddr.t
  type value = CValue.t
                   
  fun makeEmpty () = CAddr.Tbl.mkTable (10000, Fail ("StoreFn find"))
                  
  fun lookup (store, adr) = CAddr.Tbl.lookup store adr

  fun find (store, adr) = CAddr.Tbl.find store adr
                 
  fun extend (store, adr, d) = (CAddr.Tbl.insert store (adr, d); store)
                   
  fun toString store = 
      "(" ^ (String.concatWithMap " " (fn (a, d) => "(" ^ (CAddr.toString a) ^ " => " ^ (CValue.toString d) ^ ")")
                                  (CAddr.Tbl.listItemsi store))
      ^ ")"
            
  val appi = CAddr.Tbl.appi
  val foldi = CAddr.Tbl.foldi

end (* functor CStoreFn *)
*)

structure CStore = CStoreFn (
    structure CAddr = CAddr
    structure CValue = CValue)

