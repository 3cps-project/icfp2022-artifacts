(* store.sml
 *
 * Abstract stores.
 *)

structure Store = StoreFn (structure Addr = Addr structure Value = Value)

