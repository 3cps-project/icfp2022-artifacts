(* store-k.sml
 *
 * Abstract continuation stores.
 *)

structure StoreK = StoreFn (structure Addr = AddrK structure Value = ValueK)

