(* store-proxy.sml
 *
 * Abstract proxy stores.
 *)

structure StoreProxy = StoreFn (structure Addr = AddrProxy structure Value = ValueProxy)
