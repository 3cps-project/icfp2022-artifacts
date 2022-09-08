(* array-store-fn.sml
 *
 * The actual store implementation used in the compiler.
 *)

functor StoreFn (structure Addr : ADDR
                 structure Value : VALUE_BASE)
        : STORE where type addr = Addr.t 
                  and type value = Value.t
   = ArrayStoreFn (structure Addr = Addr structure Value = Value)
