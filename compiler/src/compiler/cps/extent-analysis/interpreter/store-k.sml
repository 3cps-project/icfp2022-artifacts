(* store-k.sml
 *
 * Concrete continuation stores. 
 *)

structure CStoreK = CStoreFn (
    structure CAddr = CAddrK
    structure CValue = CValueK)
