(* proxy.sml
 *
 * TODO *)

structure ProxyBase = struct

   structure C = CPS

   type t = C.exp * ValueK.t list * AddrProxy.t

   fun compare ((e1 as C.EXP (lab1, _), dKs1, aP1), (e2 as C.EXP (lab2, _), dKs2, aP2)) =
       (case Label.compare (lab1, lab2)
         of EQUAL =>
            (case AddrProxy.compare (aP1, aP2)
              of EQUAL => List.collate ValueK.compare (dKs1, dKs2)
               | ord => ord)
          | ord => ord)

   fun same (p1, p2) =
       compare (p1, p2) = EQUAL

   fun hash (C.EXP (lab_e, _), _, _) =
       Label.hash lab_e

   fun toString (e as C.EXP (lab_e, _), dKs, aP) =
       String.concat ["(", Label.toString lab_e, " ", String.concatWithMap " " ValueK.toString dKs, " ", AddrProxy.toString aP, ")"]

   structure Key = struct type ord_key = t val compare = compare end
   structure Map = RedBlackMapFn (Key)
   structure Set = RedBlackSetFn (Key)
       
end

structure Proxy = MyHashCons (structure Base = ProxyBase)

