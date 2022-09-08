
(*
(* "User" addresses. *)
structure AddrBase = ZeroCFAFn (structure Var = LVar structure Ignore = AddrProxy)
*)

(* "User" addresses. *)
structure AddrBase = OneCFAFn (structure Var = LVar structure Track = AddrProxy)

structure Addr = AddrHashCons (structure AddrBase = AddrBase)



