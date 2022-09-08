
(*
(* Continuation addresses. *)
structure AddrKBase = ZeroCFAFn (structure Var = CVar structure Ignore = AddrProxy)
*)

(* Continuation addresses. *)
structure AddrKBase = OneCFAFn (structure Var = CVar structure Track = AddrProxy)

structure AddrK = AddrHashCons (structure AddrBase = AddrKBase)

