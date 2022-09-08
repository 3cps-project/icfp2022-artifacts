(* Continuation environments. *)
structure EnvK = EnvFn (structure Var = CVar structure Addr = AddrK)
