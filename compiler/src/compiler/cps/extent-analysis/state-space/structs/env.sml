(* "User" environments. *)
structure Env = EnvFn (structure Var = LVar structure Addr = Addr)
