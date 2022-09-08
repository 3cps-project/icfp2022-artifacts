(* Type environments *)
(* TODO: Shouldn't need type schemes? some stuff is very hard here *)
structure TEnv = EnvFn (structure Var = CPSTyVar structure Addr = CPSTypes)

(* structure TEnv = HashConsEnvFn (structure Var = CPSTyVar structure Addr = CPSTypes) *)
