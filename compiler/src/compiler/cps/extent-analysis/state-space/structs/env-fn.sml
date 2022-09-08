(* env-fn.sml
 *
 * Functor for creating abstract environments.
 *)

functor EnvFn (
    structure Var : KEY
    structure Addr : GENERAL
  ) :> ENV 
       where type var = Var.t 
       where type addr = Addr.t
  = struct

    type var = Var.t
    type addr = Addr.t
    type t = addr Var.Map.map

    fun toString env = let
        fun toS (x, a) = String.concat["(", (Var.toString x), " => ", (Addr.toString a), ")"]
    in String.concat ["(", String.concatWithMap " " toS (Var.Map.listItemsi env), ")"] end

    val empty = Var.Map.empty
    val find = Var.Map.find
    fun lookup (env : t, x : Var.t) = 
        (case find(env, x)
          of SOME a => a
           | NONE => raise Fail ("Env.find: " ^ Var.toString x)
        (* end case *))
    val extend = Var.Map.insert

    val foldli = Var.Map.foldli

    val compare = Var.Map.collate Addr.compare
    fun same (env1, env2) = case compare (env1, env2) of EQUAL => true | _ => false

    fun hash env = foldli (fn (x, _, acc) => Word.+ (Var.hash x, acc)) (Word.fromInt 0) env

end

functor HashConsEnvFn (
    structure Var : KEY
    structure Addr : GENERAL
  ) :> ENV 
       where type var = Var.t 
       where type addr = Addr.t
  = struct

  structure Env = EnvFn (structure Var = Var structure Addr = Addr)
  structure HashConsEnv = MyHashCons (structure Base = Env)
  open HashConsEnv

  type var = Var.t
  type addr = Addr.t

  (* FIXME: dangerous *)
  val empty = HashConsEnv.make (Env.empty)
  fun find (env, x) = Env.find (get env, x)
  fun lookup (env, x : Var.t) = 
      (case find (env, x)
        of SOME a => a
         | NONE => raise Fail ("HashConsEnvFn.find: " ^ Var.toString x)
      (* end case *))
  fun extend (env, x, a) = HashConsEnv.make (Env.extend (get env, x, a))
                                            
  fun foldli f base env = Env.foldli f base (get env)

end
