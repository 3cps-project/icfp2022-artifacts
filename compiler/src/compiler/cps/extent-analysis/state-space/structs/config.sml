(* config.sml
 *
 * Abstract configurations.
 *)

structure ConfigBase : sig

    type t = CPS.exp * Env.t * EnvK.t * TEnv.t * AddrProxy.t

    val compare : t * t -> order
    val same : t * t -> bool

    val toString : t -> string

    val hash : t -> word

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t

  end = struct

    type t = CPS.exp * Env.t * EnvK.t * TEnv.t * AddrProxy.t

    fun compare ((e1, env1, envK1, tenv1, aP1),
                 (e2, env2, envK2, tenv2, aP2)) =
        (case CPS.compare(e1,e2)
          of EQUAL =>
             (case AddrProxy.compare (aP1, aP2)
               of EQUAL =>
                  (case Env.compare (env1, env2) 
                    of EQUAL =>
                       (case EnvK.compare (envK1, envK2)
                         of EQUAL => TEnv.compare (tenv1, tenv2)
                          | ord => ord)
                     | ord => ord) 
                | ord => ord)
           | ord => ord)

    fun same ((e1, env1, envK1, tenv1, aP1), (e2, env2, envK2, tenv2, aP2)) =
        CPS.same (e1, e2)
        andalso AddrProxy.same (aP1, aP2)
        andalso Env.same (env1, env2)
        andalso EnvK.same (envK1, envK2)
        andalso TEnv.same (tenv1, tenv2)

    fun toString (e, env, envK, tenv, aP) =
        String.concat [CPSUtil.expName e, TEnv.toString tenv]

    (* Sometimes we want a detailed toString *)
    (*
    fun toString (e, env, envK, aP) =
        String.concat ["[", CPSUtil.expName e,
                       " ", Env.toString env,
                       " ", EnvK.toString envK,
                       " ", AddrProxy.toString aP, "]"]
    *)

    fun hash (CPS.EXP (l_e, _), _, _, _, _) = Label.hash l_e

    local
      structure Key = struct type ord_key = t val compare = compare end
      structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    in
    structure Set = RedBlackSetFn (Key)
    structure Map = RedBlackMapFn (Key)
    structure MSet = MyHashSetFn (HashKey)
    structure Tbl = HashTableFn (HashKey)
    end (* local *)

  end

structure Config = MyHashCons (structure Base = ConfigBase)
