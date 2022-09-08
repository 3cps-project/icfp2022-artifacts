(* env.sml
 *
 * Concrete environments.
 *)

(* The interface for concrete environments *)
signature CENV =
  sig

    type t
    type var
    type addr

    val empty : t
    val lookup : t * var -> addr
    val find : t * var -> addr option
    val extend : t * var * addr -> t
    val compare : t * t -> order

    val toString : t -> string

  end

(* concrete environments *)
structure CEnv : CENV where type var = LVar.t and type addr = CAddr.t =
  struct

    type var = LVar.t
    type addr = CAddr.t
    type t = addr LVar.Map.map

    val empty = LVar.Map.empty
    val find = LVar.Map.find
    fun lookup (env : t, x : LVar.t) = 
        (case find(env, x)
          of SOME a => a
           | NONE => raise Fail("CEnv.lookup: " ^ LVar.toString x)
        (* end case *))
    val extend = LVar.Map.insert
    val compare = LVar.Map.collate CAddr.compare

    fun toString env = 
        "(" ^ (String.concatWithMap " " (fn (x, a) => "(" ^ (LVar.toString x) ^ " => " ^ (CAddr.toString a ^ ")"))
                                    (LVar.Map.listItemsi env))
        ^ ")"


  end

(* concrete continuation environments *)
structure CEnvK : CENV where type var = CVar.t and type addr = CAddrK.t =
  struct

    type var = CVar.t
    type addr = CAddrK.t
    type t = addr CVar.Map.map

    val empty = CVar.Map.empty
    val find = CVar.Map.find
    fun lookup (envK : t, x : CVar.t) = 
        (case find(envK, x)
          of SOME aK => aK
           | NONE => raise Fail("CEnvK.lookup: " ^ CVar.toString x)
        (* end case *))
    val extend = CVar.Map.insert
    val compare = CVar.Map.collate CAddrK.compare

    fun toString envK = 
        "(" ^ (String.concatWithMap " " (fn (k, aK) => "(" ^ (CVar.toString k) ^ " => " ^ (CAddrK.toString aK) ^ ")")
                                    (CVar.Map.listItemsi envK))
        ^ ")"


  end
