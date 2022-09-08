(* env-rep.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Representation of static environments.
 *)

structure EnvRep =
  struct

    local
      structure BT = BindTree
    in

    structure StrMap = BT.StrId.Map
    structure TycMap = BT.TycId.Map
    structure TVMap = BT.TyVar.Map
    structure ConMap = BT.ConId.Map
    structure VarMap = BT.VarId.Map

    datatype env = E of {
        stk : env_stk,
        tvMap : Types.tyvar TVMap.map
      }

  (* the environment stack tracks environments for nested structures and
   * `local ... in ... end` declarations.
   *)
    and env_stk
      = Top of {                                (* top-level environment for compilation unit *)
            ext : struct_env,                   (*   - externally defined stuff *)
            top : struct_env                    (*   - locally defined stuff *)
          }
      | Str of struct_env * env_stk             (* structure environment *)
      | Loc1 of struct_env * env_stk            (* environment for processing the local part of
                                                 * a local declaration
                                                 *)
      | Loc2 of struct_env * struct_env * env_stk (* environment for processing the visible part
                                                 * of a local declaration; the first environment
                                                 * is the local part and the second is the public
                                                 * part.
                                                 *)

    and struct_env = SE of {
        strMap : (StrId.t * struct_env) StrMap.map,     (* structures *)
        tcMap : ty_def TycMap.map,                      (* type constructors *)
        cMap : Types.dcon ConMap.map,                   (* data constructors *)
        vMap : val_bind VarMap.map                      (* values *)
      }

    and ty_def
      = TyDef of Types.ty_scheme
      | TyCon of Types.tycon

    and val_bind
      = Var of Var.t
      | Overload of Types.ty_scheme * Var.t list

    end (* local *)

  end
