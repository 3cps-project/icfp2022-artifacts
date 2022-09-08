(* struct-env.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Structure environments.
 *)

structure StructEnv : sig

    type t

    val empty : t

  (* lookup function environments *)
    val findStruct : t * BindTree.strid -> (StrId.t * t) option
    val findTyId   : t * BindTree.tycon -> EnvRep.ty_def option
    val findDCon   : t * BindTree.conid -> Types.dcon option
    val findVar    : t * BindTree.varid -> EnvRep.val_bind option

  end = struct

    structure StrMap = EnvRep.StrMap
    structure TycMap = EnvRep.TycMap
    structure ConMap = EnvRep.ConMap
    structure VarMap = EnvRep.VarMap

    datatype t = datatype EnvRep.struct_env

    val empty = SE{
            strMap = StrMap.empty,
            tcMap = TycMap.empty,
            cMap = ConMap.empty,
            vMap = VarMap.empty
          }

  (* structure-environment operations *)
    fun findStruct (SE{strMap, ...}, id) = StrMap.find (strMap, id)
    fun findTyId (SE{tcMap, ...}, id) = TycMap.find (tcMap, id)
    fun findDCon (SE{cMap, ...}, id) = ConMap.find (cMap, id)
    fun findVar (SE{vMap, ...}, id) = VarMap.find (vMap, id)

  end
