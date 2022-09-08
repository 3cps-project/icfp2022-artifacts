(* env.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Env : sig

    type t

    val insertTyVar : t * Types.tyvar * SimpleTyVar.t -> t
    val lookupTyVar : t * Types.tyvar -> SimpleTyVar.t

  end = struct

    structure TVMap = TyVar.Map
    structure TycMap = TyCon.Map
    structure VMap = Var.Map

    fun fail msg = raise Fail(concat msg)

    datatype t = E of {
        tvMap : SimpleTyVar.t TVMap.map
      }

    fun insertTyVar (E{tvMap}, tv, tv') = E{
    fun lookupTyVar (E{tvMap, ...}, tv) = (case TVMap.find(tvMap, tv)
           of SOME tv' => tv'
            | NONE => fail ["unknown type variable ", TyVar.toString tv]
          (* end case *))

  end
