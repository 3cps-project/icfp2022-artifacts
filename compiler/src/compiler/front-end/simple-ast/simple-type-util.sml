(* simple-type-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure SimpleTypeUtil : sig

    type tv_env = SimpleTypes.ty SimpleTyVar.Map.map

  (* does any variable in the domain of subst occur in the type? *)
    val domainOccursInTy : tv_env * SimpleTypes.ty -> bool

  (* extend a type-variable to type substitution with additional bindings *)
    val extendSubst : tv_env * SimpleTyVar.t list * SimpleTypes.ty list -> tv_env

  (* apply a type-variable-to-type substitution to a type, where the substitution
   * is represented by a finite map.
   *)
    val applySubst : tv_env -> SimpleTypes.ty -> SimpleTypes.ty

    val applyScheme : SimpleTypes.ty_scheme * SimpleTypes.ty list -> SimpleTypes.ty

  (* `bindFreeTVs (tvs, ty)` returns a type scheme `TyScheme(tvs', ty)`, where
   * the `tvs'` are those type variables in `tvs` that occur free in `ty`.
   *)
    val bindFreeTVs : SimpleTyVar.t list * SimpleTypes.ty -> SimpleTypes.ty_scheme

  (* return true if two types are equal.  Note that this function does not
   * do unification or alpha renaming of meta variables, but it does chase
   * instantiated meta-variable types.
   *)
    val same : (SimpleTypes.ty * SimpleTypes.ty) -> bool

    val fmt : {long : bool} -> SimpleTypes.ty -> string
    val toString : SimpleTypes.ty -> string

  (* convert a list of types (e.g., type arguments) to a string enclosed in "< >" *)
    val tysToString : SimpleTypes.ty list -> string

    val fmtScheme : {long : bool} -> SimpleTypes.ty_scheme -> string
    val schemeToString : SimpleTypes.ty_scheme -> string

  (* return true if two types are alpha-convertable. This function fails on
   * uninstantiated meta variables.
   *)
    val alphaSame : (SimpleTypes.ty * SimpleTypes.ty) -> bool

  (* compute hash of a type.  The hash will be the same for alpha-equal types.
   * This function fails on uninstantiated meta variables.
   *)
    val alphaHash : SimpleTypes.ty -> word

  end = struct

    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure TVSet = TyVar.Set
    structure TVMap = TyVar.Map
    structure TyCon = SimpleTyCon

    val tvToString = SimpleTyVar.toString

  (* return a string representation of a type (for debugging) *)
    fun fmt {long} = let
          val tyc2s = if long then TyCon.toString else TyCon.nameOf
          fun toS (Ty.VarTy tv) = tvToString tv
            | toS (Ty.ConTy([], tyc)) = tyc2s tyc
            | toS (Ty.ConTy([ty], tyc)) = concat[
                  toS ty, " ", tyc2s tyc
                ]
            | toS (Ty.ConTy(tys, tyc)) = concat[
                  "(", String.concatWithMap "," toS tys, ") ",
                  tyc2s tyc
                ]
            | toS (Ty.FunTy(ty1 as Ty.FunTy _, ty2)) =
                concat["(", toS ty1, ") -> ", toS ty2]
            | toS (Ty.FunTy(ty1, ty2)) = concat[toS ty1, " -> ", toS ty2]
            | toS (Ty.TupleTy []) = "unit"
            | toS (Ty.TupleTy tys) = let
                fun toS' (ty as Ty.FunTy _) = concat["(", toS ty, ")"]
                  | toS' ty = toS ty
                in
                  concat["(", String.concatWithMap " * " toS' tys, ")"]
                end
          in
            toS
          end

    val toString = fmt {long=false}

    fun tysToString tys = concat[
            "<", String.concatWithMap "," toString tys, ">"
          ]

    fun fmtScheme {long} (Ty.TyScheme([], ty)) = fmt {long=long} ty
      | fmtScheme {long} (Ty.TyScheme(tvs, ty)) = concat[
            "<", String.concatWith "," (List.map tvToString tvs), "> ",
            fmt {long=long} ty
          ]

  (* return the string representation of a type scheme *)
    val schemeToString = fmtScheme {long=false}

  (* return true if two types are equal.  Note that this function does not
   * do unification or alpha renaming of meta variables, but it does chase
   * instantiated meta-variable types.
   *)
    fun same (ty1, ty2) = (case (ty1, ty2)
           of (Ty.VarTy tv1, Ty.VarTy tv2) => TyVar.same(tv1, tv2)
            | (Ty.ConTy(args1, tyc1), Ty.ConTy(args2, tyc2)) =>
                TyCon.same(tyc1, tyc2) andalso ListPair.allEq same (args1, args2)
            | (Ty.FunTy(ty11, ty12), Ty.FunTy(ty21, ty22)) =>
                same(ty11, ty21) andalso same(ty21, ty22)
            | (Ty.TupleTy tys1, Ty.TupleTy tys2) =>
                ListPair.allEq same (tys1, tys2)
            | _ => false
          (* end case *))

    type tv_env = Ty.ty TVMap.map

  (* does any variable in the domain of subst occur in the type? *)
    fun domainOccursInTy (subst, ty) = let
          fun occurs ty = (case ty
                 of ty as Ty.VarTy tv => TVMap.inDomain (subst, tv)
                  | Ty.ConTy(args, tyc) => List.exists occurs args
                  | Ty.FunTy(ty1, ty2) => occurs ty1 orelse occurs ty2
                  | Ty.TupleTy tys => List.exists occurs tys
                (* end case *))
          in
            not (TVMap.isEmpty subst) andalso occurs ty
          end

  (* extend a type-variable to type substitution with additional bindings *)
    fun extendSubst (tvSubst, tvs, tys) =
          ListPair.foldlEq
            (fn (tv, ty, subst) => TVMap.insert(subst, tv, ty))
              tvSubst
                (tvs, tys)

  (* apply a type variable to type substitution to a type *)
    fun applySubst subst = let
          fun inst ty = (case ty
                 of ty as Ty.VarTy tv => (case TVMap.find(subst, tv)
                       of SOME ty' => ty'
                        | NONE => ty
                      (* end case *))
                  | Ty.ConTy(args, tyc) => Ty.ConTy(List.map inst args, tyc)
                  | Ty.FunTy(ty1, ty2) => Ty.FunTy(inst ty1, inst ty2)
                  | Ty.TupleTy tys => Ty.TupleTy(List.map inst tys)
                (* end case *))
          in
            inst
          end

    fun applyScheme (Ty.TyScheme([], ty), []) = ty
      | applyScheme (Ty.TyScheme(tvs, ty), tys) =
          applySubst (extendSubst (TVMap.empty, tvs, tys)) ty

  (* "smart" version of applySubst that does no work for empty substitutions *)
    val applySubst =
          fn subst => if TVMap.isEmpty subst then Fn.id else applySubst subst

    fun bindFreeTVs ([], ty) = Ty.TyScheme([], ty)
      | bindFreeTVs (tvs, ty) = let
          fun findFreeTVs (ty, tvs) = (case ty
                 of Ty.VarTy tv => TVSet.add (tvs, tv)
                  | Ty.ConTy(tys, _) => List.foldl findFreeTVs tvs tys
                  | Ty.FunTy(ty1, ty2) => findFreeTVs(ty2, findFreeTVs(ty1, tvs))
                  | Ty.TupleTy tys => List.foldl findFreeTVs tvs tys
                (* end case *))
          val ftvs = findFreeTVs (ty, TVSet.empty)
          in
            Ty.TyScheme(List.filter (fn tv => TVSet.member(ftvs, tv)) tvs, ty)
          end

    fun alphaSame (ty1, ty2) = let
        (* map a type variable to its unique ID *)
          fun alphaCvt (tvMap : int TVMap.map, tv) = (case TVMap.find(tvMap, tv)
                 of SOME id => (tvMap, id)
                  | NONE => let
                      val id = TVMap.numItems tvMap
                      in
                        (TVMap.insert(tvMap, tv, id), id)
                      end
                (* end case *))
          fun same (tvMap1, tvMap2, ty1, ty2) = (case (ty1, ty2)
                 of (Ty.VarTy tv1, Ty.VarTy tv2) => let
                      val (tvMap1, id1) = alphaCvt (tvMap1, tv1)
                      val (tvMap2, id2) = alphaCvt (tvMap2, tv2)
                      in
                        if (id1 = id2) then SOME(tvMap1, tvMap2) else NONE
                      end
                  | (Ty.ConTy(args1, tyc1), Ty.ConTy(args2, tyc2)) =>
                      if TyCon.same(tyc1, tyc2)
                        then sameTys(tvMap1, tvMap2, args1, args2)
                        else NONE
                  | (Ty.FunTy(ty11, ty12), Ty.FunTy(ty21, ty22)) => (
                      case same(tvMap1, tvMap2, ty11, ty21)
                       of SOME(tvMap1, tvMap2) => same(tvMap1, tvMap2, ty12, ty22)
                        | _ => NONE
                      (* end case *))
                  | (Ty.TupleTy tys1, Ty.TupleTy tys2) =>
                      sameTys(tvMap1, tvMap2, tys1, tys2)
                  | _ => NONE
                (* end case *))
          and sameTys (tvMap1, tvMap2, [], []) = SOME(tvMap1, tvMap2)
            | sameTys (tvMap1, tvMap2, ty1::tys1, ty2::tys2) = (
                case same(tvMap1, tvMap2, ty1, ty2)
                 of SOME (tvMap1, tvMap2) => sameTys (tvMap1, tvMap2, tys1, tys2)
                  | NONE => NONE
                (* end case *))
            | sameTys _ = NONE
          in
            Option.isSome (same (TVMap.empty, TVMap.empty, ty1, ty2))
          end

    fun alphaHash ty = let
        (* map a type variable to its unique ID *)
          fun alphaCvt (tvMap : word TVMap.map, tv) = (case TVMap.find(tvMap, tv)
                 of SOME id => (tvMap, id)
                  | NONE => let
                      val id = Word.fromInt(TVMap.numItems tvMap)
                      in
                        (TVMap.insert(tvMap, tv, id), id)
                      end
                (* end case *))
          fun hash (tvMap, ty) = (case ty
                 of Ty.VarTy tv => let
                      val (tvMap, id) = alphaCvt (tvMap, tv)
                      in
                        (tvMap, 0w17 * id)
                      end
                  | Ty.ConTy(tys, tyc) => hashTys (tvMap, tys, 0w19 * TyCon.hash tyc)
                  | Ty.FunTy(ty1, ty2) => let
                      val (tvMap, h1) = hash (tvMap, ty1)
                      val (tvMap, h2) = hash (tvMap, ty2)
                      in
                        (tvMap, 0w137 + h1 + h2)
                      end
                  | Ty.TupleTy tys => hashTys(tvMap, tys, 0w167)
                (* end case *))
          and hashTys (tvMap, [], h) = (tvMap, h)
            | hashTys (tvMap, ty::tys, h) = let
                val (tvMap, h') = hash (tvMap, ty)
                in
                  hashTys (tvMap, tys, 0w3 * h + h')
                end
          in
            #2 (hash (TVMap.empty, ty))
          end

  end
