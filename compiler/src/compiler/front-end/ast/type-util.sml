(* type-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Various utility functions for manipulating types.
 *)

structure TypeUtil : sig

  (* return the "head-normal form" by pruning an instantiated meta
   * variables.
   *)
    val prune : Types.ty -> Types.ty

  (* apply a type-variable-to-type substitution to a type.  The substitution
   * is represented as a list of type variable/type pairs.
   *)
    val substitute : (Types.ty * (Types.tyvar * Types.ty) list) -> Types.ty

  (* apply a type-variable-to-type substitution to a type, where the substitution
   * is represented by a finite map.
   *)
    val applySubst : Types.ty TyVar.Map.map * Types.ty -> Types.ty

    val applyScheme : Types.ty_scheme * Types.ty list -> Types.ty

  (* instantiate a type scheme.  We return the instantiated type and
   * the list of type arguments.
   *)
    val instantiate : Types.ty_scheme -> Types.ty * Types.ty list

  (* limit the depth of any non-instantiated meta-variable in the type to
   * the given depth.
   *)
    val limitDepth  : (int * Types.ty) -> unit

  (* close a type w.r.t. to a set of non-generic variables (i.e., those
   * variables whose depth is less than or equal to the given depth).
   * The first argument is a list of any explicit type variables that are
   * in the scope.
   *)
    val closeTys : (Types.tyvar list * int * Types.ty list) -> Types.ty_scheme list

  (* close a single type *)
    val closeTy : Types.tyvar list * int * Types.ty -> Types.ty_scheme

  (* `bindFreeTVs (tvs, ty)` returns a type scheme `TyScheme(tvs', ty)`, where
   * the `tvs'` are those type variables in `tvs` that occur free in `ty`.
   *)
    val bindFreeTVs : Types.tyvar list * Types.ty -> Types.ty_scheme

  (* return true if two types are equal.  Note that this function does not
   * do unification or alpha renaming of meta variables, but it does chase
   * instantiated meta-variable types.
   *)
    val same : (Types.ty * Types.ty) -> bool

  (* `isInstance (ty, tyc)` returns true if `ty` is an instance of `tyc` *)
    val isInstance : Types.ty * Types.tycon -> bool

  (* is the type an equality type? *)
    val isEqType : Types.ty  -> bool

  (* check a type for unresolved meta variables; return the list of such variables. *)
    val findMetas : Types.ty -> Types.meta list

  (* instantiate a meta variable to the specified type *)
    val setMeta : Types.ty -> Types.meta -> unit

  (* convert various things to strings *)
    val fmtMeta : {long : bool} -> Types.meta -> string

    val fmt : {long : bool} -> Types.ty -> string
    val toString : Types.ty -> string

  (* convert a list of types (e.g., type arguments) to a string enclosed in "< >" *)
    val tysToString : Types.ty list -> string

    val fmtScheme : {long : bool} -> Types.ty_scheme -> string
    val schemeToString : Types.ty_scheme -> string

  end = struct

    structure Ty = Types
    structure MV = MetaVar
    structure TVSet = TyVar.Set
    structure TVMap = TyVar.Map
    structure MVSet = MetaVar.Set
    structure MVMap = MetaVar.Map

    val tvToString = TyVar.toString

  (* return a string representation of a type (for debugging) *)
    fun fmt {long} = let
          val tyc2s = if long then TyCon.toString else TyCon.nameOf
          fun toS (Ty.ErrorTy) = "<error>"
            | toS (Ty.MetaTy mv) = fmtMeta {long=long} mv
            | toS (Ty.VarTy tv) = tvToString tv
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

    and fmtMeta {long} (Ty.MVar{stamp, info}) = (case !info
           of Ty.UNIV{depth, cls, eq} => let
                val l = (case cls of Ty.Any => [] | _ => ["::", TypeClass.toString cls])
                val prefix = if eq then "''U" else "'U"
                in
                  if long
                    then concat(
                      prefix :: Stamp.toString stamp :: "@" ::
                      (if depth < 100000 then Int.toString depth else "∞") ::
                      l)
                    else concat(prefix :: Stamp.toString stamp :: l)
                end
            | Ty.INSTANCE ty => let
                val _ = info := Ty.UNIV{depth= ~1, eq=false, cls=TypeClass.Any}
                val s = if long
                      then concat[
                          "('U", Stamp.toString stamp,
                          " == ", fmt {long=true} ty, ")"
                        ]
                      else fmt {long=false} ty
                in
                  info := Ty.INSTANCE ty; s
                end
          (* end case *))

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

  (* return the "head-normal form" by pruning an instantiated meta
   * variables.
   *)
    fun prune (Ty.MetaTy(Ty.MVar{info as ref(Ty.INSTANCE ty), ...})) = let
          val ty = prune ty
          in
            info := Ty.INSTANCE ty;     (* path compression *)
            ty
          end
      | prune ty = ty

  (* return true if two types are equal.  Note that this function does not
   * do unification or alpha renaming of meta variables, but it does chase
   * instantiated meta-variable types.
   *)
    fun same (ty1, ty2) = (case (prune ty1, prune ty2)
           of (Ty.MetaTy mv1, Ty.MetaTy mv2) => MV.same(mv1, mv2)
            | (Ty.VarTy tv1, Ty.VarTy tv2) => TyVar.same(tv1, tv2)
            | (Ty.ConTy(args1, tyc1), Ty.ConTy(args2, tyc2)) =>
                TyCon.same(tyc1, tyc2) andalso ListPair.allEq same (args1, args2)
            | (Ty.FunTy(ty11, ty12), Ty.FunTy(ty21, ty22)) =>
                same(ty11, ty21) andalso same(ty21, ty22)
            | (Ty.TupleTy tys1, Ty.TupleTy tys2) =>
                ListPair.allEq same (tys1, tys2)
            | _ => false
          (* end case *))

    fun isInstance (ty, tyc) = (case prune ty
           of Ty.ConTy(_, tyc') => TyCon.same(tyc, tyc')
            | _ => false
          (* end case *))

  (* apply a type variable to type substitution to a type *)
    fun applySubst (subst, ty) = let
          fun inst ty = (case prune ty
                 of Ty.ErrorTy => Ty.ErrorTy
                  | ty as Ty.MetaTy _ => ty
                  | ty as Ty.VarTy tv => (case TVMap.find(subst, tv)
                       of SOME ty' => ty'
                        | NONE => ty
                      (* end case *))
                  | Ty.ConTy(args, tyc) => Ty.ConTy(List.map inst args, tyc)
                  | Ty.FunTy(ty1, ty2) => Ty.FunTy(inst ty1, inst ty2)
                  | Ty.TupleTy tys => Ty.TupleTy(List.map inst tys)
                (* end case *))
          in
            inst ty
          end

  (* apply a type-variable-to-type substitution to a type.  The substitution
   * is represented as a list of type variable/type pairs.
   *)
    fun substitute (ty, []) = ty
      | substitute (ty, s) = applySubst (List.foldl TVMap.insert' TVMap.empty s, ty)

    fun applyScheme (Ty.TyScheme([], ty), []) = ty
      | applyScheme (Ty.TyScheme(tvs, ty), tys) =
          applySubst (
            ListPair.foldlEq
              (fn (tv, ty, subst) => TVMap.insert(subst, tv, ty))
                TVMap.empty
                  (tvs, tys),
            ty)

  (* instantiate a type scheme *)
    fun instantiate (Ty.TyScheme([], ty)) = (ty, [])
      | instantiate (Ty.TyScheme(tvs, ty)) = let
        (* allocate fresh meta variables for the type arguments *)
          val mvs = List.map (fn tv => Ty.MetaTy(MetaVar.new' tv)) tvs
        (* create a substitution from type variables to fresh meta variables *)
          val subst = ListPair.foldl
                (fn (tv, mv, s) => TVMap.insert(s, tv, mv))
                  TVMap.empty (tvs, mvs)
          in
            (applySubst (subst, ty), mvs)
          end

  (* limit the depth of any non-instantiated meta-variable in the type to
   * the given depth.
   *)
    fun limitDepth (d, ty) = let
          fun adjust Ty.ErrorTy = ()
            | adjust (Ty.MetaTy(Ty.MVar{info, ...})) = (case !info
                 of Ty.UNIV{depth, eq, cls} => if (d < depth)
                      then info := Ty.UNIV{depth=d, eq=eq, cls=cls}
                      else ()
                  | Ty.INSTANCE ty => adjust ty
                (* end case *))
            | adjust (Ty.VarTy _) = ()
            | adjust (Ty.ConTy(args, _)) = List.app adjust args
            | adjust (Ty.FunTy(ty1, ty2)) = (adjust ty1; adjust ty2)
            | adjust (Ty.TupleTy tys) = List.app adjust tys
          in
            adjust ty
          end

  (* close a list of type w.r.t. to a set of non-generic variables (i.e.,
   * those variables whose depth is less than or equal to the given depth).
   * The first argument is a list of any explicit type variables that are
   * in the scope.  The result will be a list of type schemes.
   *)
    fun closeTys (btvs, d, tys) = let
        (* the first step is to collect the sets of generic meta variables for
         * each type.
         *)
          val varSets = let
                fun collect (ty, gtvs, ftvs) = (case prune ty
                       of Ty.ErrorTy => (gtvs, ftvs)
                        | ty as Ty.MetaTy(mv as Ty.MVar{info, ...}) => (case !info
                             of Ty.UNIV{depth, eq, cls=TypeClass.Any} => if (depth > d)
                                  then (MVSet.add(gtvs, mv), ftvs) (* generic variable *)
                                  else (gtvs, ftvs) (* non-generic variable *)
                              | Ty.UNIV _ => (gtvs, ftvs) (* kinded variable *)
                              | _ => raise Fail "impossible"
                            (* end case *))
                        | ty as Ty.VarTy tv => (gtvs, TVSet.add(ftvs, tv))
                        | Ty.ConTy(args, tyc) => collect' (args, gtvs, ftvs)
                        | Ty.FunTy(ty1, ty2) => let
                            val (gtvs, ftvs) = collect (ty1, gtvs, ftvs)
                            in
                              collect (ty2, gtvs, ftvs)
                            end
                        | Ty.TupleTy tys => collect' (tys, gtvs, ftvs)
                      (* end case *))
                and collect' ([], gtvs, ftvs) = (gtvs, ftvs)
                  | collect' (ty::tys, gtvs, ftvs) = let
                      val (gtvs, ftvs) = collect (ty, gtvs, ftvs)
                      in
                        collect' (tys, gtvs, ftvs)
                      end
                in
                  List.map (fn ty => collect (ty, MVSet.empty, TVSet.empty)) tys
                end
          val allVars = List.foldl
                (fn ((mvs, _), acc) => MVSet.union(mvs, acc))
                  MVSet.empty varSets
        (* create a mapping from generic meta varibles to fresh type variables *)
          val gtvMap = let
                val count = ref 0
              (* generate a fresh type variable *)
                fun newVar (mv as Ty.MVar{info, ...}, gMap) = let
                      val id = !count
                      val prefix = str(Char.chr(Char.ord #"a" + id mod 26))
                      val suffix = if (id >= 26) then Int.toString(id mod 26) else ""
                      val tv = TyVar.new'(concat["'", prefix, suffix])
                      in
                        count := id+1;
                        info := Ty.INSTANCE(Ty.VarTy tv);
                        MVMap.insert(gMap, mv, tv)
                      end
                in
                  MVSet.foldl newVar MVMap.empty allVars
                end
        (* form the type schemes for the result *)
          fun mkScheme (ty, (gtvs, ftvs)) = let
                val btvs' = List.filter (fn tv => TVSet.member(ftvs, tv)) btvs
                val tvs = MVSet.foldl
                      (fn (mv, tvs) => MVMap.lookup(gtvMap, mv) :: tvs)
                        [] gtvs
                in
                  Ty.TyScheme(btvs' @ tvs, ty)
                end
          in
            ListPair.map mkScheme (tys, varSets)
          end

(* TODO: specialize this function by factoring out common code from closeTys *)
    fun closeTy (btvs, depth, ty) = let
          val [tyScm] = closeTys (btvs, depth, [ty])
          in
            tyScm
          end

    fun bindFreeTVs ([], ty) = Ty.TyScheme([], ty)
      | bindFreeTVs (tvs, ty) = let
          fun findFreeTVs (ty, tvs) = (case prune ty
                 of Ty.ErrorTy => tvs
                  | Ty.MetaTy _ => tvs
                  | Ty.VarTy tv => TVSet.add (tvs, tv)
                  | Ty.ConTy(tys, _) => List.foldl findFreeTVs tvs tys
                  | Ty.FunTy(ty1, ty2) => findFreeTVs(ty2, findFreeTVs(ty1, tvs))
                  | Ty.TupleTy tys => List.foldl findFreeTVs tvs tys
                (* end case *))
          val ftvs = findFreeTVs (ty, TVSet.empty)
          in
            Ty.TyScheme(List.filter (fn tv => TVSet.member(ftvs, tv)) tvs, ty)
          end

  (* check if a type constructor supports equality.  We cache this information
   * in the "equality mark" defined in the `TyCon` structure.
   *)
    fun isEqTyc tyc = (case TyCon.peekEqMark tyc
           of SOME eq => eq
            | NONE => let
                fun isEqTy Ty.ErrorTy = true
                  | isEqTy (Ty.MetaTy _) = raise Fail "unexpected meta type"
                  | isEqTy (Ty.VarTy _) = true
                  | isEqTy (Ty.ConTy(tys, tyc)) =
                      TyCon.isMutable tyc
                        orelse (isEqTyc tyc andalso List.all isEqTy tys)
                  | isEqTy (Ty.FunTy _) = false
                  | isEqTy (Ty.TupleTy tys) = List.all isEqTy tys
                fun isEqDCon (Ty.DCon{argTy=NONE, ...}) = true
                  | isEqDCon (Ty.DCon{argTy=SOME ty, ...}) = isEqTy ty
                in
                  case tyc
                   of Ty.Tyc{def=Ty.AbsTyc _, ...} =>
                        raise Fail "abstype w/o equality mark"
                    | Ty.Tyc{def=Ty.DataTyc{cons, ...}, ...} => let
                        val _ = TyCon.markEq (tyc, true) (* to handle recursive types *)
                        val isEq = List.all isEqDCon (!cons)
                        in
                          TyCon.markEq (tyc, isEq);
                          isEq
                        end
                  (* end case *)
                end
          (* end case *))

    fun isEqType Ty.ErrorTy = true
      | isEqType (Ty.MetaTy(Ty.MVar{info, ...})) = (case !info
           of Ty.UNIV{eq, ...} => eq
            | Ty.INSTANCE ty => (
                info := Ty.UNIV{depth=0, eq=false, cls=TypeClass.Any}; (* blackhole *)
                isEqType ty before info := Ty.INSTANCE ty)
          (* end case *))
      | isEqType (Ty.VarTy(Ty.TVar{eq, ...})) = eq
      | isEqType (Ty.ConTy([], tyc)) = isEqTyc tyc
      | isEqType (Ty.ConTy(tyArgs, tyc)) =
          TyCon.isMutable tyc orelse (isEqTyc tyc andalso List.all isEqType tyArgs)
      | isEqType (Ty.TupleTy tys) = List.all isEqType tys
      | isEqType _ = false

  (* check a type for unresolved meta variables; return the list of such variables. *)
    fun findMetas ty = let
          fun find (ty, mvs) = (case prune ty
                 of Ty.ErrorTy => mvs
                  | Ty.MetaTy mv => MVSet.add (mvs, mv)
                  | Ty.VarTy _ => mvs
                  | Ty.ConTy(tys, _) => List.foldl find mvs tys
                  | Ty.FunTy(ty1, ty2) => find(ty2, find(ty1, mvs))
                  | Ty.TupleTy tys => List.foldl find mvs tys
                (* end case *))
          in
            MVSet.toList (find (ty, MVSet.empty))
          end

    fun setMeta ty (Ty.MVar{info, ...}) = (case !info
           of Ty.UNIV _ => info := Ty.INSTANCE ty
            | _ => raise Fail "expected universal meta variable"
          (* end case *))

  end
