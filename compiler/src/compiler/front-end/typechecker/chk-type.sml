(* chk-type.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ChkType : sig

  (* check a type expression *)
    val check : Context.t * BindTree.ty -> Types.ty

  (* given a list of implicitly-bound type-variable identifiers, generate fresh type
   * variables for them, extend the context with the bindings, and return both the
   * list of type variables and the extended context.
   *)
    val bindTyVars : Context.t * BindTree.tyvar list -> Types.tyvar list * Context.t

  end = struct

    structure BT = BindTree
    structure E = Env
    structure TU = TypeUtil
    structure C = Context

  (* error reporting *)
    datatype token = datatype TypeError.token
    val error = Context.error

    val qualId = TypeError.qualId BT.TycId.nameOf

  (* "smart" tuple type constructor *)
    fun mkTupleTy [ty] = ty
      | mkTupleTy tys = AST.TupleTy tys

    fun check (cxt, ty) = (case ty
           of BT.MarkTy m => check(C.withMark(cxt, m))
            | BT.NamedTy(tyArgs, qid) => let
                val tyArgs' = List.map (fn ty => check(cxt, ty)) tyArgs
                fun chk (SOME(E.TyDef(AST.TyScheme(tvs, ty)))) =
                      if (List.length tvs <> List.length tyArgs')
                        then (
                          error(cxt, [S "arity mismatch for ", qualId qid]);
                          Types.ErrorTy)
                        else TU.substitute (ty, ListPair.zip(tvs, tyArgs'))
                  | chk (SOME(E.TyCon tyc')) =
                      if (TyCon.arityOf tyc' <> List.length tyArgs')
                        then (
                          error(cxt, [S "arity mismatch for ", qualId qid]);
                          Types.ErrorTy)
                        else AST.ConTy(tyArgs', tyc')
                  | chk NONE = raise Fail "impossible"
                in
                  case ChkQualId.check(cxt, qid)
                   of SOME(SOME strEnv, id) => chk (E.findTyId'(strEnv, id))
                    | SOME(NONE, id) => chk (C.findTyId(cxt, id))
                    | NONE => raise Fail "impossible"
                  (* end case *)
                end
            | BT.VarTy tv => (case C.findTyVar(cxt, tv)
                 of SOME tv' => AST.VarTy tv'
                  | NONE => raise Fail "impossible"
                (* end case *))
            | BT.TupleTy tys =>
                mkTupleTy(List.map (fn ty => check(cxt, ty)) tys)
            | BT.FunTy(ty1, ty2) =>
                AST.FunTy(check(cxt, ty1), check(cxt, ty2))
            | BT.ErrorTy => Types.ErrorTy
          (* end case *))

    fun bindTyVars (cxt, []) = ([], cxt)
      | bindTyVars (cxt, tvs) = let
          fun bind (tv, (tvs', cxt)) = let
                val tv' = TyVar.new tv
                in
                  (tv' :: tvs', C.insertTyVar(cxt, tv, tv'))
                end
          in
            List.foldr bind ([], cxt) tvs
          end

  end
