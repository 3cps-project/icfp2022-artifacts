(* chk-pat.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ChkPat : sig

    type var_bind = (BindTree.varid * Var.t)

  (* typecheck a pattern, returning the AST pattern, the list of bound variables,
   * the type of the pattern.
   *)
    val check : Context.t * int option * BindTree.pat -> AST.pat * var_bind list * Types.ty

  end = struct

    structure BT = BindTree
    structure E = Env
    structure C = Context
    structure TU = TypeUtil
    structure ASet = AtomSet
    structure Ty = Types

  (* error reporting *)
    datatype token = datatype TypeError.token
    val error = Context.error

    val qualId = TypeError.qualId BT.ConId.nameOf

  (* a pattern for when there is an error *)
    val bogusPat = AST.TuplePat[]

    type var_bind = (BindTree.varid * Var.t)

    val newWild = Var.newTmp "_"

  (* make a list cons pattern *)
    fun consPat tyArgs (hdPat, tlPat) =
          AST.ConPat(PrimTy.listCons, tyArgs, AST.TuplePat[hdPat, tlPat])
    fun nilPat tyArgs = AST.ConstPat(AST.DConst(PrimTy.listNil, tyArgs))

  (* normalize a layered pattern, where we assume that the two patterns
   * are compatible.
   *)
    fun mkLayered (AST.WildPat _, p) = p
      | mkLayered (p, AST.WildPat _) = p
      | mkLayered (AST.VarPat x, p) = AST.AsPat(x, p)
      | mkLayered (p, AST.VarPat x) = AST.AsPat(x, p)
      | mkLayered (p as AST.ConstPat _, _) = p
      | mkLayered (_, p as AST.ConstPat _) = p
      | mkLayered (AST.ConPat(dc, tys, p1), AST.ConPat(_, _, p2)) =
          AST.ConPat(dc, tys, mkLayered(p1, p2))
      | mkLayered (AST.TuplePat ps1, AST.TuplePat ps2) =
          AST.TuplePat(ListPair.mapEq mkLayered (ps1, ps2))
      | mkLayered (AST.AsPat(x, p1), p2) = AST.AsPat(x, mkLayered(p1, p2))
      | mkLayered (p1, AST.AsPat(x, p2)) = AST.AsPat(x, mkLayered(p1, p2))
      | mkLayered _ = raise Fail "impossible"

  (* check a qualified constructor ID *)
    fun chkDCon (cxt, qid) = (case ChkQualId.check(cxt, qid)
             of SOME(SOME strEnv, conid) => (case E.findDCon'(strEnv, conid)
                   of NONE => NONE
                    | someDC => someDC
                  (* end case *))
              | SOME(NONE, conid) => (case C.findDCon(cxt, conid)
                   of NONE => NONE
                    | someDC => someDC
                  (* end case *))
              | NONE => NONE
            (* end case *)
          (* end case *))

    fun check (cxt : C.t, depth, pat : BindTree.pat) = let
          fun chk (cxt, pat, binds) = (case pat
                 of BT.MarkPat{span, tree} => chk(C.setSpan(cxt, span), tree, binds)
                  | BT.ConAppPat(qid, pat) => let
                      val (pat, binds, ty) = chk (cxt, pat, binds)
                      in
                        case chkDCon (cxt, qid)
                         of SOME dc => (case TU.instantiate (DataCon.typeOf dc)
                               of (Ty.FunTy(argTy, resTy), tyArgs) => (
                                    if not(Unify.unify(argTy, ty))
                                      then error(cxt, [S "type mismatch in constructor pattern"])
                                      else ();
(* TODO: add type args to data constructors *)
                                    (AST.ConPat(dc, tyArgs, pat), binds, resTy))
                                | _ => (
                                    error(cxt, [
                                        S "application of nullary constructor ", qualId qid
                                      ]);
                                    (bogusPat, binds, Types.ErrorTy))
                              (* end case *))
                          | NONE => raise Fail "impossible"
                        (* end case *)
                      end
                  | BT.ConsPat(pat1, pat2) => let
                      val (Ty.FunTy(argTy, resTy), tyArgs) =
                            TU.instantiate (DataCon.typeOf PrimTy.listCons)
                      val (pat1, binds, ty1) = chk (cxt, pat1, binds)
                      val (pat2, binds, ty2) = chk (cxt, pat2, binds)
                      val pat = consPat tyArgs (pat1, pat2)
                      in
                        if not(Unify.unify(argTy, Ty.TupleTy[ty1, ty2]))
                          then error(cxt, [S "type mismatch in '::' pattern"])
                          else ();
                        (pat, binds, resTy)
                      end
                  | BT.TuplePat pats => let
                      fun chk' (pat, (pats, binds, tys)) = let
                            val (pat', binds, ty) = chk (cxt, pat, binds)
                            in
                              (pat'::pats, binds, ty::tys)
                            end
                      val (pats, binds, tys) = List.foldr chk' ([], binds, []) pats
                      in
                        case (pats, tys)
                         of ([], [])=> (AST.TuplePat[], binds, PrimTy.unitTy)
                          | ([pat], [ty]) => (pat, binds, ty)
                          | _ => (AST.TuplePat pats, binds, Ty.TupleTy tys)
                        (* end case *)
                      end
                  | BT.ListPat[] => let
                      val (ty, tyArgs) = TU.instantiate (DataCon.typeOf PrimTy.listNil)
                      val pat = nilPat tyArgs
                      in
                        (pat, binds, ty)
                      end
                  | BT.ListPat ps => let
                      val (Ty.FunTy(Ty.TupleTy[elemTy, _], resTy), tyArgs) =
                            TU.instantiate (DataCon.typeOf PrimTy.listCons)
                      fun chkElems ([], binds) = (nilPat tyArgs, binds)
                        | chkElems (p::pr, binds) = let
                            val (p', binds, ty) = chk (cxt, p, binds)
                            val _ = if not(Unify.unify(elemTy, ty))
                                  then error(C.setSpanFromPat(cxt, p), [
                                      S "element type mismatch in list pattern;\n",
                                      S "  expected: ", TY elemTy, S "\n",
                                      S "  found:    ", TY ty
                                    ])
                                  else ()
                            val (pr', binds) = chkElems (pr, binds)
                            in
                              (consPat tyArgs (p', pr'), binds)
                            end
                      val (listPat, binds) = chkElems (ps, binds)
                      in
                        (listPat, binds, resTy)
                      end
                  | BT.WildPat => let
                      val ty = Ty.MetaTy(MetaVar.new depth)
                      val x' = newWild ty
                      in
                        (AST.VarPat x', binds, ty)
                      end
                  | BT.ConPat qid => (case chkDCon (cxt, qid)
                       of SOME dc => (case TU.instantiate (DataCon.typeOf dc)
                               of (Ty.FunTy _, _) => (
                                    error(cxt, [
                                        S "missing arguments to data constructor ", qualId qid
                                      ]);
                                    (bogusPat, binds, Types.ErrorTy))
                                | (ty, tyArgs) => (AST.ConstPat(AST.DConst(dc, tyArgs)), binds, ty)
                              (* end case *))
                        | NONE => raise Fail "impossible"
                      (* end case *))
                  | BT.VarPat x => let
                      val ty = Ty.MetaTy(MetaVar.new depth)
                      val x' = Var.new(x, ty)
                      in
                        (AST.VarPat x', (x, x')::binds, ty)
                      end
                  | BT.AsPat(p1, p2) => let
                      val (p1', binds, ty1) = chk (cxt, p1, binds)
                      val (p2', binds, ty2) = chk (cxt, p2, binds)
                      in
                        if not(Unify.unify(ty1, ty2))
                          then (
                            error(cxt, [
                                S "type mismatch between arms of layered pattern;\n",
                                S "  lhs: ", TY ty1, S "\n",
                                S "  rhs: ", TY ty2
                              ]);
                            (bogusPat, binds, Types.ErrorTy))
                        (* check that the two patterns are not mutually exclusive *)
                          else if ASTUtil.compatiblePats(p1', p2')
                            then (mkLayered(p1', p2'), binds, ty1)
                            else (
                              error (cxt, [
                                  S "arms of layered pattern are mutually exclusive"
                                ]);
                              (bogusPat, binds, Types.ErrorTy))
                      end
                  | BT.ConstPat const => let
                      val (const', ty) = ChkLit.check (cxt, const)
                      in
                        (AST.ConstPat(AST.LConst(const', ty)), binds, ty)
                      end
                  | BT.ConstraintPat(p, ty) => let
                      val constraintTy = ChkType.check (cxt, ty)
                      val (p', binds, ty') = chk (cxt, p, binds)
                      in
                        if not(Unify.unify(ty', constraintTy))
                          then error(cxt, [S "type mismatch in constraint pattern"])
                          else ();
                        (p', binds, constraintTy)
                      end
                  | BT.ErrorPat => (bogusPat, binds, Ty.ErrorTy)
                (* end case *))
          in
            chk (cxt, pat, [])
          end

  end
