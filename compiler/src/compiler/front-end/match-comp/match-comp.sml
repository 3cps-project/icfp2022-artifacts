(* match-comp.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Compile arbitrary pattern matching to decision trees.  Note that
 * the typechecker tests for nonexhaustive matches and adds extra
 * clauses as required, so we can assume that all matches are
 * exhaustive.
 *
 * We also simplify function declarations by converting functions of the
 * form
 *
 *      fun f p1 p2 = e
 *
 * to
 *
 *      fun f x1 = let
 *          fun f2 x2 = case (x1, x2) of (p1, p2) => e
 *          in
 *            f2
 *          end
 *
 * TODO: support alternative compilation schemes
 *)

structure MatchComp : sig

    val transform : AST.comp_unit -> AST.comp_unit

  end = struct

    structure A = AST
    structure Ty = Types

    fun debug () = Controls.get Ctl.debugMatch
    fun say s = Log.msg("[MC] " :: s)

  (* temporary varables *)
    val newTmp = Var.newTmp "_t"
    val newTmp' = Var.newPolyTmp "_t"
    val newParam = Var.newTmp "_param"
    val newArg = Var.newTmp "_arg"
    val newEx = Var.newTmp "_ex"

    fun letVal (lhs, tyScm, rhs, e) = A.LetExp(A.ValDecl(lhs, tyScm, rhs), e)

    val isVarPat = ASTUtil.isVarPat

  (* test if a pattern is simple *)
    fun isSimplePat p = (case p
           of A.VarPat _ => true
            | A.WildPat _ => true
            | A.ConstPat(A.DConst _) => true
            | A.ConstPat _ => raise Fail "unexpected refutable pattern"
            | A.ConPat(_, _, p) => isVarPat p
            | A.TuplePat ps => List.all isVarPat ps
            | A.AsPat(_, p) => isSimplePat p
          (* end case *))

  (* simplify a binding pattern that is known to be exhaustive.  For example, say
   * we have the following code:
   *
   *    datatype ('a, 'b) t = A of 'a * 'b
   *      ...
   *    let val A(A(x,y),A(z,w)) = rhs in exp end
   *
   * it will simplify to
   *
   *    let val A ab = rhs
   *        val (a, b) = ab
   *        val A xy = a
   *        val (x, y) = xy
   *        val A zw = b
   *        val (z, w) = zw
   *    in
   *      exp
   *    end
   *
   * where `a` and `b` are fresh variables.
   *)
    fun simplifyBinding (lhs, Ty.TyScheme(tvs, lhsTy), rhs, exp) = let
          fun mkScm ty = TypeUtil.bindFreeTVs (tvs, ty)
          fun mkVarExp (x, Ty.TyScheme(tvs, _)) =
                A.VarExp(x, List.map Ty.VarTy tvs)
          fun f (p as A.ConPat(dc, tys, p'), ty, rhs, k) = if isVarPat p'
                  then letVal(p, mkScm ty, rhs, k())
                  else let
                    val argTy = valOf(DataCon.argTypeOf'(dc, tys))
                    val scm = mkScm argTy
                    val x = newTmp' scm
                    in
                      letVal(
                        A.ConPat(dc, tys, A.VarPat x), mkScm ty, rhs,
                        f (p', argTy, mkVarExp(x, scm), k))
                    end
            | f (p as A.TuplePat ps, ty, rhs, k) = if List.all isVarPat ps
                  then letVal(p, mkScm ty, rhs, k())
                  else let
                    val Ty.TupleTy tys = TypeUtil.prune ty
                    fun doArgs ([], _, args', k) = letVal(
                          A.TuplePat(List.rev args'), mkScm ty, rhs,
                          k())
                      | doArgs (p::pr, ty::tys, args', k) = if isVarPat p
                          then doArgs(pr, tys, p::args', k)
                          else let
                            val scm = mkScm ty
                            val x = newTmp' scm
                            fun k' () = f (p, ty, mkVarExp(x, scm), k)
                            in
                              doArgs (pr, tys, AST.VarPat x :: args', k')
                            end
                      | doArgs _ = raise Fail "tuple-pattern/tuple-type mismatch"
                    in
                      doArgs (ps, tys, [], k)
                    end
            | f (A.AsPat(x, p), ty, rhs, k) = let
                val scm = mkScm ty
                in
                  letVal(A.VarPat x, scm, rhs, f (p, ty, mkVarExp(x, scm), k))
                end
            | f (p, ty, rhs, k) = letVal(p, mkScm ty, rhs, k())
          in
            f (lhs, lhsTy, rhs, fn () => exp)
          end

  (* do a bottom-up rewrite of an expression where bindings are simplified and
   * cases (CaseExp and HandleExp) are compiled.
   *)
    fun xform e = (case e
           of A.LetExp(A.ValDecl(lhs, tyScm, rhs), e) => (
                if debug()
                  then say["`let ", ASTUtil.patToString lhs, " = ...`\n"]
                  else ();
                simplifyBinding (lhs, tyScm, xform rhs, xform e))
            | A.LetExp(A.FunDecl fbs, e) =>
                A.LetExp(A.FunDecl(List.map xformFB fbs), xform e)
            | A.IfExp(e1, e2, e3, ty) => A.IfExp(xform e1, xform e2, xform e3, ty)
            | A.CaseExp(e, cases, ty) => let
                val arg = newArg(ASTUtil.typeOfExp e)
                in
                  letVal(A.VarPat arg, Var.typeOf arg, e, matchComp(arg, cases, ty))
                end
            | A.HandleExp(e, cases, ty) => let
                val ex = newEx PrimTy.exnTy
                val hndlr = matchComp(ex, cases, ty)
                in
                  A.HandleExp(xform e, [(A.VarPat ex, hndlr)], ty)
                end
            | A.RaiseExp(loc, e, ty) => A.RaiseExp(loc, xform e, ty)
            | A.FunExp(x, e, ty) => A.FunExp(x, xform e, ty)
            | A.ApplyExp(e1, e2, ty) => A.ApplyExp(xform e1, xform e2, ty)
            | A.TupleExp es => A.TupleExp(List.map xform es)
            | A.ConstExp _ => e
            | A.SeqExp(e1, e2) => A.SeqExp(xform e1, xform e2)
            | A.VarExp _ => e
            | A.OverloadExp _ => e
          (* end case *))

  (* we convert a curried declaration `fun f x1 x2 ... = e` into
   * nested declarations so that any function declaration has
   * at most one argument.
   *)
    and xformFB (f, [x], e) = (
          if debug()
            then say[
                "`fun ", Var.toString f, " ", Var.toString x, " = ...`\n"
              ]
            else ();
          (f, [x], xform e))
      | xformFB (f, x::xr, e) = let
          val newFun = Var.newTmp (Var.nameOf f)
          val Ty.TyScheme(_, Ty.FunTy(argTy, retTy)) = Var.typeOf f
          fun curry ([], _) = xform e
            | curry (x::xr, Ty.FunTy(argTy, retTy)) = let
                val f = newFun(Ty.FunTy(argTy, retTy))
                in
                  A.LetExp(
                    A.FunDecl[(f, [x], curry(xr, retTy))],
                    A.VarExp(f, []))
                end
          in
            if debug()
              then say[
                  "`fun ", Var.toString f, " ",
                  String.concatWithMap " " Var.toString (x::xr), " = ...`\n"
                ]
              else ();
            (f, [x], curry(xr, retTy))
          end

    and matchComp (x, cases, ty) = let
        (* first we recursively process the actions of the cases *)
          val cases' = List.map (fn (p, e) => (p, xform e)) cases
          in
            BacktrackMC.transform (x, cases', ty)
          end

    fun transform tops = let
          fun xformTop (A.StructTopDec(strId, strExp)) = let
                val strExp' = (case strExp
                       of A.IdStrExp _ => strExp
                        | A.DefStrExp(sign, tops) =>
                            A.DefStrExp(sign, List.map xformTop tops)
                      (* end case *))
                in
                  A.StructTopDec(strId, strExp')
                end
            | xformTop (top as A.DConTopDec _) = top
            | xformTop (A.ValTopDec(A.ValDecl(lhs, tyScm, rhs))) =
                if isSimplePat lhs
                  then A.ValTopDec(A.ValDecl(lhs, tyScm, xform rhs))
                  else let
                  (* copy a pattern while alpha-converting the bound variables.
                   * Returns the new pattern, plus the lists of the old and
                   * new variables.
                   *)
                    fun copyPat (pat, xs, xs') = (case pat
                           of A.VarPat x => let
                                val x' = Var.copy x
                                in
                                  (A.VarPat x', x::xs, x'::xs')
                                end
                            | A.WildPat _ => (pat, xs, xs')
                            | A.ConstPat(A.DConst _) => (pat, xs, xs')
                            | A.ConPat(dc, tys, pat) => let
                                val (pat', xs, xs') = copyPat (pat, xs, xs')
                                in
                                  (A.ConPat(dc, tys, pat'), xs, xs')
                                end
                            | A.TuplePat ps => let
                                fun f (p, (ps, xs, xs')) = let
                                      val (p', xs, xs') = copyPat (p, xs, xs')
                                      in
                                        (p'::ps, xs, xs')
                                      end
                                val (ps', xs, xs') = List.foldr f ([], xs, xs') ps
                                in
                                  (A.TuplePat ps', xs, xs')
                                end
                            | _ => raise Fail "unexpected refutable pattern"
                          (* end case *))
                    val (pat', xs, xs') = copyPat (lhs, [], [])
                    val lhs' = A.TuplePat(List.map A.VarPat xs)
                    val rhs' = simplifyBinding (
                          pat', tyScm, xform rhs,
                          A.TupleExp(List.map (fn x => A.VarExp(x, [])) xs'))
                    in
                      A.ValTopDec(A.ValDecl(lhs', tyScm, rhs'))
                    end
            | xformTop (A.ValTopDec(A.FunDecl fbs)) =
                A.ValTopDec(A.FunDecl(List.map xformFB fbs))
          in
            List.map xformTop tops
          end

  end
