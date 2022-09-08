(* simplify.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Simplify a program.  This transformation involves normalizing by denesting
 * expressions and by compiling pattern matches.  We assume the following
 * properties about patterns in the input program, which are established by
 * the match-compilation phase:
 *
 *      1) all matches are exhaustive
 *
 *      2) all patterns in case and handle expressions are simple patterns
 *         consisting of either a constant, a variable, a tuple of variables,
 *         or a data constructor applied to a variable.
 *
 *      3) patterns on the LHS of a let binding are either a variable or a
 *         tuple of variables.
 *
 *      4) the argument pattern of a function definition is either a variable
 *         or a tuple of variables.
 *
 * Note: for now, we just flatten the top-level declarations into a big let binding and
 * then apply the simplification tansformation.  Eventually, we will need to deal
 * with structure imports and exports.
 *)

structure Simplify : sig

    val transform : AST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure A = AST
    structure Ty = Types
    structure S = SimpleAST
    structure SVar = SimpleVar
    structure STy = SimpleTypes
    structure STyUtil = SimpleTypeUtil
    structure POp = PrimOp
    structure SPrim = SimplePrim

    val unitTy = STy.ConTy([], SimplePrim.unitTyc)
    val boolTy = STy.ConTy([], SimplePrim.boolTyc)
    val boolFalse = SimplePrim.boolFalse
    val boolTrue = SimplePrim.boolTrue

    val typeOfExp = ASTUtil.typeOfExp
    val typeOfPat = ASTUtil.typeOfPat

    val newWild = SVar.newTmp "_"
    val newTmp = SVar.newTmp "_t"
    val newParam = SVar.newTmp "_param"
    val newArg = SVar.newTmp "_arg"
    val newRes = SVar.newTmp "_res"
    val newFlg = SVar.newTmp "_flg"
    val newFn = SVar.newTmp "_fn"

    fun monoVar x = S.A_Var(x, [])

  (* the environment tracks a mapping a bound AST type variables to Simple AST
   * type variables and the set of enclosing functions for the current context.
   * The latter is used to instantiate recursive mentions of a function with
   * their type arguments (since the type checker would have left them as
   * unapplied instances).
   *)
    datatype env = Env of {
        tvMap : SimplifyTy.tv_env,
        encFns : Var.Set.set
      }

    val emptyEnv = Env{tvMap = TyVar.Map.empty, encFns = Var.Set.empty}

    fun bindFns (Env{tvMap, encFns}, fbs) = Env{
            tvMap = tvMap,
            encFns = List.foldl (fn ((f, _, _), s) => Var.Set.add(s, f)) encFns fbs
          }

    fun cvtTy (Env{tvMap, ...}, ty) = SimplifyTy.cvtTy (tvMap, ty)
    fun cvtTys (Env{tvMap, ...}, tys) = SimplifyTy.cvtTys (tvMap, tys)

  (* a property to map AST variables to Simple AST *)
    local
      val {getFn : Var.t -> SVar.t, setFn, ...} =
            Var.newProp (fn x => raise Fail("unmapped variable " ^ Var.toString x))
    in
    fun cvtPolyVar (Env{tvMap, encFns}, x) = let
          val (tyScm', tvMap') = SimplifyTy.cvtTyScheme(tvMap, Var.typeOf x)
          val x' = SVar.newPoly(Var.nameOf x, tyScm')
          in
            setFn (x, x');
          (* propagate join attribute *)
            if Var.isJoin x then SVar.markJoin x' else ();
            (x', Env{tvMap = tvMap', encFns = encFns})
          end
  (* convert a variable that must be monomorphic *)
    fun cvtMonoVar (env, x) = let
          val x' = SVar.new(Var.nameOf x, cvtTy (env, Var.monoTypeOf x))
          in
            setFn (x, x');
            x'
          end
    fun getMonoVar x = monoVar (getFn x)
    fun getPolyVar (Env{tvMap, encFns}, x, tyArgs) = let
          val x' = getFn x
          in
            case (SimplifyTy.cvtTys(tvMap, tyArgs), Var.Set.member(encFns, x))
             of ([], true) => let
                (* A recursive use of x, so we need to instantiate it with its
                 * type variables mapped to their corresponding types. Note that
                 * because of mutually-recursive definitions, we cannot just
                 * grab the type variables from x'.
                 *)
                  val Ty.TyScheme(tvs, _) = Var.typeOf x
                  val tyArgs' = List.map
                        (fn tv => SimplifyTy.cvtTy(tvMap, A.VarTy tv))
                          tvs
                  in
                    S.A_Var(x', tyArgs')
                  end
              | (tyArgs', false) => S.A_Var(x', tyArgs')
              | _ => raise Fail("instantiation of recursive use of " ^ Var.toString x)
            (* end case *)
          end
    end

  (* unpack the elements of a tuple *)
    fun unpackTpl (tpl, tys, k) = let
          fun mk (_, [], args) = k (List.rev args)
            | mk (i, ty::tys, args) = let
                val arg = newArg ty
                in
                  S.mkLet(arg, S.mkSelect(i, tpl, []),
                    mk (i+1, tys, monoVar arg :: args))
                end
          in
            mk (1, tys, [])
          end

    fun resolve (A.OverloadExp(ref(A.Instance x))) = A.VarExp(x, [])
      | resolve (A.ApplyExp(A.OverloadExp(ref(A.Instance f)), arg, ty)) =
          A.ApplyExp(A.VarExp(f, []), arg, ty)
      | resolve exp = exp

  (* recursive calls to a function will be monomorphic (since SML does
   * not have polymorphic recursion), but we want to add the type arguments
   * to the call so that everything is
   * consistent.
   *)
    fun mkApply (env, f, tyArgs) = let
          val S.A_Var(f', tyArgs') = getPolyVar (env, f, tyArgs)
          in
            fn arg => S.mkApply(f', tyArgs', arg)
          end

    fun expToAtom (env, e, k : S.atom -> S.exp) = (case e
           of A.ConstExp(A.DConst(dc, tys)) =>
                k (S.A_DCon(SimplifyTy.cvtDCon dc, cvtTys (env, tys)))
            | A.ConstExp(A.LConst(lit, ty)) => k (S.A_Lit(lit, cvtTy (env, ty)))
            | A.VarExp(x, tys) => varToAtom (env, x, tys, k)
            | _ => let
                val x = newTmp(cvtTy(env, typeOfExp e))
                in
                  rhsToLetExp (env, x, e, k (monoVar x))
                end
          (* end case *))

    and varToAtom (env, x, tys, k : S.atom -> S.exp) = (case PrimEnv.lookup x
           of PrimEnv.NotPrim => k (getPolyVar(env, x, tys))
          (* for primops, we make a `fn` expression and then convert *)
            | _ => let
                val Ty.TyScheme(tvs, Ty.FunTy(domTy, rngTy)) = Var.typeOf x
                val param = Var.newTmp "_param" domTy
                val body = A.ApplyExp(
                      A.VarExp(x, List.map Ty.VarTy tvs),
                      AST.VarExp(param, []),
                      rngTy)
                val fb' as S.FB(f', _, _, _) = funToFun env (Var.copy x, [param], body)
                in
                  S.mkFun([fb'], k (S.A_Var(f', cvtTys (env, tys))))
                end
          (* end case *))

    and expsToAtoms (env, es, k) = let
          fun lp ([], atms) = k (List.rev atms)
            | lp (e::es, atms) = expToAtom (env, e, fn atm => lp (es, atm::atms))
          in
            lp (es, [])
          end

    and expToPrimArgs (env, 1, e, k) = expToAtom(env, e, fn atm => k [atm])
      | expToPrimArgs (env, _, A.TupleExp es, k) = expsToAtoms(env, es, k)
      | expToPrimArgs (env, _, e, k) = expToAtom(env, e, fn (S.A_Var(tpl, tys)) =>
          case STyUtil.applyScheme(SVar.typeOf tpl, tys)
           of STy.TupleTy tys => unpackTpl (tpl, tys, k)
            | ty => raise Fail("expected tuple type, but found " ^ STyUtil.toString ty)
          (* end case *))

  (* convert an AST expression to a SimpleAST expression where the resulting expression
   * will be on the RHS of a let binding.
   *)
    and rhsToLetExp (env, lhs, rhs, e' : S.exp) = (case SVar.typeOf lhs
           of STy.TyScheme([], _) => S.mkLet(lhs, expToExp(env, rhs), e')
            | STy.TyScheme(tvs, _) => let
                fun mk e = S.mkLetPoly(lhs, tvs, e, e')
              (* the rhs is a "value", but because of simplification it might
               * be formed from nested let expressions.  Therefore, we denest.
               *)
                fun denest (S.E(lab, S.E_Let(x, e1, e2))) =
                      S.E(lab, S.E_Let(x, e1, denest e2))
                  | denest (S.E(lab, S.E_LetPoly(x, tvs, e1, e2))) =
                      S.E(lab, S.E_LetPoly(x, tvs, e1, denest e2))
                  | denest (S.E(lab, S.E_Fun(fbs, e))) =
                      S.E(lab, S.E_Fun(fbs, denest e))
                  | denest (e as S.E(_, S.E_DConApp _)) = mk e
                  | denest (e as S.E(_, S.E_Tuple _)) = mk e
                  | denest (e as S.E(_, S.E_Select _)) = mk e
                  | denest (e as S.E(_, S.E_Atom _)) = mk e
                  | denest e = raise Fail "lhs is not a value"
                in
                  denest (expToExp(env, rhs))
                end
          (* end case *))

  (* convert an AST expression to a SimpleAST expression where the resulting
   * expression will be in a tail context
   *)
    and expToExp (env, exp) = (case exp
(* TODO: the `lhsScm` tells us if this is a polymorphic binding *)
           of A.LetExp(A.ValDecl(A.VarPat x, lhsScm, rhs), e) => let
              (* This could be a polymorphic binding *)
                val (x', env') = cvtPolyVar (env, x)
                in
                  rhsToLetExp (env', x', rhs, expToExp(env', e))
                end
            | A.LetExp(A.ValDecl(pat, lhsScm, rhs), e) => (
              (* Note that the lhs pattern should be exhaustive *)
                case simplifyPattern (env, pat, fn env => expToExp(env, e))
                 of (pat' as S.P_DConApp _, e') =>
                    (* `let con arg = rhs in e` ==> `case rhs of con arg => e` *)
                      expToAtom (env, rhs, fn atm =>
                        S.mkCase(atm, [S.mkRULE(pat', e')], cvtTy(env, typeOfExp e)))
(* FIXME: this case does not handle polymorphic x, but the rule above does that
 * for now.  Needs to be fixed to support tuples of polymorphic variables.
 *)
                  | (S.P_Var x, e') => rhsToLetExp (env, x, rhs, e')
                  | (S.P_DCon(dc, tys), e') => let
                    (* `let con = rhs in e` ==> `let _ = rhs in e` *)
                      val ty = STyUtil.applyScheme(SimpleDataCon.typeOf dc, tys)
                      in
                        rhsToLetExp (env, newWild ty, rhs, e')
                      end
                  | (S.P_Lit(lit, ty), e') => raise Fail "unexpected literal pattern"
                (* end case *))
            | A.LetExp(A.FunDecl fbs, e) => let
              (* record that we are processing the functions *)
                val env' = bindFns (env, fbs)
              (* first pass converts function names to Simple AST *)
                fun pass1 (f, [param], body) = let
                      val (f', env') = cvtPolyVar (env', f)
                      in
                        (env', f', param, body)
                      end
                val fbs' = List.map pass1 fbs
              (* the second pass processes the function bodies *)
                fun pass2 (env, f, param, body) = let
                      val param' = cvtMonoVar (env, param)
                      val body' = expToExp(env, body)
                      in
                        S.mkFB(f, param', body')
                      end
                in
                  S.mkFun(List.map pass2 fbs', expToExp(env, e))
                end
            | A.IfExp(e1, e2, e3, ty) => let
                val e2' = expToExp(env, e2)
                val e3' = expToExp(env, e3)
		val ty' = cvtTy(env, ty)
		fun mkBoolCase (atm, thenE, falseE, ty') =
		      S.mkCase(atm, [
			    S.mkRULE(S.P_DCon(SPrim.boolTrue, []), thenE),
			    S.mkRULE(S.P_DCon(SPrim.boolFalse, []), falseE)
			  ],
			ty')
                fun mkIf () = expToAtom(env, e1, fn atm =>
		      mkBoolCase (atm, e2', e3', ty'))
                fun mkTst (tst, arg) =
                      expToPrimArgs (env, POp.Test.arity tst, arg, fn atms =>
                        S.mkIf(tst, atms, e2', e3', ty'))
                in
                  case resolve e1
                   of A.ApplyExp(A.VarExp(f, tyArgs), arg, _) => (case PrimEnv.lookup f
                         of PrimEnv.NotPrim => mkIf()
                          | PrimEnv.EqTest flg => let
                              val [ty] = cvtTys (env, tyArgs)
                              in
                                case Equality.eqTest(flg, ty)
                                 of Equality.PrimTest tst => mkTst (tst, arg)
                                  | Equality.EqFun f => let
(* FIXME: should generate a `case` on the result here! *)
                                      val res = newFlg boolTy
                                      val res' = monoVar res
                                      in
                                        expToAtom (env, arg, fn atm =>
                                          S.mkLet(res, S.mkApply(f, [], atm),
                                            if flg
                                              then mkBoolCase(res', e2', e3', ty)
                                              else mkBoolCase(res', e3', e2', ty)))
                                      end
                                (* end case *)
                              end
                          | PrimEnv.Test tst => mkTst (tst, arg)
                          | _ => raise Fail "impossible"
                        (* end case *))
                    | _ => mkIf()
                  (* end case *)
                end
            | A.CaseExp(e, cases, ty) => let
                fun simplify (pat, exp) =
                      S.mkRULE(simplifyPattern(env, pat, fn env => expToExp(env, exp)))
                in
                  expToAtom (env, e, fn atm =>
                    S.mkCase(atm, List.map simplify cases, cvtTy(env, ty)))
                end
          (* NOTE: the pattern match compiler will have already simplified the handler *)
            | A.HandleExp(e, [(A.VarPat ex, hndlr)], ty) => let
                val e' = expToExp (env, e)
                val ex' = cvtMonoVar (env, ex)
                val hndlr' = expToExp (env, hndlr)
                val ty' = cvtTy(env, ty)
                in
                  S.mkHandle(e', ex', hndlr', ty')
                end
            | A.HandleExp _ => raise Fail "expected simple handler"
            | A.RaiseExp(loc, e, ty) =>
                expToAtom (env, e, fn atm => S.mkRaise(loc, atm, cvtTy(env, ty)))
            | A.FunExp(pat, e, ty) => funToExp (env, pat, e, ty)
            | A.ApplyExp(A.ConstExp(A.DConst(dc, tys)), e2, _) => let
                val dc' = SimplifyTy.cvtDCon dc
                val tys' = cvtTys (env, tys)
                in
                  expToAtom (env, e2, fn arg => S.mkDConApp(dc', tys', arg))
                end
            | A.ApplyExp(e1, e2, _) => (case resolve e1
                 of A.VarExp(f, tys) => let
                      val tys' = cvtTys (env, tys)
                      fun mkTst tst = let
                            val STy.FunTy(_, resTy) =
                                  cvtTy (env, TypeUtil.applyScheme(Var.typeOf f, tys))
                            fun mk args = S.mkIf(tst, args,
                                  S.mkAtom(S.A_DCon(boolTrue, [])),
                                  S.mkAtom(S.A_DCon(boolFalse, [])),
                                  resTy)
                            in
                              expToPrimArgs (env, POp.Test.arity tst, e2, mk)
                            end
                      in
                        case PrimEnv.lookup f
                         of PrimEnv.NotPrim => expToAtom(env, e2, mkApply(env, f, tys))
                          | PrimEnv.Pure rator =>
                              expToPrimArgs (env, POp.Pure.arity rator, e2, fn args =>
                                S.mkPrim(S.Pure rator, tys', args))
                          | PrimEnv.Arith rator =>
                              expToPrimArgs (env, POp.Arith.arity rator, e2, fn args =>
                                S.mkPrim(S.Arith rator, tys', args))
                          | PrimEnv.Getter rator =>
                              expToPrimArgs (env, POp.Getter.arity rator, e2, fn args =>
                                S.mkPrim(S.Getter rator, tys', args))
                          | PrimEnv.Setter rator =>
                              expToPrimArgs (env, POp.Setter.arity rator, e2, fn args =>
                                S.mkPrim(S.Setter rator, tys', args))
                          | PrimEnv.EqTest flg => let
                              val [ty] = cvtTys (env, tys)
                              in
                                case Equality.eqTest(flg, ty)
                                 of Equality.PrimTest tst => mkTst tst
                                  | Equality.EqFun f =>
                                      expToAtom(env, e2, fn arg => S.mkApply(f, [], arg))
                                (* end case *)
                              end
                          | PrimEnv.Test tst => mkTst tst
                        (* end case *)
                      end
                  | _ => expToAtom (env, e1, fn (S.A_Var(f, tys)) =>
                      expToAtom (env, e2, fn arg =>
                        S.mkApply(f, tys, arg)))
                (* end case *))
            | A.TupleExp[] => S.mkAtom S.A_Unit
            | A.TupleExp es => expsToAtoms (env, es, fn atms => S.mkTuple atms)
            | A.ConstExp _ => expToAtom (env, exp, S.mkAtom)
            | A.VarExp(x, tys) => varToAtom (env, x, tys, S.mkAtom)
            | A.SeqExp(e1, e2) => let
                val x = newTmp(cvtTy(env, typeOfExp e1))
                in
                  rhsToLetExp(env, x, e1, expToExp(env, e2))
                end
            | A.OverloadExp ovld => (case !ovld
                 of A.Unknown _ => raise Fail "unresolved overload"
                  | A.Instance x => varToAtom (env, x, [], S.mkAtom)
                (* end case *))
          (* end case *))

  (* convert a single, non-recursive, AST function to Simple AST *)
    and funToFun env (f, [x], exp) = let
          val (f', env') = cvtPolyVar (env, f)
          val x' = cvtMonoVar (env', x)
          in
            S.mkFB(f', x', expToExp(env', exp))
          end
      | funToFun _ _ = raise Fail "unexpected curried function definition"

    and funToExp (env, x, body, ty) =  let
          val x' = cvtMonoVar (env, x)
          val f' = newFn (STy.FunTy(SVar.monoTypeOf x', cvtTy(env, ty)))
          in
            S.mkFun([S.mkFB(f', x', expToExp(env, body))], S.mkAtom(monoVar f'))
          end

  (* given an AST pattern and a function that returns the SimpleAST expression
   * that is the pattern's scope, return a pair of the simple pattern and a
   * possibly modified expression.  The expression is represented by a function
   * because variable bindings in the pattern need to be processed *before*
   * the expression.
   *)
    and simplifyPattern (env, pat, mkExp : env -> S.exp) = let
          fun return pat = (pat, mkExp env)
          in
            case pat
             of A.VarPat x => let
                  val (x', env') = cvtPolyVar (env, x)
                  in
                    (S.P_Var x', mkExp env')
                  end
              | A.WildPat ty => return (S.P_Var(newTmp(cvtTy(env, ty))))
              | A.ConstPat(A.DConst(dc, tys)) => let
                  val dc' = SimplifyTy.cvtDCon dc
                  val tys' = cvtTys (env, tys)
                  in
                    return (S.P_DCon(dc', tys'))
                  end
              | A.ConstPat(A.LConst(lit, ty)) =>
                  return (S.P_Lit(lit, cvtTy(env, ty)))
              | A.ConPat(dc, tys, A.VarPat x) => let
                  val dc' = SimplifyTy.cvtDCon dc
                  val tys' = cvtTys (env, tys)
                  val (x', env') = cvtPolyVar (env, x)
                  in
                    (S.P_DConApp(dc', tys', x'), mkExp env')
                  end
              | A.ConPat(dc, tys, A.WildPat ty) => let
                  val dc' = SimplifyTy.cvtDCon dc
                  val tys' = cvtTys (env, tys)
                  val x' = newTmp (cvtTy(env, ty))
                  in
                    return (S.P_DConApp(dc', tys', x'))
                  end
              | A.ConPat _ => raise Fail(concat[
                    "expected simple pattern '", ASTUtil.patToString pat, "'"
                  ])
              | A.TuplePat[] => return (S.P_Var(newTmp SimpleASTUtil.unitTy))
              | A.TuplePat apats => let
(* FIXME: we cannot handle tuple patterns that bind polymorphic variables;
 * e.g., tests/good26.sml
 *)
                  val x = newArg(cvtTy(env, typeOfPat pat))
                  fun mkBinds (_, []) = mkExp env
                    | mkBinds (i, pat::pats) = (case pat
                         of A.VarPat y => let
                              val y' = cvtMonoVar (env, y)
                              in
                                S.mkLet(y', S.mkSelect(i, x, []), mkBinds (i+1, pats))
                              end
                          | A.WildPat _ => mkBinds (i+1, pats)
                          | _ => raise Fail(concat[
                                "expected variable pattern, but found '",
                                ASTUtil.patToString pat, "'"
                              ])
                        (* end case *))
                  val exp' = mkBinds (1, apats)
                  in
                    (S.P_Var x, exp')
                  end
              | A.AsPat _ => raise Fail "unexpected layered pattern"
            (* end case *)
          end

    val newCU = Var.newTmp "_compUnit"

    fun flattenCU (tops : AST.comp_unit) = let
          fun flatten (tops, binds) = List.foldr flattenTop binds tops
          and flattenTop (top, binds) = (case top
                 of A.StructTopDec(_, A.IdStrExp _) => binds (* ?? *)
                  | A.StructTopDec(_, A.DefStrExp(sign, tops)) => flatten(tops, binds)
(* FIXME: what about exception constructors? *)
                  | A.DConTopDec dc => binds
                  | A.ValTopDec bind => AST.LetExp(bind, binds)
                (* end case *))
          val f = newCU (Ty.FunTy(PrimTy.unitTy, PrimTy.unitTy))
          in
            (f, [Var.newTmp "_wild" PrimTy.unitTy], flatten (tops, AST.TupleExp[]))
          end

    fun transform (cu : A.comp_unit) = let
          val fb as S.FB(f, lab, param, body) = funToFun emptyEnv (flattenCU cu)
          in
            case Equality.getEqTests()
             of [] => S.CU fb
              | fbs => S.CU(S.FB(f, lab, param, S.mkFun(fbs, body)))
            (* end case *)
          end

  end
