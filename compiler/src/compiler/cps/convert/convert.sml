(* convert.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Conversion from SimpleAST to CPS.
 *)

structure Convert : sig

    val transform : SimpleAST.comp_unit -> CPS.comp_unit

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure Var = SimpleVar
    structure TVMap = TyVar.Map
    structure VMap = Var.Map
    structure P = PrimOp

    structure C = CPS
    structure CTy = CPSTypes
    structure CUtil = CPSUtil
    structure Ex = Extent

  (* an environment for tracking standard exceptions *)
    structure XMap = ListMapFn (
      struct
        type ord_key = CPSDataCon.t
        val compare = CPSDataCon.compare
      end)

  (* count syntatic analysis extent assignments *)
    structure ST = Stats

    val cntrs = ST.Group.newWithPri ST.Group.root ("convert", [2, 0])
    local
      val newCntr = ST.Counter.new cntrs
    in
  (* assignments of SimpleAST variables *)
    val cntHeap = newCntr "heap-lvar"
    val cntStk = newCntr "stk-lvar"
    val cntReg = newCntr "reg-lvar"
    fun cntLVar (Ex.HEAP) = ST.Counter.tick cntHeap
      | cntLVar (Ex.STK) = ST.Counter.tick cntStk
      | cntLVar (Ex.REG) = ST.Counter.tick cntReg
  (* for temporary LVars introduced by conversion *)
    val cntHeapTmpLVar = newCntr "heap-tmp-lvar"
    val cntStkTmpLVar = newCntr "stk-tmp-lvar"
    val cntRegTmpLVar = newCntr "reg-tmp-lvar"
    fun cntTmpLVar (Ex.HEAP) = ST.Counter.tick cntHeapTmpLVar
      | cntTmpLVar (Ex.STK) = ST.Counter.tick cntStkTmpLVar
      | cntTmpLVar (Ex.REG) = ST.Counter.tick cntRegTmpLVar
  (* for temporary CVars introduced by conversion *)
    val cntHeapTmpCVar = newCntr "heap-tmp-cvar"
    val cntStkTmpCVar = newCntr "stk-tmp-cvar"
    val cntRegTmpCVar = newCntr "reg-tmp-cvar"
    fun cntTmpCVar (Ex.HEAP) = ST.Counter.tick cntHeapTmpCVar
      | cntTmpCVar (Ex.STK) = ST.Counter.tick cntStkTmpCVar
      | cntTmpCVar (Ex.REG) = ST.Counter.tick cntRegTmpCVar
    end

  (* new variables *)
    local
      fun newLVar name (ty, ext) =
          (cntTmpLVar ext; LVar.newTmp (name, CPSTypes.TyScheme([], ty), ext))
      fun newCVar name (ty, ext) =
          (cntTmpCVar ext; CVar.newTmp (name, ty, ext))
    in
    val newAtm =   newLVar "_atm"
    val newArg =   newLVar "_arg"
    val newExn =   newLVar "_exn"
    val newRes =   newLVar "_res"
    val newUnit =  newLVar "_un"
    val newExhK =  newCVar "_exhk"
    val newHndlK = newCVar "_hndlk"
    val newJoin =  newCVar "_join"
    val newRetK =  newCVar "_retk"
    end (* local *)

    val zero = C.LIT(Literal.Int 0, CPSPrimTy.intTy)

  (* the environment tracks both variable and type variable bindings *)
    datatype env = E of {
        tvMap : CTy.tyvar TVMap.map,
        vMap : LVar.t VMap.map
      }

  (* the continuation environment tracks the current exception handler
   * continuation.  It also has flags to record the need for raising standard
   * exceptions.
   *)
    datatype kenv = KE of {
        exhK : CVar.t,
        raiseKs : C.cvar XMap.map ref
      }

  (* return the current exception handler continuation *)
    fun getExh (KE{exhK, ...}) = exhK

  (* get a continuation that will raise the specified exception in the current
   * exception handler context.
   *)
    fun raiseExn (KE{exhK, raiseKs}, exn) = (case XMap.find(!raiseKs, exn)
           of SOME k => k
            | NONE => let (* need to create a new continuation *)
                val k = CVar.newTmp("raise" ^ CPSDataCon.nameOf exn, CTy.ContTy[], Ex.STK)
                in
                  ST.Counter.tick cntStkTmpCVar;
                  raiseKs := XMap.insert(!raiseKs, exn, k);
                  k
                end
          (* end case *))

  (* when we enter a new exception-handler scope, we need to define new
   * exception-raising continuations.
   *)
    fun withKEnv (exhK, f) = let
          val raiseKs = ref XMap.empty
          val kenv = KE{exhK = exhK, raiseKs = raiseKs}
          val e = f kenv
          fun bindK (exnCon, k, e) = let
                val ex = newExn (CPSPrimTy.exnTy, Ex.HEAP)
                in
                  C.mkLETCONT(
                    [C.mkCLambda (k, [], C.mkATOM(C.DCON(exnCon, []), ex, C.mkTHROW(exhK, [ex])))],
                    e)
                end
          in
            XMap.foldli bindK e (!raiseKs)
          end

  (* a property to map Simple AST functions that are join points to
   * continuations.  Note that this property is only set when the
   * `joinConts` control is enabled.
   *)
    local
      val {setFn : Var.t * CPS.cvar -> unit, peekFn, ...} =
            Var.newProp (fn f => raise Fail(concat[
                "no join continuation for '", Var.toString f, "'"
              ]))
    in
    val setJoinCont = setFn
    val getJoinCont = peekFn
    end

(* DEBUG *)
    fun prTyVarMap (prefix, tvMap) = (
          print (prefix ^ ": tvMap = {\n");
          List.app
            (fn (x, x') => print(concat["  ", TyVar.toString x, " -> ", CPSTyVar.toString x', "\n"]))
              (TVMap.listItemsi tvMap);
          print "}\n")
    fun prTyVarMap' (prefix, E{tvMap, ...}) = prTyVarMap (prefix, tvMap)
    fun prVarMap (prefix, vMap) = (
          print (prefix ^ ": vMap = {\n");
          List.app
            (fn (x, x') => print(concat["  ", Var.toString x, " -> ", LVar.toString x', "\n"]))
              (VMap.listItemsi vMap);
          print "}\n")
(* DEBUG *)

    val emptyEnv = E{tvMap = TVMap.empty, vMap = VMap.empty}

  (* type conversion *)
    fun cvtTy (E{tvMap, ...}) = ConvertTy.cvtTy tvMap
    fun cvtTys (env, tys) = List.map (cvtTy env) tys
    fun dconOf (E{tvMap, ...}, dc) = ConvertTy.dconOf(tvMap, dc)

    fun bindTVs (tvMap, tvs) = let
          fun bind ([], tvs', tvMap') = (List.rev tvs', tvMap')
            | bind (tv::tvr, tvs', tvMap') = let
                val tv' = CPSTyVar.new()
                in
                  bind (tvr, tv'::tvs', TVMap.insert(tvMap', tv, tv'))
                end
          in
            bind (tvs, [], tvMap)
          end

    fun bindVar (E{tvMap, vMap}, x) = let
          val Ty.TyScheme(tvs, ty) = Var.typeOf x
          val (tvs', tvMap) = bindTVs (tvMap, tvs)
          val ext = VarAnalysis.getExtent x
          val x' = LVar.newTmp(
                Var.nameOf x,
                CTy.TyScheme(tvs', ConvertTy.cvtTy tvMap ty),
                ext)
          in
            cntLVar ext;
            (x', E{tvMap=tvMap, vMap=VMap.insert(vMap, x, x')})
          end
(*DEBUG*)
handle ex => (print(concat["bindVar (-, ", Var.toString x, ")\n"]); raise ex)

    fun rename (E{vMap, ...}) x = (case VMap.find(vMap, x)
           of SOME x' => x'
            | NONE => (
(*DEBUG*)
prVarMap ("rename", vMap);
raise Fail(concat["unable to rename '", Var.toString x, "'"])
)
          (* end case *))

    fun cvtPat (env, S.P_DConApp(dc, tys, x)) = let
          val (x', env') = bindVar (env, x)
          in
            (C.DCPAT(dconOf(env, dc), cvtTys(env, tys), SOME x'), env')
          end
      | cvtPat (env, S.P_Var x) = let
          val (x', env') = bindVar (env, x)
          in
            (C.VPAT x', env')
          end
      | cvtPat (env, S.P_DCon(dc, tys)) =
            (C.DCPAT(dconOf(env, dc), cvtTys(env, tys), NONE), env)
      | cvtPat (env, S.P_Lit(lit, ty)) = (C.LPAT(lit, cvtTy env ty), env)
(*DEBUG*)
val cvtPat = fn (env, p) => (cvtPat (env, p)
handle ex => (print(concat["cvtPat(-, ", SimpleASTUtil.patToString p, ")\n"]); raise ex))

    fun cvtAtm (env, S.A_Var(x, tys)) = C.LVAR(rename env x, cvtTys(env, tys))
      | cvtAtm (env, S.A_DCon(dc, tys)) = C.DCON(dconOf(env, dc), cvtTys(env, tys))
      | cvtAtm (env, S.A_Lit(lit, ty)) = C.LIT(lit, cvtTy env ty)
      | cvtAtm (_, S.A_Unit) = C.UNIT
(*DEBUG*)
val cvtAtm = fn (env, atm) => (cvtAtm (env, atm)
handle ex => (prTyVarMap'(concat["cvtAtm(-, ", SimpleASTUtil.atomToString atm, ")\n"], env); raise ex))

    fun cvtAtms (env, atms) = List.map (fn atm => cvtAtm (env, atm)) atms

    fun atomToVar (env, atm, k) = (case cvtAtm (env, atm)
           of C.LVAR(x, []) => k x
            | atm' as C.LVAR(x, tys) => let
                val ty =  CTy.TyScheme([], CPSTypeUtil.applyScheme(LVar.typeOf x, tys))
                val x' = LVar.newTmp (LVar.nameOf x, ty, LVar.extentOf x)
                in
                  cntTmpLVar (LVar.extentOf x);
                  C.mkATOM(atm', x', k x')
                end
            | atm' => let
                val x = newAtm (CUtil.typeOfAtom atm', Ex.STK)
                in
                  C.mkATOM(atm', x, k x)
                end
          (* end case *))

    fun atomsToVars (env, atms, k) = let
          fun cvt ([], xs) = k (List.rev xs)
            | cvt (atm::atms, xs) = atomToVar (env, atm, fn x => cvt(atms, x::xs))
          in
            cvt (atms, [])
          end

    datatype cont_of_prim
      = LetBind of LVar.t * C.exp
      | TailExp of LVar.t -> C.exp

    fun cvtPrimApp (env, p, tys, args, k, kenv) = atomsToVars (env, args, fn args' => (
          case p
           of S.Pure rator => (case k
                 of LetBind(x, e) => C.mkPURE(rator, args', x, e)
                  | TailExp k => let
                      val ty = CUtil.typeOfPure(rator, tys)
                      val res = newRes (ty, Ex.STK)
                      in
                        C.mkPURE(rator, args', res, k res)
                      end
                (* end case *))
            | S.Arith rator => let
                fun mkARITH (rator, raiseExn) = (case k
                       of LetBind(x, e) => C.mkARITH(rator, args', x, e, C.mkTHROW (raiseExn, []))
                        | TailExp k => let
                            val res = newRes (CUtil.typeOfArith rator, Ex.STK)
                            in
                              C.mkARITH(rator, args', res, k res, C.mkTHROW (raiseExn, []))
                            end
                      (* end case *))
                fun withOverflow () = mkARITH(rator, raiseExn (kenv, CPSExn.exnOverflow))
                in
                  case rator
                   of P.Arith.IntOp(P.Arith.IDiv, 0) => raise Fail "IntInf division"
                    | P.Arith.IntOp(P.Arith.IDiv, sz) => let
                        val [_, divisor] = args'
                        val z = newAtm (CPSPrimTy.intTy, Ex.REG)
                        in
                        (* explicit test for divide by zero *)
                          C.mkATOM(zero, z,
                            C.mkIF(P.Test.ICmp(P.Test.IEq, sz), [divisor, z],
                              C.mkTHROW(raiseExn (kenv, CPSExn.exnDiv), []),
                              withOverflow()))
                        end
                    | P.Arith.Floor{from, to} => let
                      (* we need to test for NaN before doing the conversion *)
                        val [x] = args'
                        val raiseDomain = raiseExn (kenv, CPSExn.exnDomain)
                        in
                          C.mkIF(P.Test.FCmp(P.Test.FNEq, from), [x, x],
                            C.mkTHROW(raiseDomain, []),
                            withOverflow())
                        end
(* NOTE: for now, we include the bounds check in the primop, but eventually, this
* check should be exposed to allow for bounds-check elimination.
*)
                    | P.StrSub => let
                        val raiseSubscript = raiseExn (kenv, CPSExn.exnSubscript)
                        in
                          mkARITH(rator, raiseSubscript)
                        end
                    | _ => withOverflow()
                  (* end case *)
                end
            | S.Getter rator => (case k
                 of LetBind(x, e) => C.mkGET(rator, args', x, e)
                  | TailExp k => let
                      val ty = CUtil.typeOfGetter(rator, tys)
                      val res = newRes (ty, Ex.STK)
                      in
                        C.mkGET(rator, args', res, k res)
                      end
                (* end case *))
            | S.Setter rator => (case k
                 of LetBind(x, e) => C.mkSET(rator, args', x, e)
                  | TailExp k => let
                      val res = newRes (CUtil.typeOfSetter rator, Ex.STK)
                      in
                        C.mkSET(rator, args', res, k res)
                      end
                (* end case *))
          (* end case *)))

    fun mkThrow k x = C.mkTHROW(k, [x])

  (* helpers for making primitive nodes; these figure out the result type and
   * generate a new variable for the result.
   *)
    fun mkDCAPPLY (dc, tys, arg, k) = let
          val ty = CPSTypeUtil.applyScheme(CPSDataCon.typeOf dc, tys)
          val res = newRes (ty, Ex.STK)
          in
            C.mkDCAPPLY(dc, tys, arg, res, k res)
          end
    fun mkTUPLE (xs, k) = let
          val ty = CTy.TupleTy(List.map LVar.monoTypeOf xs)
          val res = newRes (ty, Ex.STK)
          in
            C.mkTUPLE(xs, res, k res)
          end
    fun mkSELECT (i, x, k) = let
          val (CTy.TupleTy tys) = LVar.monoTypeOf x
          val res = newRes (List.nth(tys, i-1), Ex.STK)
          in
            C.mkSELECT (i, x, res, k res)
          end

  (* does a function binding define a join point? *)
    fun isJoinBind [S.FB(f, _, _, _)] = Var.isJoin f
      | isJoinBind _ = false

  (* CPS convert an expression in tail position *)
    fun cvtTailExp (env, S.E(_, e), k : CVar.t, kenv : kenv) = (case e
           of S.E_Let(x, e1, e2) => let
                val (x', env') = bindVar (env, x)
                in
                  cvtExp (env, x', e1, cvtTailExp (env', e2, k, kenv), kenv)
                end
            | S.E_LetPoly(x, tvs, e1, e2) => let
                val (x', env') = bindVar (env, x)
                in
                (* NOTE: we use env' to process `e1` because it has the
                 * type-variable bindings for `x`'s type parameters.
                 *)
                  cvtExp (env', x', e1, cvtTailExp (env', e2, k, kenv), kenv)
                end
            | S.E_Fun(fbs, e) => if isJoinBind fbs
                then C.mkLETCONT(
                  cvtJoin (env, fbs, k, kenv),
                  cvtTailExp (env, e, k, kenv)) (* cvtJoin does not modify env! *)
                else let
                  val (fbs', env') = cvtFunBinds (env, fbs)
                  in
                    C.mkLETFUN(fbs', cvtTailExp (env', e, k, kenv))
                  end
            | S.E_Apply(f, tys, atm) => atomToVar (env, atm, fn arg' => (
                case getJoinCont f
                 of SOME k => C.mkTHROW(k, [arg'])
                  | NONE => C.mkAPPLY(
                      rename env f,
                      cvtTys(env, tys),
                      [arg'],
                      [k, getExh kenv])
                (* end case *)))
            | S.E_DConApp(dc, tys, atm) => atomToVar (env, atm, fn arg =>
                mkDCAPPLY(dconOf(env, dc), cvtTys(env, tys), arg, mkThrow k))
            | S.E_Prim(p, tys, atms) =>
                cvtPrimApp (env, p, cvtTys(env, tys), atms, TailExp(mkThrow k), kenv)
            | S.E_Tuple atms => atomsToVars (env, atms, fn args' => mkTUPLE(args', mkThrow k))
(* FIXME: what should we do about the type args *)
            | S.E_Select(i, x, tys) => mkSELECT(i, rename env x, mkThrow k)
            | S.E_If(tst, atms, e1, e2, ty) => atomsToVars (env, atms, fn args' =>
                C.mkIF(tst, args',
                  cvtTailExp (env, e1, k, kenv),
                  cvtTailExp (env, e2, k, kenv)))
            | S.E_Case(atm, rules, ty) => atomToVar (env, atm, fn arg' => let
                fun cvtRule (S.RULE(_, pat, exp)) = let
                      val (pat', env') = cvtPat (env, pat)
                      in
                        (pat', cvtTailExp (env', exp, k, kenv))
                      end
                in
                  C.mkSWITCH(arg', List.map cvtRule rules)
                end)
            | S.E_Handle(e, ex, hndlr, ty) => let
                val (ex', env') = bindVar (env, ex)
                val exhK' = newHndlK (CPSPrimTy.exhCTy, Ex.STK)
                in
                  C.mkLETCONT([C.mkCLambda (exhK', [ex'], cvtTailExp(env', hndlr, k, kenv))],
                    withKEnv (exhK', fn kenv' => cvtTailExp(env, e, k, kenv')))
                end
            | S.E_Raise(_, atm, _) =>
                atomToVar (env, atm, fn arg' => C.mkTHROW(getExh kenv, [arg']))
(* FIXME: we probably should add an ATOM expression form, since we are now
 * embedding the continuation for primitives in the term structure.
 *)
            | S.E_Atom atm =>
                atomToVar (env, atm, fn arg' => C.mkTHROW(k, [arg']))
          (* end case *))

  (* convert the rhs of the binding `let x = rhs in e`, where x' is the CPS
   * user variable for `x` and `e'` is the conversion of `e`.
   *)
    and cvtExp (env, x', rhs as S.E(_, rhsRep), e', kenv : kenv) = (case rhsRep
           of S.E_Let(y, e1, e2) => (* cannot happen because of denesting *)
                raise Fail "unexpected rhs Let"
            | S.E_LetPoly(x, tvs, e1, e2) => (* cannot happen because of denesting *)
                raise Fail "unexpected rhs LetPoly"
            | S.E_Fun(fbs, e) => let
              (* NOTE: this case should not happen if denesting is working correctly *)
                val (fbs', env') = cvtFunBinds (env, fbs)
                in
                  C.mkLETFUN(fbs', cvtExp (env', x', e, e', kenv))
                end
            | S.E_Apply(f, tys, atm) => atomToVar (env, atm, fn arg' => (
                case getJoinCont f
                 of SOME k => raise Fail(concat[
                        "unexpected call to join ", Var.toString f,
                        " in non-tail position"
                      ])
                  | NONE => let
                      val k' = newRetK (CTy.ContTy [LVar.monoTypeOf x'], Ex.STK)
                      val call = C.mkAPPLY(rename env f,
                            cvtTys(env, tys),
                            [arg'],
                            [k', getExh kenv])
                      in
                        C.mkLETCONT ([C.mkCLambda (k', [x'], e')], call)
                      end
                (* end case *)))
            | S.E_DConApp(dc, tys, atm) => atomToVar (env, atm, fn arg' =>
                C.mkDCAPPLY(dconOf(env, dc), cvtTys(env, tys), arg', x', e'))
            | S.E_Prim(p, tys, atms) =>
                cvtPrimApp (env, p, cvtTys(env, tys), atms, LetBind(x', e'), kenv)
            | S.E_Tuple atms => atomsToVars (env, atms, fn args' => C.mkTUPLE(args', x', e'))
(* FIXME: what should we do about the type args *)
            | S.E_Select(i, x, tys) => C.mkSELECT(i, rename env x, x', e')
            | S.E_Raise(_, atm, _) =>
                atomToVar (env, atm, fn arg' => C.mkTHROW(getExh kenv, [arg']))
            | S.E_Atom atm => C.mkATOM(cvtAtm(env, atm), x', e')
          (* the remaining forms use their continuation twice and we need to
           * avoid code duplication, so we introduce a join continuation here.
           *)
            | _ => let
                val k' = newJoin (CTy.ContTy[LVar.monoTypeOf x'], Ex.STK)
                in
                  C.mkLETCONT([C.mkCLambda (k', [x'], e')], cvtTailExp (env, rhs, k', kenv))
                end
          (* end case *))

    and cvtFunBinds (env, fbs) = let
          val env' = List.foldl
                (fn (S.FB(f, _, _, _), env) => #2 (bindVar (env, f)))
                  env fbs
          fun cvtFB (S.FB(f, _, x, e)) = let
                val f' = rename env' f
                val CTy.TyScheme(tvs, CTy.FunTy(_, [retContTy, exhContTy])) = LVar.typeOf f'
                val (x', env'') = bindVar (env', x)
              (* fresh continuation parameters *)
                val retK = newRetK (retContTy, Ex.STK)
                val exhK = newExhK (exhContTy, Ex.STK)
                in
                  C.mkLambda (f', [x'], [retK, exhK],
                    withKEnv (exhK, fn kenv => cvtTailExp (env'', e, retK, kenv)))
                end
          in
            (List.map cvtFB fbs, env')
          end

  (* convert a join-point binding *)
    and cvtJoin (env, [S.FB(f, _, x, e)], retK, kenv) = let
          val k = CVar.newTmp (
                Var.nameOf f,
                CTy.ContTy[cvtTy env (Var.monoTypeOf x)],
                Ex.STK)
          val (x', env') = bindVar (env, x)
          in
            ST.Counter.tick cntStkTmpCVar;
            setJoinCont (f, k);
            [C.mkCLambda (k, [x'], cvtTailExp (env', e, retK, kenv))]
          end
      | cvtJoin _ = raise Fail "impossible"

    fun transform (prog as S.CU fb) = let
          val _ = VarAnalysis.analyze prog
          val ([top], _) = cvtFunBinds (emptyEnv, [fb])
          in
            C.CU top
          end

  end
