(* uncurry.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The "uncurry" transformation from "Compiling with Continuations".
 * Given a function definition:
 *
 *      fun f <tvs> x = let
 *            fun g y = e
 *            in
 *              g
 *            end
 *
 * We transform it to
 *
 *      fun f' <tvs> (x, y, g) = e
 *      and f <tvs> x' = let
 *              fun g' y' = f' <tvs1> (x', y', g')
 *              in
 *                g'
 *              end
 *
 * Then, subsequent inlining of `f`/`g'` specialize curried applications to
 * uncurried ones.  We pass `g'` to `f'` to cover the case where g is referenced
 * in the expression `e`.
 *
 * Note that we assume that type contraction has been run prior to uncurrying,
 * which will ensure that `g` is monomorphic (for curried definitions in the
 * original source, this property already holds).
 *)

structure Uncurry : sig

    val transform : Census.t * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure STy = SimpleTypes
    structure SV = SimpleVar
    structure STyU = SimpleTypeUtil
    structure ST = Stats

  (* debug messages *)
    fun say msg = Log.msg("[S-UNC] " :: msg)
    fun ctlSay msg = if Controls.get Ctl.debugSimpleOpt
          then say msg
          else ()
    val v2s = SV.toString
    fun tvs2s tvs = concat["<", String.concatWithMap "," TyVar.toString tvs, ">"]
    fun tys2s tys = concat["<", String.concatWithMap "," STyU.toString tys, ">"]

  (* counters for optimizations *)
    val cntrs = ST.Group.newWithPri SimpleOptStats.group ("uncurry", [4])
    local
      val newCntr = ST.Counter.new cntrs
    in
    val cntUncurry      = newCntr "uncurry"
    end (* local *)

  (* `uncurry info (f, x, outerFns, body)` returns a pair of functions,
   * where the first is the uncurried version of `f` and the second is
   * the curried version.  For a curried definition of the form
   *
   *    fun f x = let
   *        fun g y = let
   *            fun h z = e
   *            in h<tys2> end
   *        in g<tys1> end
   *
   * the call will be
   *
   *    uncurry info (f, x, [(g, y), (h, x)], e)
   *)
    fun uncurry info (f, x, outerFns, body) = let
          val setUseCnt = Census.setUse info
          val useCntOf = Census.useCntOf info
          val useVar = Census.use info
          val decUseCnt = Census.decUse info
          val applyFn = Census.apply info
          fun var x = S.A_Var(useVar x, [])
        (* `f` should have the type <tvs> argTy1 -> argTy2 -> ... -> resTy *)
          val (tvs, argTys, resTy) = let
                val STy.TyScheme(tvs, STy.FunTy(ty1, _)) = SV.typeOf f
                fun getArgTys ([(g, y)], argTys) = let
                      val STy.FunTy(ty1, ty2) = SV.monoTypeOf g
                      val argTys = if useCntOf g > 1
                            then SV.monoTypeOf g :: ty1 :: argTys
                            else ty1 :: argTys
                      in
                        (tvs, List.rev argTys, ty2)
                      end
                  | getArgTys ((g, y)::outers, argTys) = if useCntOf g > 1
                      then getArgTys (outers, SV.monoTypeOf g :: SV.monoTypeOf y :: argTys)
                      else getArgTys (outers, SV.monoTypeOf y :: argTys)
                in
                  getArgTys (outerFns, [ty1])
                end
          val argTplTy = STy.TupleTy argTys
          val uncurriedTyScm = STy.TyScheme(tvs, STy.FunTy(argTplTy, resTy))
          val f' = SV.newPoly(SV.nameOf f, uncurriedTyScm)
        (* construct the uncurried version of `f` *)
          val uncurriedFB = let
                fun getParams ((g, y), params) = if useCntOf g > 1
                      then y :: g :: params
                      else y :: params
                val params = x :: List.foldr getParams [] outerFns
              (* the tuple parameter *)
                val tplParam = SV.new("_param", argTplTy)
              (* extract the parameters from the tuple *)
                val body' = let
                      fun get (i, x, e) =
                            S.mkLet(x, S.mkSelect(i+1, useVar tplParam, []), e)
                      in
                        List.foldri get body params
                      end
                in
                  S.mkFB(f', tplParam, body')
                end
        (* reconstruct the curried function *)
          val curriedFB = let
                fun mk ([], args) = let
                      val tyArgs = List.map STy.VarTy tvs
                      val arg = SV.new("_argTpl", argTplTy)
                      in
                        S.mkLet(arg, S.mkTuple(List.rev args),
                          S.mkApply(applyFn f', tyArgs, var arg))
                      end
                  | mk ((g, y)::outer, args) = let
                      val y' = SV.copy y
                      val args = var y' :: args
                      val (g, args) = if useCntOf g > 1
                            then let
                              val g' = SV.copy g
                              in
                              (* we replace the use of g with g' in the body of the let *)
                                decUseCnt g;  setUseCnt(g', 1);
                                (g', var g' :: args)
                              end
                            else (g, args)
                      val e' = mk (outer, args)
                      in
                        S.mkFun([S.mkFB(g, y', e')], S.mkAtom(S.A_Var(g, [])))
                      end
                val x' = SV.copy x
                in
                (* we rely on inlining to complete the uncurrying tranformation *)
                  SV.markAlwaysInline f;
                  S.mkFB(f, x', mk (outerFns, [var x']))
                end
          in
            ST.Counter.tick cntUncurry;
            [uncurriedFB, curriedFB]
          end

    fun transform (info, S.CU mainFB) = let
          val uncurry = uncurry info
          fun xform (exp as S.E(lab, e)) = (case e
                 of S.E_Let(x, e1, e2) =>
                      S.E(lab, S.E_Let(x, xform e1, xform e2))
                  | S.E_LetPoly(x, tvs, e1, e2) =>
                      S.E(lab, S.E_LetPoly(x, tvs, xform e1, xform e2))
                  | S.E_Fun(fbs, e) =>
                      S.E(lab, S.E_Fun(List.foldr xformFB [] fbs, xform e))
                  | S.E_Apply(f, tys, arg) => exp
                  | S.E_DConApp _ => exp
                  | S.E_Prim _ => exp
                  | S.E_Tuple _ => exp
                  | S.E_Select _ => exp
                  | S.E_If(tst, args, e1, e2, ty) =>
                      S.E(lab, S.E_If(tst, args, xform e1, xform e2, ty))
                  | S.E_Case(arg, rules, ty) => let
                      fun xformRule (S.RULE(lab, p, e)) = S.RULE(lab, p, xform e)
                      in
                        S.E(lab, S.E_Case(arg, List.map xformRule rules, ty))
                      end
                  | S.E_Handle(body, ex, hndlr, ty) =>
                      S.E(lab, S.E_Handle(xform body, ex, xform hndlr, ty))
                  | S.E_Raise _ => exp
                  | S.E_Atom _ => exp
                (* end case *))
        (* transform a function binding by collecting curried arguments and then
         * rewriting.
         *)
          and xformFB (S.FB(f, lab, x, e), fbs) = let
                fun collect (exp as S.E(_, e), outerFns) = (case e
                       of S.E_Fun([S.FB(g, _, y, gBody)], S.E(_, S.E_Atom(S.A_Var(g', [])))) =>
                            if SV.same(g, g')
                              then collect (gBody, (g, y)::outerFns)
                              else rewrite (exp, outerFns)
                        | _ => rewrite (exp, outerFns)
                      (* end case *))
                and rewrite (e, []) = S.FB(f, lab, x, xform e) :: fbs
                  | rewrite (e, outerFns) =
                      uncurry(f, x, rev outerFns, xform e) @ fbs
                in
                  collect (e, [])
                end
          val S.FB(main, mainLab, mainParam, mainBody) = mainFB
          in
            S.CU(S.FB(main, mainLab, mainParam, xform mainBody))
          end

  end
