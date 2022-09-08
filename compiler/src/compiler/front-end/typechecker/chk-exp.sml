(* chk-exp.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ChkExp : sig

    val check : Context.t * BindTree.exp -> AST.exp * Types.ty

    val checkValDecl : Context.t * BindTree.val_decl -> AST.val_decl * Context.t

  end = struct

    structure BT = BindTree
    structure E = Env
    structure U = Unify
    structure Ty = Types
    structure TU = TypeUtil
    structure C = Context

    fun debug () = Controls.get Ctl.debugTypeChk
    fun say s = Log.msg("[TY] " :: s)

  (* error reporting *)
    datatype token = datatype TypeError.token
    val warning = Context.warning
    val error = Context.error

    val chkTy = ChkType.check
    val chkPat = ChkPat.check
    val chkLit = ChkLit.check

  (* depth for top-level bindings *)
    val topDepth = 1

  (* strip top-level marks from an expression *)
    fun stripMark (BT.MarkExp{tree, ...}) = stripMark tree
      | stripMark e = e

  (* "smart" tuple type constructor *)
    fun mkTupleTy [ty] = ty
      | mkTupleTy tys = AST.TupleTy tys

  (* an expression/type pair for when there is an error *)
    val bogusExp = (AST.TupleExp[], Ty.ErrorTy)

  (* an atomic pattern for when there is an error *)
    val bogusAPat = AST.ConstPat(AST.LConst(Literal.Int 0, PrimTy.intTy))

    fun raiseExn (cxt, exn, ty) = AST.RaiseExp(C.getLocation cxt, exn, ty)

  (* case rule to raise the `Bind` exception *)
    fun raiseBindRule (cxt, argTy, resTy) =
          (AST.WildPat argTy, raiseExn(cxt, AST.ConstExp(AST.DConst(PrimExn.exnBind, [])), resTy))

  (* expression to raise the `Match` exception *)
    fun raiseMatch (cxt, resTy) =
          raiseExn(cxt, AST.ConstExp(AST.DConst(PrimExn.exnMatch, [])), resTy)

  (* case rule to raise the `Match` exception *)
    fun raiseMatchRule (cxt, argTy, resTy) = (AST.WildPat argTy, raiseMatch(cxt, resTy))

  (* case rule to re-raise an exception in a handler *)
    local
      val newEx = Var.newTmp "_ex"
    in
    fun reraise (cxt, ty) = let
          val ex = newEx PrimTy.exnTy
          in
            (AST.VarPat ex, raiseExn(cxt, AST.VarExp(ex, []), ty))
          end
    end (* local *)

  (* convert a variable or wildcard pattern to a variable *)
    local
      val newWild = Var.newTmp "_wild"
    in
    fun patToVar (AST.VarPat x) = x
      | patToVar (AST.WildPat ty) = newWild ty
      | patToVar _ = raise Fail "expected var/wild pattern"
    end (* local *)

  (* make a list cons expression *)
    fun consExp tyArgs (hdExp, tlExp, resTy) = AST.ApplyExp(
          AST.ConstExp(AST.DConst(PrimTy.listCons, tyArgs)),
          AST.TupleExp[hdExp, tlExp],
          resTy)
    fun nilExp tyArgs = AST.ConstExp(AST.DConst(PrimTy.listNil, tyArgs))

  (* common code for checking `val pat = e` bindings *)
    fun chkValBind (cxt, depth, tvs, pat, e) = let
          val _ = if debug()
                then say ["chkValBind: `let ", BindTreeUtil.patToString pat, " = ...`\n"]
                else ()
          val (e', rhsTy) = chkExp (cxt, depth, e)
          val (tvs', cxt') = ChkType.bindTyVars (cxt, tvs)
          val (pat', binds, lhsTy) = chkPat(cxt', NONE, pat)
          fun expansiveErr () = error (cxt, [
                  S "unable to generalize type variables because binding is expansive"
                ])
          fun nonexhaustiveWarn pat = warning(cxt, [
                  S "nonexhaustive binding\n",
                  S "  counter example: ", S(ASTUtil.patToString pat)
                ])
        (* unify the lhs and rhs types *)
          val _ = if not(U.unify(lhsTy, rhsTy))
                then error (cxt, [S "type mismatch in `val` binding"])
                else ();
          fun return (tyScm, isExh) = (pat', tyScm, e', rhsTy, isExh, binds)
          in
          (* check for exhaustiveness and close the LHS type when
           * the binding is not expansive.
           *)
            case (Pattern.checkBind (pat', lhsTy), ASTUtil.isValue e', tvs')
             of (NONE, true, _) => let
                (* get the closed type scheme for the whole lhs pattern.  Note that
                 * the bound type variables (tvs') are included in tvs.  Also, the
                 * generic meta variables in the type have been instantiated to
                 * bound type variables.
                 *)
                  val lhsScm as Ty.TyScheme(tvs, _) = TU.closeTy(tvs', depth, lhsTy)
                (* close the types of variables bound in a pattern *)
                  fun closePat (AST.VarPat x) =
                        Var.updateType (x, TU.bindFreeTVs (tvs, Var.monoTypeOf x))
                    | closePat (AST.ConPat(_, _, p)) = closePat p
                    | closePat (AST.TuplePat ps) = List.app closePat ps
                    | closePat _ = ()
                  in
                    if List.null tvs then () else closePat pat';
                    return (lhsScm, true)
                  end
              | (NONE, false, []) => (
                  TU.limitDepth(depth, lhsTy);
                  return (Ty.TyScheme([], lhsTy), true))
              | (NONE, false, _) => ( (* rhs must be value when there are type vars *)
                  expansiveErr ();
                  return (Ty.TyScheme([], lhsTy), true))
              | (SOME counterEx, _, []) => (
                  TU.limitDepth(depth, lhsTy);
                  nonexhaustiveWarn counterEx;
                  return (Ty.TyScheme([], lhsTy), false))
              | (SOME counterEx, _, _) => (
                  nonexhaustiveWarn counterEx;
                  expansiveErr ();
                  return (Ty.TyScheme([], lhsTy), false))
            (* end case *)
          end

  (* typecheck a group of function bindings *)
    and chkFunDcls (cxt, depth, tvs, fbs) = let
        (* deal with the bound type variables *)
          val (tvs', cxt') = ChkType.bindTyVars (cxt, tvs)
          val depth' = depth+1
        (* create variable bindings for the functions.  We also process the
         * parameter patterns and return type constraints in this pass so as
         * to get a more accurate initial type for the functions (in the case
         * that the user has supplied type constraints).
         *)
          fun bindFun cxt (BT.Funct{span, tree=(f, clauses)}, (fbs, fdefs)) = let
                val _ = if debug()
                      then say ["chkFun: `fun ", BT.VarId.nameOf f, " ...`\n"]
                      else ()
                val cxt = C.setSpan(cxt, span)
              (* get the result type annotation (if any) *)
                val resTy = let
                      fun chk ({span, tree=(_, NONE, _)}, optTy) = optTy
                        | chk ({span, tree=(_, SOME ty, _)}, optTy) = let
                            val cxt' = C.setSpan(cxt, span)
                            val ty' = chkTy (cxt', ty)
                            in
                              case optTy
                               of NONE => SOME ty'
                                | SOME ty'' => (
                                    if not(U.unify(ty', ty''))
                                      then error(cxt', [
                                          S "inconsistent return types for function ",
                                          ID(BT.VarId.nameOf f), S "\n",
                                          S "  expected: ", TY ty'', S "\n",
                                          S "  found:    ", TY ty'
                                        ])
                                      else ();
                                    optTy)
                              (* end case *)
                            end
                      in
                        case List.foldl chk NONE clauses
                         of NONE => AST.MetaTy(MetaVar.new(SOME depth'))
                          | SOME ty' => ty'
                        (* end case *)
                      end
                val arity = List.length (#1 (#tree (List.hd clauses)))
                fun chk {span, tree=(ps, _, e)} = let
                    (* check the patterns in the clause, returning the AST patterns,
                     * pattern types, and variable bindings.
                     *)
                      val (ps', paramTys, pbinds) = let
                            fun chkParam (p, (params, paramTys, pbinds)) = let
                                  val (p', binds, ty') = chkPat (cxt, SOME depth', p)
                                  in
                                    (p' :: params, ty' :: paramTys, binds @ pbinds)
                                  end
                            in
                              List.foldr chkParam ([], [], []) ps
                            end
                      in
                        (span, ps', paramTys, pbinds, e)
                      end
                val clauses' = List.map chk clauses
              (* check that pattern types agree *)
                val paramTys = (case clauses'
                       of (_, _, [paramTy], _, _)::rest => let
                            fun chkTys ((span, _, [ty], _, _)) =
                                  if not(U.unify(ty, paramTy))
                                        then error(C.setSpan(cxt, span), [
                                            S "inconsistent parameter types for function ",
                                            ID(BT.VarId.nameOf f), S "\n",
                                            S "  expected: ", TY paramTy, S "\n",
                                            S "  found:    ", TY ty
                                          ])
                                        else ()
                              | chkTys _ = raise Fail "impossible"
                            in
                              List.app chkTys rest;
                              [paramTy]
                            end
                        | (_, _, paramTys, _, _)::rest => let
                            fun chkTys (span, _, tys, _, _) = let
                                  fun chkTy (i, ty, paramTy) = if not(U.unify(ty, paramTy))
                                        then error(C.setSpan(cxt, span), [
                                            S "inconsistent parameter type in position ",
                                            S(Int.toString(i+1)), S " for function ",
                                            ID(BT.VarId.nameOf f), S "\n",
                                            S "  expected: ", TY paramTy, S "\n",
                                            S "  found:    ", TY ty
                                          ])
                                        else ()
                                  in
                                    ListPair.appiEq chkTy (tys, paramTys)
                                  end
                            in
                              List.app chkTys rest;
                              paramTys
                            end
                      (* end case *))
                val funTy = List.foldr AST.FunTy resTy paramTys
                val f' = Var.new(f, funTy)
                in
                  ((f, f') :: fbs, (f', paramTys, resTy, clauses') :: fdefs)
                end (* bindFun *)
          val (fbs', fdefs) = List.foldr (bindFun cxt') ([], []) fbs
        (* insert the function variables into a context for checking the function defs *)
          val cxt' = C.varsFromList (cxt', fbs')
        (* check the definitions *)
          fun chkFun (f', paramTys, resTy, clauses') = let
                val AST.TyScheme(_, funTy) = Var.typeOf f'
              (* type check the rhs of the function's clauses *)
                fun chkClause (span, params, paramTys, binds, rhs) = let
                      val cxt' = C.setSpan(cxt', span)
                    (* add the parameter variables to the context *)
                      val cxt'' = C.varsFromList (cxt', binds)
                    (* check the rhs expression *)
                      val (rhs', rhsTy) = chkExp (cxt'', depth', rhs)
                      in
                        if not(U.unify(resTy, rhsTy))
                          then error(cxt', [
                              S "return type mismatch in function ",
                              ID(Var.nameOf f'), S "\n",
                              S "  expected: ", TY resTy, S "\n",
                              S "  found:    ", TY rhsTy
                            ])
                          else ();
                        (params, rhs')
                      end
                val clauses'' = List.map chkClause clauses'
              (* check for non-exhaustive/redundant patterns *)
                val {useless, uncovered} = Pattern.checkMatch (
                      List.map (ASTUtil.tuplePat o #1) clauses'',
                      mkTupleTy paramTys)
              (* report redundant pattern errors, if any *)
                val _ = (case useless
                       of [] => ()
                        | indices => let
                            fun getLoc (span, _, _, _, _) = C.spanToLoc(cxt, span)
                          (* project out the context information for the redundant patterns *)
                            fun proj (_, [], _) = []
                              | proj (n, ix::ixs, cl::cls) = if (ix = n)
                                  then getLoc cl :: proj(n+1, ixs, cls)
                                  else proj(n+1, ix::ixs, cls)
                            in
                              case proj (0, indices, clauses')
                               of [loc] => error(cxt, [
                                      S "redundant pattern at ", LN loc,
                                      S " in function ", ID(Var.nameOf f')
                                    ])
                                | locs => error(cxt, [
                                      S "redundant patterns at ", LNS locs,
                                      S " in function ", ID(Var.nameOf f')
                                    ])
                              (* end case *)
                            end
                      (* end case *))
                val clauses'' = (case uncovered
                       of NONE => clauses''
                        | SOME p => (
                            warning(cxt, [
                                S "nonexhaustive match in ",
                                ID(Var.nameOf f'), S "\n",
                                S "  counter example: ",
(* TODO: if the function is curried, then the counter example will be
 * a tuple pattern that should be split into multiple patterns.
 *)
                                S(ASTUtil.patToString p)
                              ]);
                          (* add a clause to raise Match *)
                            clauses'' @ [
                                (List.map AST.WildPat paramTys, raiseMatch(cxt, resTy))
                              ])
                      (* end case *))
              (* normalize the parameters to variables *)
                val (params', body') = let
                      fun normalize () = let
                            val xs = List.map (Var.newTmp "_param") paramTys
                            val caseArgs = List.map (fn x => AST.VarExp(x, [])) xs
                            fun doClause (pats, exp) = (ASTUtil.tuplePat pats, exp)
                            val body = AST.CaseExp (
                                  ASTUtil.tupleExp caseArgs,
                                  List.map
                                    (fn (pats, exp) => (ASTUtil.tuplePat pats, exp))
                                      clauses'',
                                  resTy)
                            in
                              (xs, body)
                            end
                      in
                        case clauses''
                         of [(pats, body)] => if List.all ASTUtil.isVarPat pats
                              then (List.map patToVar pats, body)
                              else normalize()
                          | _ => normalize()
                        (* end case *)
                      end
                in
                  (f', params', body')
                end
          val fbs' = List.map chkFun fdefs
        (* close over the types of the functions *)
          val _ = let
                val tys = List.map (Var.monoTypeOf o #1) fdefs
                val tyScms = TypeUtil.closeTys(tvs', depth, tys)
                in
                  ListPair.app
                    (fn (fdef, tyScm) => Var.updateType(#1 fdef, tyScm))
                      (fdefs, tyScms)
                end
          in
            if debug()
              then let
                fun pr (f', _, _) = say[
                        "chkFun: ", Var.nameOf f', " : ",
                        TU.fmtScheme {long=true} (Var.typeOf f'), "\n"
                      ]
                in
                  List.app pr fbs'
                end
              else ();
            (AST.FunDecl fbs', cxt')
          end

  (* typecheck value declarations *)
    and chkValDcl (cxt, depth, decl, next) = (case decl
           of BT.MarkVDecl{span, tree} => chkValDcl (C.setSpan(cxt, span), depth, tree, next)
            | BT.ValVDecl(tvs, pat, e) => let
                val (pat', lhsScm, e', rhsTy, isExhaustive, binds) =
                      chkValBind (cxt, depth, tvs, pat, e)
                val cxt' = C.varsFromList (cxt, binds)
              (* check the scope of the binding *)
                val (e'', resTy) = next cxt'
                in
                  if isExhaustive
                    then (AST.LetExp(AST.ValDecl(pat', lhsScm, e'), e''), resTy)
                    else let
                      val Ty.TyScheme([], lhsTy) = lhsScm
                      val act = raiseBindRule(cxt, lhsTy, resTy)
                      in
                        (AST.CaseExp(e', [(pat', e''), act], resTy), resTy)
                      end
                end
            | BT.FunVDecl(tvs, fbs) => let
                val (fdecl, cxt') = chkFunDcls (cxt, depth, tvs, fbs)
                val (e', resTy) = next cxt'
                in
                  (AST.LetExp(fdecl, e'), resTy)
                end
          (* end case *))

  (* typecheck expressions as described in Section 6.8 *)
    and chkExp (cxt, depth, exp : BindTree.exp) = (case exp
           of BT.MarkExp{span, tree} => chkExp (C.setSpan(cxt, span), depth, tree)
            | BT.LetExp(valDcls, exp) => let
                fun chkDcls ([], cxt) = chkExp (cxt, depth, exp)
                  | chkDcls (vd::vds, cxt) =
                      chkValDcl (cxt, depth, vd, fn cxt' => chkDcls(vds, cxt'))
                in
                  chkDcls (valDcls, cxt)
                end
            | BT.IfExp(e1, e2, e3) => let
                val (e1', ty1) = chkExp (cxt, depth, e1)
                val (e2', ty2) = chkExp (cxt, depth, e2)
                val (e3', ty3) = chkExp (cxt, depth, e3)
                in
                  if not(U.unify(ty1, PrimTy.boolTy))
                    then error(cxt, [S "type of conditional not bool"])
                    else ();
                  if not(U.unify(ty2, ty3))
                    then (
                      error(cxt, [S "types of then and else clauses must match"]);
                      bogusExp)
                    else (AST.IfExp(e1', e2', e3', ty2), ty2)
                end
            | BT.FnExp cases => let
                val argTy = AST.MetaTy(MetaVar.new NONE)
                val resTy = AST.MetaTy(MetaVar.new NONE)
                val cases' =
                      chkMatchCase ("'fn'", cxt, depth+1, argTy, resTy, cases, false)
                val funTy = AST.FunTy(argTy, resTy)
                val (x, body') = (case cases'
                       of [(AST.VarPat x, e)] => (x, e)
                        | _ => let
                            val x = Var.newTmp "_fn_param" argTy
                            val e = AST.CaseExp(AST.VarExp(x, []), cases', resTy)
                            in
                              (x, e)
                            end
                      (* end case *))
                in
                  (AST.FunExp(x, body', resTy), funTy)
                end
            | BT.CaseExp(e, cases) => let
                val (e', argTy) = chkExp (cxt, depth, e)
                val resTy = AST.MetaTy(MetaVar.new NONE)
                val cases' =
                      chkMatchCase ("'case'", cxt, depth, argTy, resTy, cases, false)
                in
                  (AST.CaseExp(e', cases', resTy), resTy)
                end
            | BT.HandleExp(e, cases) => let
                val (e', resTy) = chkExp (cxt, depth, e)
                val cases' = chkMatchCase (
                      "'handle'", cxt, depth, PrimTy.exnTy, resTy, cases, true)
                val exp' = AST.HandleExp(e', cases', resTy)
                in
                  (exp', resTy)
                end
            | BT.RaiseExp e => let
                val (e', ty) = chkExp (cxt, depth, e)
                val resTy = AST.MetaTy(MetaVar.new NONE)
                in
                  if not(U.unify(ty, PrimTy.exnTy))
                    then error(cxt, [S "expected 'exn' type for argument of 'raise'"])
                    else ();
                  (raiseExn(cxt, e', resTy), resTy)
                end
            | BT.AndAlsoExp(e1, e2) => let
                val (e1', ty1) = chkExp (cxt, depth, e1)
                val (e2', ty2) = chkExp (cxt, depth, e2)
                val exp = AST.IfExp(
                      e1',
                      e2',
                      AST.ConstExp(AST.DConst(PrimTy.boolFalse, [])),
                      PrimTy.boolTy)
                in
                  if not(U.unify(ty1, PrimTy.boolTy) andalso U.unify(ty2, PrimTy.boolTy))
                    then error(cxt, [S "arguments of andalso must have type bool"])
                    else ();
                  (exp, PrimTy.boolTy)
                end
            | BT.OrElseExp(e1, e2) => let
                val (e1', ty1) = chkExp (cxt, depth, e1)
                val (e2', ty2) = chkExp (cxt, depth, e2)
                val exp = AST.IfExp(
                      e1',
                      AST.ConstExp(AST.DConst(PrimTy.boolTrue, [])),
                      e2',
                      PrimTy.boolTy)
                in
                  if not(U.unify(ty1, PrimTy.boolTy) andalso U.unify(ty2, PrimTy.boolTy))
                    then error(cxt, [S "arguments of orelse must have type bool"])
                    else ();
                  (exp, PrimTy.boolTy)
                end
            | BT.ApplyExp(e1, e2) => let
              (* because non-nullary data constructor expressions are turned into
               * lambdas, we check for that case here to reduce the need for later
               * inlining.
               *)
                val (e1', ty1) = (case stripMark e1
                       of BT.ConExp dc => let
                            val (dc', tyArgs, ty) = chkDataCon (cxt, dc)
                            in
                              (AST.ConstExp(AST.DConst(dc', tyArgs)), ty)
                            end
                        | _ => chkExp (cxt, depth, e1)
                      (* end case *))
                val (e2', ty2) = chkExp (cxt, depth, e2)
                val resTy = AST.MetaTy(MetaVar.new NONE)
                in
                  if not(U.unify(ty1, AST.FunTy(ty2, resTy)))
                    then error(cxt, [
                        S "type mismatch in application\n",
                        S "    function type: ", TY ty1, S "\n",
                        S "    argument type: ", TY ty2
                      ])
                    else ();
                  (AST.ApplyExp(e1', e2', resTy), resTy)
                end
            | BT.TupleExp[] => (AST.TupleExp[], PrimTy.unitTy)
            | BT.TupleExp es => let
                fun chk (e, (es, tys)) = let
                      val (e', ty) = chkExp(cxt, depth, e)
                      in
                        (e'::es, ty::tys)
                      end
                val (es', tys) = List.foldr chk ([], []) es
                in
                  (ASTUtil.tupleExp es', mkTupleTy tys)
                end
            | BT.ListExp[] => let
                val (ty, tyArgs) = TU.instantiate (DataCon.typeOf PrimTy.listNil)
                in
                  (nilExp tyArgs, ty)
                end
            | BT.ListExp es => let
                val (Ty.FunTy(Ty.TupleTy[elemTy, _], resTy), tyArgs) =
                      TU.instantiate (DataCon.typeOf PrimTy.listCons)
                fun chkElems [] = nilExp tyArgs
                  | chkElems (e::er) = let
                      val (e', ty) = chkExp (cxt, depth, e)
                      val _ = if not(Unify.unify(elemTy, ty))
                            then error(C.setSpanFromExp(cxt, e), [
                                S "element type mismatch in list expression;\n",
                                S "  expected: ", TY elemTy, S "\n",
                                S "  found:    ", TY ty
                              ])
                            else ()
                      val er' = chkElems er
                      in
                        consExp tyArgs (e', er', resTy)
                      end
                val listExp = chkElems es
                in
                  (listExp, resTy)
                end
            | BT.SeqExp es => let
                fun chk [e] = chkExp(cxt, depth, e)
                  | chk (e::r) = let
                      val (e', _) = chkExp (cxt, depth, e)
                      val (e'', ty) = chk r
                      in
                        (AST.SeqExp(e', e''), ty)
                      end
                in
                  chk es
                end
            | BT.ConExp dc => let
                val (dc', tyArgs, ty) = chkDataCon (cxt, dc)
                in
                  case TU.prune ty
                   of ty as Ty.FunTy(dom, rng) => let (* wrap with lambda *)
                        val x = Var.newTmp "_arg" dom
                        val body = AST.ApplyExp(
                              AST.ConstExp(AST.DConst(dc', tyArgs)),
                              AST.VarExp(x, []),
                              rng)
                        in
                          (AST.FunExp(x, body, rng), ty)
                        end
                    | ty => (AST.ConstExp(AST.DConst(dc', tyArgs)), ty)
                  (* end case *)
                end
            | BT.VarExp qid => let
                fun chk (SOME(E.Var x')) =  let
                      val (ty, tyArgs) = TU.instantiate (Var.typeOf x')
                      in
                        (AST.VarExp(x', tyArgs), ty)
                      end
                  | chk (SOME(E.Overload(tyScheme, candidates))) = let
                    (* instantiate the type scheme *)
                      val (ty, _) = TU.instantiate tyScheme
                      val ovldInst = ref(AST.Unknown(ty, candidates))
                      in
                        C.addOverloadVar (cxt, ovldInst);
                        (AST.OverloadExp ovldInst, ty)
                      end
                  | chk NONE = raise Fail("impossible " ^ BindTreeUtil.qidToString BindTree.VarId.toString qid)
                in
                  case ChkQualId.check(cxt, qid)
                   of SOME(SOME strEnv, id) => chk (E.findVar'(strEnv, id))
                    | SOME(NONE, id) => chk (C.findVar(cxt, id))
                    | NONE => raise Fail "impossible"
                  (* end case *)
                end
            | BT.ConstExp const => let
                val (const', ty) = chkLit (cxt, const)
                in
                  (AST.ConstExp(AST.LConst(const', ty)), ty)
                end
            | BT.ConstraintExp(e, ty) => let
                val constraintTy = ChkType.check (cxt, ty)
                val (e', ty') = chkExp (cxt, depth, e)
                in
                   if not(U.unify(ty', constraintTy))
                     then error(cxt, [S "type mismatch in constraint expression"])
                     else ();
                  (e', ty')
                end
            | BT.ErrorExp => bogusExp
          (* end case *))

    and chkDataCon (cxt, dc) = let
          fun chk (SOME dc') = let
                val (ty, tyArgs) = TU.instantiate (DataCon.typeOf dc')
                in
                  (dc', tyArgs, ty)
                end
            | chk NONE = raise Fail "impossible"
          in
            case ChkQualId.check(cxt, dc)
             of SOME(SOME strEnv, id) => chk (E.findDCon'(strEnv, id))
              | SOME(NONE, id) => chk (C.findDCon(cxt, id))
              | NONE => raise Fail "impossible"
            (* end case *)
          end

    and chkMatchCase (kind, cxt, depth, argTy, resTy, cases, isHandle) = let
          fun chkMatch (cxt, mcase) = (case mcase
                 of BT.MarkMatch{span, tree} => chkMatch(C.setSpan(cxt, span), tree)
                  | BT.CaseMatch(pat, exp) => let
                      val _ = if debug()
                            then say[
                                "chkMatch: `", BindTreeUtil.patToString pat, " => ...`\n"
                              ]
                            else ()
                      val (pat', binds, argTy') = chkPat(cxt, SOME depth, pat)
                      val cxt' = C.varsFromList (cxt, binds)
                      val (exp', resTy') = chkExp(cxt', depth, exp)
                      in
                        if not(U.unify(argTy, argTy'))
                          then error(cxt, [
                              S "type mismatch in ", S kind, S "\n",
                              S "  argument type: ", TY argTy, S "\n",
                              S "  pattern type:  ", TY argTy
                            ])
                          else ();
                        if not(U.unify(resTy, resTy'))
                          then error(cxt, [S "type mismatch in ", S kind])
                          else ();
                        (pat', exp')
                      end
                (* end case *))
          val cases' = List.map (fn m => chkMatch(cxt, m)) cases
          val {useless, uncovered} = Pattern.checkMatch (List.map #1 cases', argTy)
          fun nonexhaustiveWarn pat = warning(cxt, [
                  S "nonexhaustive match in ", S kind, S ";\n",
                  S "  counter example: ", S(ASTUtil.patToString pat)
                ])
          in
          (* report redundant pattern errors *)
            case useless
             of [] => ()
              | indices => let
                  fun getLoc (BT.MarkMatch{span, ...}) = C.spanToLoc(cxt, span)
                    | getLoc _ = raise Fail "missing span info"
                (* project out the context information for the redundant patterns *)
                  fun proj (_, [], _) = []
                    | proj (n, ix::ixs, mc::mcs) = if (ix = n)
                        then getLoc mc :: proj(n+1, ixs, mcs)
                        else proj(n+1, ix::ixs, mcs)
                  in
                    case proj (0, indices, cases)
                     of [loc] => error(cxt, [
                            S "redundant pattern at ", LN loc, S " in ", S kind
                          ])
                      | locs => error(cxt, [
                            S "redundant patterns at ", LNS locs, S " in ", S kind
                          ])
                    (* end case *)
                  end
            (* end case *);
          (* handle nonexhastive matches *)
            case (uncovered, isHandle)
             of (NONE, _) => cases'
              | (SOME pat, false) => (
                  nonexhaustiveWarn pat;
                  cases' @ [raiseMatchRule(cxt, argTy, resTy)])
              | (SOME pat, true) => cases' @ [reraise(cxt, resTy)]
            (* end case *)
          end

  (* exported functions *)

    fun check (cxt, exp) = chkExp (cxt, topDepth, exp)

    fun checkValDecl (cxt, decl) = (case decl
           of BT.MarkVDecl m => checkValDecl (C.withMark(cxt, m))
            | BT.ValVDecl(tvs, pat, e) => let
                val (pat', lhsScm, e', rhsTy, isExhaustive, binds) =
                      chkValBind (cxt, topDepth, tvs, pat, e)
                val cxt' = C.varsFromList (cxt, binds)
                in
                  if isExhaustive
                    then (AST.ValDecl(pat', lhsScm, e'), cxt')
                    else let
                      (* the pattern is refutable, so we convert `val p = e` into
                       * `val xs = case e of p => xs | _ => raise Bind`, where `xs` is
                       * the tuple of variables bound in `p`.
                       *)
                        val Ty.TyScheme([], lhsTy) = lhsScm
                        val lhs = ASTUtil.tuplePat(List.map (AST.VarPat o #2) binds)
                        val exp = ASTUtil.tupleExp(List.map (fn (_, x) => AST.VarExp(x, [])) binds)
                        val rhs = AST.CaseExp(
                              e',
                              [(pat', exp), raiseBindRule(cxt, lhsTy, rhsTy)],
                              rhsTy)
                        in
                          (AST.ValDecl(lhs, lhsScm, rhs), cxt')
                        end
                end
            | BT.FunVDecl(tvs, fbs) => chkFunDcls (cxt, topDepth, tvs, fbs)
          (* end case *))

  end
