(* contract.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Contraction (aka "Shrinking") for the Simple AST IR.  The optimizations are:
 *
 *    - eliminate unused functions
 *    - eliminate unused bindings when the lhs is pure
 *    - contract cases expressions on known values
 *    - contract selections from known tuples
 *    - beta-reduce functions that are applied once
 *    - float nested lets
 *)

structure Contract : sig

    val transform : Census.t * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure TVMap = TyVar.Map
    structure TVSet = TyVar.Set
    structure Var = SimpleVar
    structure VMap = SimpleVar.Map
    structure DataCon = SimpleDataCon
    structure C = Census
    structure TyU = SimpleTypeUtil
    structure Util = SimpleASTUtil
    structure ST = Stats

  (* debug messages *)
    fun say msg = Log.msg("[S-OPT] " :: msg)
    fun ctlSay msg = if Controls.get Ctl.debugSimpleOpt
          then say msg
          else ()
    val v2s = Var.toString
    fun tvs2s tvs = concat["<", String.concatWithMap "," TyVar.toString tvs, ">"]
    fun tys2s tys = concat["<", String.concatWithMap "," TyU.toString tys, ">"]

  (* counters for optimizations *)
    local
      val cntrs = ST.Group.newWithPri SimpleOptStats.group ("contract", [2])
      val newCntr = ST.Counter.new cntrs
    in
    val cntRound        = newCntr "rounds"
    val cntDeadFun      = newCntr "dead-fun"
    val cntDeadVar      = newCntr "dead-var"
    val cntRename       = newCntr "rename-var"
    val cntCase         = newCntr "case-elim"
    val cntTuple        = newCntr "tuple-elim"
    val cntBeta         = newCntr "inline"
    end (* local *)

    val unitTy = Ty.ConTy([], SimplePrim.unitTyc)

  (* known values that a variable can be bound to.  For CONS/TPL/ATOM values,
   * we include type variables for when the value is the rhs of a polymorphic
   * binding.
   *)
    datatype value
    (* call-once function availble for inlining *)
      = FUN of S.lambda
    (* data-constructor application on rhs of let binding *)
      | CONS of TyVar.t list * S.dcon * S.atom
    (* tuple construction on rhs of let binding *)
      | TPL of TyVar.t list * S.atom list
    (* atom on rhs of let binding *)
      | ATOM of TyVar.t list * S.atom
    (* variable bound to something else *)
      | UNKNOWN

  (* for debugging *)
    fun valToString v = let
          fun prefix [] l = concat l
            | prefix tvs l = concat(tvs2s tvs :: l)
          in
            case v
             of FUN(S.FB(f, _, x, _)) => concat["FUN(", v2s f, ", ", v2s x, ", -)"]
              | CONS(tvs, dc, atm) => prefix tvs
                  ["CONS(", DataCon.nameOf dc, ", ", Util.atomToString atm, ")"]
              | TPL(tvs, atms) => prefix tvs
                  ["TPL[", String.concatWithMap ", " Util.atomToString atms, "]"]
              | ATOM(tvs, atm) => prefix tvs ["ATOM(", Util.atomToString atm, ")"]
              | UNKNOWN => "UNKNOWN"
            (* end case *)
          end

  (* property to track if a function was inlined *)
    local
      val {getFn, setFn} = Var.newFlag ()
    in
    fun markInlined f = setFn(f, true)
    val wasInlined = getFn
    end (* local *)


  (* the environment tracks four kinds of mappings:
   *
   *   1) function type parameters to types; these mappings are created by
   *      beta reduction of a polymorphic function application.
   *
   *   2) function parameters to argument atoms; these mappings are created
   *      by beta reduction of a function application.  Census bookkeeping
   *      for these is prior to inlining.
   *
   *   3) local variables to type-specialized versions; these mappings are
   *      introduced when the type of a local variable changes because of
   *      mapping #1 being applied to its type.  Note that polymorphic
   *      variables will perserve their arity.  The census count for the
   *      original variable is shared with the fresh variable.
   *
   *   4) variables bound to RHS values.  These bindings are used to drive
   *      contraction.
   *
   * Because the domain of the second and third maps is disjoint, we use
   * a single substitution and a union type to represent it.  Note also
   * that the domain of the fourth mapping is disjoint with #2 and #3,
   * because binding to rhs values is handled *after* freshening locals.
   *
   * Bindings of the form `let x = atm` and `letpoly x = atm` are handled
   * like beta reduction, which means that the `x := atm` mapping is inserted
   * into mapping #2, census counts are updated immediately, and the binding
   * is removed.  In this case, we do *not* have to freshen `x`, since it
   * be replaced by `atm`.
   *)
    datatype env = E of {
        tvSubst : Ty.ty TVMap.map,      (* actual/formal type parameter substitution *)
        vSubst : var VMap.map,          (* substitution for variables *)
        bMap : value VMap.map           (* track rhs of let-bound variables *)
      }

    and var
      = Arg of S.atom                   (* for parameter -> argument mapping *)
      | Var of SimpleVar.t              (* for local variable -> fresh variable mapping *)

    val emptyEnv = E{
            tvSubst = TVMap.empty,
            vSubst = VMap.empty,
            bMap = VMap.empty
          }

  (* extend a type-variable to type substitution with additional bindings *)
    fun extendTVSubst (tvSubst, tvs, tys) =
          ListPair.foldlEq
            (fn (tv, ty, subst) => TVMap.insert(subst, tv, ty))
              tvSubst
                (tvs, tys)

    fun renameTy (E{tvSubst, ...}, ty) = TyU.applySubst tvSubst ty
    fun renameTys (E{tvSubst, ...}, tys) = List.map (TyU.applySubst tvSubst) tys

  (* Given a polymoprhic variable `x` with type parameters `tvs` that
   * are instantiated to `tys`, apply the substitution { tvs := tys } to the
   * types tys'.
   *)
    fun specializeTysForVar (x, [], tys') = tys'
      | specializeTysForVar (x, tys, tys') = let
          val Ty.TyScheme(tvs, _) = Var.typeOf x
          val tvSubst = extendTVSubst (TVMap.empty, tvs, tys)
          in
            List.map (TyU.applySubst tvSubst) tys'
          end

  (* insert a variable to atom binding in the environment *)
    fun insertVar (E{tvSubst, vSubst, bMap}, x, atm) =
          E{tvSubst = tvSubst, vSubst = VMap.insert (vSubst, x, Arg atm), bMap = bMap}

  (* lookup a variable in the environment *)
    fun lookupVar (E{vSubst, ...}, x) = (case VMap.find(vSubst, x)
           of SOME(Var x') => x'
            | SOME(Arg(S.A_Var(x', _))) => x'
            | _ => x
          (* end case *))

  (* rename a variable use `x<tys>` where a variable is required; we assume that
   * the type arguments have already been renamed.
   *)
    fun rename (E{vSubst, ...}, x, tys) = (case VMap.find(vSubst, x)
           of SOME(Var x') => (x', tys)
            | SOME(Arg(S.A_Var(x', tys'))) => let
              (* Here `x` may be a polymorphic variable, which means that this
               * we have `letpoly x = <tvs> x'<tys'> in ... x<tys> ...`, so
               * we need to apply the substitution { tvs := tys } to the
               * types tys'.
               *)
                val tys'' = specializeTysForVar (x, tys, tys')
                in
                  (x', tys'')
                end
            | NONE => (x, tys)
            | SOME(Arg atm) => raise Fail(concat[
                  "rename: ", v2s x, "<> ==> ", Util.atomToString atm
                ])
          (* end case *))

  (* rename an occurrence of an atom *)
    fun renameAtom info (env as E{vSubst, ...}, atm) = (case atm
           of S.A_Var(x, tys) => (case VMap.find(vSubst, x)
                 of SOME(Var x') => S.A_Var(x', renameTys (env, tys))
                  | SOME(Arg(S.A_Var(x', tys'))) => (case tys
                       of [] => S.A_Var(x', tys')
                        | _ => let
                         (* Here `x` is a polymorphic variable, which means that this
                          * we have `letpoly x = <tvs> x'<tys'> in ... x<tys> ...`, so
                          * we need to apply the substitution { tvs := tys } to the
                          * types tys'.
                          *)
                           val Ty.TyScheme(tvs, _) = Var.typeOf x
                           val tvSubst = extendTVSubst (TVMap.empty, tvs, tys)
                           val tys'' = List.map (TyU.applySubst tvSubst) tys'
                           in
                             S.A_Var(x', tys'')
                           end
                      (* end case *))
                  | SOME(Arg atm) => atm
                  | NONE => (S.A_Var(x, renameTys (env, tys)))
                (* end case *))
            | S.A_DCon(dc, tys) => S.A_DCon(dc, renameTys (env, tys))
            | atm => atm
          (* end case *))

  (* instantiate any _free_ type variables in the type scheme to their instantiations.
   * Returns `NONE` when there are no free type variables in the domain of `tvSubst`.
   *)
    fun freshTyScheme (tvSubst, Ty.TyScheme(tvs, ty)) =
          if TyU.domainOccursInTy(tvSubst, ty)
            then SOME(Ty.TyScheme(tvs, TyU.applySubst tvSubst ty))
            else NONE

  (* bind a variable to a value *)
    fun bindVal (E{bMap, tvSubst, vSubst}, x, v) = (
          ctlSay ["bindVal: ", v2s x, " := ", valToString v, "\n"];
          E{tvSubst = tvSubst, vSubst = vSubst, bMap = VMap.insert (bMap, x, v)})

  (* bind the variable `x` to an atom; this operation is used when the atom is going
   * to be substituted for the variable in the variable's scope (e.g., the
   * parameter of an inlined function), so we need to do some census count
   * bookkeeping when the atom is a variable `y`.  In that case, we are removing
   * one use of `y`, but adding the uses/applications of `x` to `y`.
   *)
    fun bindArg info (env, x, atm) = (
          case atm
           of S.A_Var(y, tys) => (
                ctlSay [
                    "bindArg: ", C.varToString info y, tys2s tys,
                    " for ", C.varToString info x, "\n"
                  ];
                C.replaceWith info (x, y))
            | _ => ()
          (* end case *);
          insertVar (env, x, atm))

  (* bind type variables to types *)
    fun bindTVsToTys (E{tvSubst, vSubst, bMap}, tvs, tys) = let
          val tvSubst = extendTVSubst (tvSubst, tvs, tys)
          in
            E{tvSubst = tvSubst, vSubst = vSubst, bMap = bMap}
          end

  (* `freshVar (env, x)` creates a fresh, type-specialized version of `x` plus
   * an updated environment that maps `x` to the new variable.  Type specialization
   * is not required when the variable's type is not modified,  In that case,
   * `freshVar` just returns its arguments.
   *)
    fun freshVar info (env as E{tvSubst, vSubst, bMap}, x) = (
          case freshTyScheme(tvSubst, Var.typeOf x)
           of SOME tyScm' => let
              (* inside a beta expansion we need to rename variables with new
               * types.
               *)
                val x' = Var.newPoly(Var.nameOf x, tyScm')
                val env' = E{
                        tvSubst = tvSubst,
                        vSubst = VMap.insert(vSubst, x, Var x'),
                        bMap = bMap
                      }
                in
                  ctlSay [
                      "freshVar: ",
                      v2s x, " : ", TyU.schemeToString(Var.typeOf x),
                      " ==> ", v2s x', " : ", TyU.schemeToString tyScm',
                      "\n"
                    ];
                  C.share info (x, x');
                  (x', env')
                end
            | NONE => (x, env)
          (* end case *))

  (* `freshFB (env, fb)` returns `(fb', env')` where `fb'` has a fresh function
   * variable (if necessary) and `env'` provides the renaming of that variable.
   * The new lambda (`fb'`) will have the same label and parameter variable as
   * `fb`).
   *)
    fun freshFB info (env, S.FB(f, lab, x, e)) = let
          val (f', env) = freshVar info (env, f)
          in
            (S.FB(f', lab, x, e), env)
          end

  (* bind a variable to a rhs expression.  The rhs has been contracted already,
   * but the lhs is the original variable.  The `tvs` argument is the list of
   * bound type variables for LetPoly.  If we do not establish a binding then
   * we freshen the lhs variable.
   *)
    fun bindRHS info (env, x, tvs, S.E(_, rhs)) = let
        (* because we many not contract uses of the variable, we need to
         * generate a fresh one.
         *)
          fun bindV v = let
                val (x', env') = freshVar info (env, x)
                in
                  (x', bindVal (env', x', v))
                end
          in
            case rhs
             of S.E_DConApp(dc, _, atm) => bindV (CONS(tvs, dc, atm))
              | S.E_Tuple args => bindV (TPL(tvs, args))
              | S.E_Atom atm => (* here we expect tvs <> [] *)
 if List.null tvs then raise Fail(concat[
 "bindRHS: ", v2s x, tvs2s tvs, " ==> ", Util.atomToString atm
 ]) else
                  (x, bindVal (env, x, ATOM(tvs, atm)))
              | _ => freshVar info (env, x)
            (* end case *)
          end

  (* lookup the rhs binding of a variable *)
    fun lookupRHS (E{bMap, ...}, x) = (case VMap.find(bMap, x)
           of SOME v => v
            | NONE => UNKNOWN
          (* end case *))

(* TODO: now that expressions have labels, we should use them to record
 * purity info.
 *)
  (* is an expression "pure"? *)
    fun hasEffect (S.E(_, e)) = (case e
           of S.E_Let(_, e1, e2) => hasEffect e1 orelse hasEffect e2
            | S.E_LetPoly(_, _, _, e2) => hasEffect e2
            | S.E_Fun(_, e) => hasEffect e
            | S.E_Apply _ => true
            | S.E_DConApp _ => false
            | S.E_Prim(S.Arith _, _, _) => true    (* raise Div/Overflow *)
            | S.E_Prim(S.Setter _, _, _) => true   (* assignment *)
            | S.E_Prim _ => false
            | S.E_Tuple _ => false
            | S.E_Select _ => false
            | S.E_If(_, _, e1, e2, _) => hasEffect e1 orelse hasEffect e2
            | S.E_Case(_, rules, _) =>
                List.exists (fn (S.RULE(_, _, e)) => hasEffect e) rules
            | S.E_Handle(e1, _, _, _) => hasEffect e1
            | S.E_Raise _ => true
            | S.E_Atom _ => false
          (* end case *))

  (* memoized check for the "purity" of an expression; returns `true` if
   * the expression `e` has an effect and `false` if it is pure.
   *)
    fun purityChk e = let
          val cache = ref NONE
          fun chk () = (case !cache
                 of SOME flg => flg
                  | NONE => let
                      val flg = hasEffect e
                      in
                        cache := SOME flg;
                        flg
                      end
                (* end case *))
          in
            chk
          end

  (* update the census counts to account for the deletion of the `exp` *)
    fun delete info (env, exp) = let
          val decUse' = C.decUse info
          val decApp' = C.decApp info
          fun decUse x = let val x = lookupVar (env, x)
                in
                  ctlSay ["## decUse dead ", C.varToString info x, "\n"];
                  decUse' x
                end
          fun decApp x = let val x = lookupVar (env, x)
                in
                  ctlSay ["## decApp dead ", C.varToString info x, "\n"];
                  decUse' x; decApp' x
                end
          val renameAtom = renameAtom info
          fun decAtom atm = (case renameAtom (env, atm)
                 of (S.A_Var(x, _)) => decUse x
                  | _ => ()
                (* end case *))
          fun delFB (S.FB(_, _, _, e)) = delExp e
          and delExp (S.E(_, e)) = (case e
                 of S.E_Let(_, e1, e2) => (delExp e1; delExp e2)
                  | S.E_LetPoly(_, _, e1, e2) => (delExp e1; delExp e2)
                  | S.E_Fun(fbs, e) => (List.app delFB fbs; delExp e)
                  | S.E_Apply(f, _, arg) => (decApp f; decAtom arg)
                  | S.E_DConApp(_, _, arg) => decAtom arg
                  | S.E_Prim(_, _, args) => List.app decAtom args
                  | S.E_Tuple args => List.app decAtom args
                  | S.E_Select(_, x, _) => decUse x
                  | S.E_If(tst, args, e1, e2, _) => (
                      List.app decAtom args; delExp e1; delExp e2)
                  | S.E_Case(arg, rules, _) => (
                      decAtom arg;
                      List.app (fn (S.RULE(_, _, e)) => delExp e) rules)
                  | S.E_Handle(body, _, hndlr, _) => (delExp body; delExp hndlr)
                  | S.E_Raise(_, arg, _) => decAtom arg
                  | S.E_Atom atm => decAtom atm
                (* end case *))
          in
            delExp exp
          end

  (* select the first element of a list that satisfies the specified predicate and
   * return `SOME(item, lst)` where `item` is the selected item and `lst` is the
   * residual list.  If no such item exists, then return `NONE`.
   *)
    fun remove pred = let
          fun rmv ([], _) = NONE
            | rmv (x::xs, prefix) = if pred x
                then SOME(x, List.revAppend(prefix, xs))
                else rmv (xs, x::prefix)
          in
            fn lst => rmv (lst, [])
          end

    fun contractOnce info = let
        (* bookkeeping for deleteded dead code *)
          val delete = delete info
          fun deleteRules (env, rules) =
                List.app (fn (S.RULE(_, _, e)) => delete (env, e)) rules
        (* some debug support *)
          val v2s = C.varToString info
          fun atm2s (S.A_Var(x, tys)) = v2s x ^ tys2s tys
            | atm2s atm = Util.atomToString atm
        (* helper functions for use and application counts *)
          val useCntOf = C.useCntOf info
          val appCntOf = C.appCntOf info
          val incUse = C.incUse info
          val decUse = C.decUse info
          val incApp = C.incApp info
          val decApp = C.decApp info
          val isUsed = C.isUsed info
          fun incVar x = (ctlSay ["## incVar ", v2s x, "\n"]; incUse x)
          fun decVar x = (ctlSay ["## decVar ", v2s x, "\n"]; decUse x)
          fun incAtom (S.A_Var(x, _)) = incVar x
            | incAtom _ = ()
          fun decAtom (S.A_Var(x, _)) = decVar x
            | decAtom _ = ()
          val freshVar = freshVar info
          val freshFB = freshFB info
          val bindArg = bindArg info
          val bindRHS = bindRHS info
          val renameAtom = renameAtom info
        (* contract a function binding; note that we have already freshened `f` *)
          fun xformFB env (fb as S.FB(f, lab, x, e)) = if (useCntOf f = 0)
                then fb (* don't bother to optimize dead code *)
                else let
                  val (x', env') = freshVar (env, x)
                  in
                    ctlSay [
                        "xformFB: ", v2s f, " ", v2s x', " = ...\n"
                      ];
                    if Var.same(x, x') then () else Var.setBindingLabel(x', lab);
                    S.FB(f, lab, x', xformExp(env', e))
                  end
        (* contract an expression *)
          and xformExp (env, exp as S.E(lab, e)) : S.exp = (case e
                 of S.E_Let(x, e1, e2) => let
                      val hasEffect = purityChk e1
                    (* bookeeping for when e1 is dead *)
                      fun deadCode (env, x, e1) = (
                            ctlSay ["dead code: `let ", v2s x, " = ...\n"];
                            ST.Counter.tick cntDeadVar;
                            delete (env, e1))
                      in
                      (* check for dead code *)
                        if isUsed x orelse hasEffect()
                          then let
                            val _ = ctlSay [
                                    "xformExp: `let ", v2s x, " = ...\n"
                                  ]
                            in
                              case xformExp (env, e1)
                               of S.E(_, S.E_Atom atm) => (
                                    ST.Counter.tick cntRename;
                                    xformExp (bindArg (env, x, atm), e2))
                                | e1' => let
                                  (* specialize x's type, if necessary *)
                                    val (x', env') = bindRHS (env, x, [], e1')
                                    val e2' = xformExp (env', e2)
                                    in
                                    (* check for dead code again *)
                                      if isUsed x' orelse hasEffect()
                                        then SimpleOptUtil.mkLet(x', e1', e2')
                                        else (
                                          deadCode (env, x', e1');
                                          e2')
                                    end
                            end
                          else (
                            deadCode (env, x, e1);
                            xformExp (env, e2))
                      end
                  | S.E_LetPoly(x, tvs, e1, e2) => let
                    (* bookeeping for when e1 is dead *)
                      fun deadCode (env, x, e1) = (
                            ctlSay ["dead code: `letpoly ", v2s x, " = ...\n"];
                            ST.Counter.tick cntDeadVar;
                            delete (env, e1))
                      in
                      (* note that the rhs of LetPoly cannot have an effect *)
                        if isUsed x
                          then let
                            val _ = ctlSay [
                                    "xformExp: `letpoly ", v2s x, " = ",
                                    tvs2s tvs, " ...\n"
                                  ]
                            val e1' = xformExp (env, e1)
                          (* specialize x's type, if necessary *)
                            val (x', env') = bindRHS (env, x, tvs, e1')
                            val e2' = xformExp (env', e2)
                            in
                            (* check for dead code again *)
                              if isUsed x'
                                then S.E(lab, S.E_LetPoly(x', tvs, e1', e2'))
                                else (
                                  deadCode (env, x', e1');
                                  e2')
                            end
                          else ( (* `e1` is dead code *)
                            deadCode (env, x, e1);
                            xformExp (env, e2))
                      end
                  | S.E_Fun(fbs, e) => let
(* TODO: eliminate functions that just call themselves *)
                    (* first we introduce fresh function names (if necessary) *)
                      val (fbs', env') = List.foldr
                            (fn (fb, (fbs, env)) => let
                                  val (fb', env') = freshFB (env, fb)
                                  in
                                    (fb'::fbs, env')
                                  end)
                              ([], env) fbs
                    (* next we optimize the scope of the binding in an environment
                     * where the non-escaping functions that are just called once
                     * are bound to their definition.
                     *)
(* TODO: if we bind f to S.FB in its non-recursive scope and move the
 * test that the counts are 1 to the call site, then we can reduce the
 * number of traversals over the body of f, when all but one of its call
 * sites are removed as dead code (i.e., in a contracted case/if)
 *)
                      fun markFB (fb as S.FB(f, _, _, _), env) =
                            if (appCntOf f = 1) andalso (useCntOf f = 1)
                              then bindVal(env, f, FUN fb)
                              else env
                    (* the environment with inlining info *)
                      val env'' = List.foldl markFB env' fbs'
                      val e' = xformExp (env'', e)
                    (* then optimize the function bodies *)
                      val fbs' = List.map (xformFB env') fbs'
                    (* remove functions that are never used *)
                      fun chkForDead (fb as S.FB(f, _, _, e)) = if useCntOf f > 0
                              then SOME fb
                            else if wasInlined f
                              then NONE (* inlined functions do not need to be deleted *)
                              else (
                                ctlSay ["dead function ", v2s f, "\n"];
                                ST.Counter.tick cntDeadFun;
                                delete (env, e);
                                NONE)
                      in
                        case List.mapPartial chkForDead fbs'
                         of [] => e'
                          | fbs' => S.E(lab, S.E_Fun(fbs', e'))
                        (* end case *)
                      end
                  | S.E_Apply(f, tys, arg) => let
                      val (f', tys') = xformVar (env, f, renameTys (env, tys), true)
                      val arg' = xformAtom env arg
                      in
                        ctlSay [
                            "xformExp: ", v2s f', tys2s tys', " ",
                            atm2s arg', "\n"
                          ];
                        case lookupRHS(env, f')
                         of FUN(S.FB(_, _, param, body)) => let
                              val _ = ctlSay [
                                      "inline: ", v2s f', tys2s tys', " (",
                                      v2s param, " ==> ", atm2s arg', ")\n"
                                    ]
                              val env' = if List.null tys'
                                    then env
                                    else let
                                      val Ty.TyScheme(tvs, _) = Var.typeOf f'
                                      in
                                        bindTVsToTys (env, tvs, tys')
                                      end
                            (* substitute the argument for the parameter *)
                              val env' = bindArg (env', param, arg')
                              in
                              (* beta reduce the application (it is the only one). *)
                                ST.Counter.tick cntBeta;
                              (* record the elimination of the call *)
                                decApp f'; decVar f';
                                markInlined f';
                              (* replace the call with the body of the function *)
                                xformExp(env', body)
                              end
                          | _ => S.E(lab, S.E_Apply(f', tys', arg'))
                        (* end case *)
                      end
                  | S.E_DConApp(dc, tys, arg) =>
                      S.E(lab, S.E_DConApp(dc, renameTys (env, tys), xformAtom env arg))
                  | S.E_Prim(rator, tys, args) =>
                      S.E(lab, S.E_Prim(rator, renameTys (env, tys), List.map (xformAtom env) args))
(* TODO: tuple reconstruction *)
                  | S.E_Tuple args => S.E(lab, S.E_Tuple(List.map (xformAtom env) args))
                  | S.E_Select(i, x, tys) => let
                      val (x', tys') = xformVar (env, x, renameTys (env, tys), false)
                      in
                        case lookupRHS(env, x')
                         of TPL(tvs, args) => let
                              val atm = List.nth(args, i-1)
                              in
                                ctlSay [
                                    "contract `#", Int.toString i, " ",
                                    v2s x', " ==> ", atm2s atm, "`\n"
                                  ];
                                ST.Counter.tick cntTuple;
                                decVar x';
                                incAtom atm;
(* FIXME: need to do something about the type variables! *)
                                S.mkAtom atm
                              end
                          | UNKNOWN => S.E(lab, S.E_Select(i, x', tys'))
                          | v => raise Fail(concat[
                                "bogus select: ", v2s x, " is bound to ",
                                valToString v
                              ])
                        (* end case *)
                      end
                  | S.E_If(tst, args, e1, e2, ty) => let
                      val args' = List.map (xformAtom env) args
                      val e1' = xformExp (env, e1)
                      val e2' = xformExp (env, e2)
                      in
                        S.E(lab, S.E_If(tst, args', e1', e2', renameTy (env, ty)))
                      end
                  | S.E_Case(arg, rules, ty) =>
                      xformCase (env, lab, xformAtom env arg, rules, ty)
                  | S.E_Handle(body, ex, hndlr, ty) => S.E(lab, S.E_Handle(
                      xformExp (env, body),
                      ex, xformExp (env, hndlr),
                      renameTy (env, ty)))
                  | S.E_Raise(loc, arg, ty) =>
                      S.E(lab, S.E_Raise(loc, xformAtom env arg, renameTy (env, ty)))
                  | S.E_Atom atm => let
                      val atm' = xformAtom env atm
                      in
                        ctlSay [
                            "xformExp: ", atm2s atm, " ==> ",
                            atm2s atm', "\n"
                          ];
                        S.E(lab, S.E_Atom atm')
                      end
                (* end case *))
        (* transform a case expression; we assume that `arg` has already been
         * transformed.
         *)
          and xformCase (env, lab, arg, cases, ty) = let
                val _ = ctlSay [
                        "xformCase: `case (", atm2s arg, ") of ...`\n"
                      ]
              (* given a predicate on patterns, seach the rules for a match *)
                fun search pred = (
                      ctlSay [
                          "contract `case ", atm2s arg, "`\n"
                        ];
                      ST.Counter.tick cntCase;
                      case remove pred cases
                       of SOME(S.RULE(_, S.P_Var x, act), cases') => (
                            deleteRules (env, cases');
                            xformExp(bindArg(env, x, arg), act))
                        | SOME(S.RULE(_, _, act), cases') => (
                            decAtom arg;
                            deleteRules (env, cases');
                            xformExp(env, act))
                        | _ => raise Fail "impossible"
                      (* end case *))
              (* default contraction just contracts the individual rules *)
                fun default () = S.E(lab, S.E_Case(
                      arg,
                      List.map (xformRule (env, arg)) cases,
                      renameTy (env, ty)))
                in
                (* if the argument can be resolved to a value/atom, then we
                 * apply the match to contract the case.
                 *)
                  case arg
                   of S.A_Var(x, tys) => (case lookupRHS(env, x)
                         of v as CONS(tvs, dc, atm) => let
                              fun match (S.RULE(_, S.P_DConApp(dc', _, _), _)) =
                                    DataCon.same(dc,dc')
                                | match (S.RULE(_, S.P_Var _, _)) = true
                                | match _ = false
                              in
(* FIXME: need to do something about the tvs -> tys mapping *)
                                ctlSay [
                                    "contract `case ", atm2s arg,
                                    " [= ", DataCon.nameOf dc, " ",
                                    atm2s atm, "]`\n"
                                  ];
                                ST.Counter.tick cntCase;
                                decVar x;
                                case remove match cases
                                 of SOME(S.RULE(_, S.P_DConApp(_, _, x), act), cases') => (
                                      deleteRules (env, cases');
                                      xformExp(bindVal(env, x, ATOM([], atm)), act))
                                  | SOME(S.RULE(_, S.P_Var x, act), cases') => (
                                      deleteRules (env, cases');
                                      xformExp(bindVal(env, x, v), act))
                                  | _ => raise Fail "impossible"
                                (* end case *)
                              end
                          | _ => default ()
                        (* end case *))
                    | S.A_DCon(dc, _) => let
                        fun match (S.RULE(_, S.P_DCon(dc', _), _)) = DataCon.same(dc, dc')
                          | match (S.RULE(_, S.P_Var _, _)) = true
                          | match _ = false
                        in
                          search match
                        end
                    | S.A_Lit(lit, _) => let
                        fun match (S.RULE(_, S.P_Lit(lit', _), _)) = Literal.same(lit, lit')
                          | match (S.RULE(_, S.P_Var _, _)) = true
                          | match _ = false
                        in
                          search match
                        end
                    | _ => default ()
                  (* end case *)
                end

        (* transform a case rule, where `atm` is the argument atom. For a given
         * `(pat, act)` rule, we know that `atm` must match `pat`, so we add
         * that information to the value map.
         *)
          and xformRule (env, atm as S.A_Var(y, _)) (S.RULE(lab, pat, act)) = (
                case pat
                 of S.P_DConApp(dc, tys, x) => let
                      val tys' = renameTys (env, tys)
                      val (x', env') = freshVar (env, x)
                      val env' = bindVal (env', y, CONS([], dc, S.A_Var(x', [])))
                      in
                        S.RULE(lab, S.P_DConApp(dc, tys', x'), xformExp(env', act))
                      end
                  | S.P_Var x => let
                      val (x', env') = freshVar (env, x)
                      in
                        S.RULE(lab, S.P_Var x', xformExp(env', act))
                      end
                  | S.P_DCon(dc, tys) => let
                      val tys' = renameTys (env, tys)
                      val env' = bindVal (env, y, ATOM([], S.A_DCon(dc, tys')))
                      in
                        S.RULE(lab, S.P_DCon(dc, tys'), xformExp(env', act))
                      end
                  | S.P_Lit(lit, ty) => let
                      val env' = bindVal (env, y, ATOM([], S.A_Lit(lit, ty)))
                      in
                        S.RULE(lab, pat, xformExp(env', act))
                      end
                (* end case *))
          and xformVar (env, x, tys, isApply) = let
                val (x', tys') = rename(env, x, tys)
                in
                  case lookupRHS(env, x')
                   of ATOM(tvs, S.A_Var(y, tys')) => (
                      (* we have `let/letpoly x = <tvs> y<tys'> in ... x<tys'> ...` *)
                        decUse x; incUse y;
                        if isApply then (decApp x; incApp y) else ();
                        (y, specializeTysForVar(x, tys, tys')))
                    | _ => (x', tys')
                  (* ens case *)
                end
        (* rename variable atoms and substitute for type variables *)
          and xformAtom env atm = (case renameAtom(env, atm)
                 of atm' as S.A_Var(x, tys') => (case lookupRHS(env, x)
                       of ATOM(tvs, atm'') => (
                          (* we have `let/letpoly x = <tvs> atm'' in ... x<tys'> ...` *)
                            decUse x;
                            case atm''
                             of S.A_Var(y, tys'') => (
                                  incUse y;
                                  S.A_Var(y, specializeTysForVar(x, tys', tys'')))
                              | S.A_DCon(dc, tys'') =>
                                  S.A_DCon(dc, specializeTysForVar(x, tys', tys''))
                              | _ => atm''
                            (* end case *))
                        | _ => atm'
                      (* ens case *))
                  | atm' => atm'
                (* end case *))
          in
            fn lambda => xformFB emptyEnv lambda
          end

    fun transform (info, S.CU lambda) = let
          val contractOnce = contractOnce info
        (* run contraction until nothing changes *)
          fun lp (lambda, nRnds, nticks) = let
                val _ = ctlSay ["***** Contract ******\n"]
                val lambda = contractOnce lambda
                val nticks' = ST.Group.total SimpleOptStats.group
                in
                  if Controls.get Ctl.debugSimpleOpt
                    then let
                      val _ = say ["**** Check census counts\n"];
                      val errors = Census.check say (S.CU lambda, info);
                      val _ = CheckSimpleAST.check ("contract", S.CU lambda)
                      in
                        if not(Controls.get Ctl.dumpSimple)
                          then PrintSimpleAST.output (
                            Log.outstream(), "after contract", S.CU lambda)
                        else ();
                        if errors then raise Fail "census bug in contraction" else ()
                      end
                    else ();
                  if nticks' > nticks
                    then lp (lambda, nRnds+1, nticks')
                    else (
                      ST.Counter.bump (cntRound, nRnds);
                      S.CU lambda)
                end
          in
            lp (lambda, 0, ST.Group.total SimpleOptStats.group)
          end

  end
