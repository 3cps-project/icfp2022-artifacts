(* beta.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Beta reduction for Simple AST.
 *)

structure Beta : sig

    val reduce : Census.t
          -> SimpleAST.lambda * SimpleTypes.ty list * SimpleAST.atom
          -> SimpleAST.exp

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure TVMap = TyVar.Map
    structure Var = SimpleVar
    structure VMap = SimpleVar.Map
    structure TyU = SimpleTypeUtil

    datatype env = E of {
        tvMap : TyU.tv_env,
        vMap : Var.t VMap.map
      }

    fun newEnv (tvs, tys) = E{
            tvMap = TyU.extendSubst (TVMap.empty, tvs, tys),
            vMap = VMap.empty
          }
    fun freshTVs (E{tvMap, vMap}, tvs) = let
          val tvs' = List.map (fn _ => TyVar.new()) tvs
          val env' = E{
                  tvMap = TyU.extendSubst (tvMap, tvs, List.map Ty.VarTy tvs'),
                  vMap = vMap
                }
          in
            (tvs', env')
          end
    fun insertVar (E{tvMap, vMap}, x, x') = E{
            tvMap = tvMap,
            vMap = VMap.insert (vMap, x, x')
          }
    fun rnTy (E{tvMap, ...}) = TyU.applySubst tvMap
    fun rnTys env = List.map (rnTy env)

    fun reduce info = let
        (* census operations *)
          val incUse = Census.incUse info
          val incApp = Census.incApp info
          val copyInfo = Census.copy info
          fun useVar x = (incUse x; x)
          fun appVar x = (incApp x; x)
        (* beta reduce the application *)
          fun reduce' (S.FB(f, _, param, body), tys, arg) = let
                val Ty.TyScheme(tvs, _) = Var.typeOf f
                val initialEnv = newEnv (tvs, tys)
                fun freshVar (env, x) = (case Var.typeOf x
                       of Ty.TyScheme([], ty) => Var.new(Var.nameOf x, rnTy env ty)
                        | Ty.TyScheme(tvs, ty) => let
                            val (tvs', env) = freshTVs (env, tvs)
                            val ty' = rnTy env ty
                            in
                              Var.newPoly (Var.nameOf x, Ty.TyScheme(tvs', ty'))
                            end
                      (* end case *))
                fun bindVar (env, x) = let
                      val x' = freshVar (env, x)
                      in
                        copyInfo (x, x');
                        (x', insertVar(env, x, x'))
                      end
              (* rename a variable use; if the variable is free in the function
               * body, then we bump its use count.
               *)
                fun renameVar (E{vMap, ...}, x) = (case VMap.find(vMap, x)
                       of SOME x' => x'
                        | NONE => useVar x
                      (* end case *))
              (* rename a function application; if the function is free in the function
               * body, then we bump its use and application counts.
               *)
                fun renameFun (E{vMap, ...}, f) = (case VMap.find(vMap, f)
                       of SOME f' => f'
                        | NONE => (useVar f; appVar f)
                      (* end case *))
                fun xformAtom env (S.A_Var(x, tys)) = if Var.same(x, param)
                      then arg
                      else S.A_Var(renameVar(env, x), rnTys env tys)
                  | xformAtom env (S.A_DCon(dc, tys)) = S.A_DCon(dc, rnTys env tys)
                  | xformAtom _ atm = atm
                fun xform (env, S.E(_, e)) =
                    (* Note that we create fresh labels, since the old body of the
                     * function may still be in the code.
                     *)
                      S.E(Label.new(), xformRep (env, e))
                and xformRep (env, e) = (case e
                       of S.E_Let(x, e1, e2) => let
                            val e1' = xform (env, e1)
                            val (x', env') = bindVar (env, x)
                            val e2' = xform (env', e2)
                            in
                              S.E_Let(x', e1', e2')
                            end
                        | S.E_LetPoly(x, tvs, e1, e2) => let
                            val (tvs', env') = freshTVs (env, tvs)
                            val e1' = xform (env', e1)
                            val (x', env'') = bindVar (env, x)
                            val e2' = xform (env'', e2)
                            in
                              S.E_LetPoly(x', tvs', e1', e2')
                            end
                        | S.E_Fun(fbs, e) => let
                          (* first we assign fresh names for the functions *)
                            fun bindFB (S.FB(f, _, x, e), (env, fbs)) = let
                                  val (f', env') = bindVar (env, f)
                                  in
                                    (env', (f', x, e)::fbs)
                                  end
                            val (env', fbs') = List.foldr bindFB (env, []) fbs
                          (* then transform functions *)
                            fun xformFB (f', x, e) = let
                                  val (x', env') = bindVar (env', x)
                                  in
                                    S.mkFB(f', x', xform(env', e))
                                  end
                            in
                              S.E_Fun(List.map xformFB fbs', xform(env', e))
                            end
                        | S.E_Apply(f, tys, arg) => S.E_Apply(
                            renameFun(env, f),
                            rnTys env tys,
                            xformAtom env arg)
                        | S.E_DConApp(dc, tys, atm) =>
                            S.E_DConApp(dc, rnTys env tys, xformAtom env atm)
                        | S.E_Prim(p, tys, atms) =>
                            S.E_Prim(p, rnTys env tys, List.map (xformAtom env) atms)
                        | S.E_Tuple atms => S.E_Tuple(List.map (xformAtom env) atms)
                        | S.E_Select(i, x, tys) =>
                            S.E_Select(i, renameVar(env, x), rnTys env tys)
                        | S.E_If(p, atms, e1, e2, ty) =>
                            S.E_If(p, List.map (xformAtom env) atms,
                              xform(env, e1), xform(env, e2),
                              rnTy env ty)
                        | S.E_Case(arg, rules, ty) => let
                            fun doRule (S.RULE(lab, p, e)) = let
                                  fun mk (env, p) = S.RULE(lab, p, xform(env, e))
                                  in
                                    case p
                                     of S.P_DConApp(dc, tys, x) => let
                                          val tys' = rnTys env tys
                                          val (x', env) = bindVar (env, x)
                                          in
                                            mk (env, S.P_DConApp(dc, tys', x'))
                                          end
                                      | S.P_Var x => let
                                          val (x', env) = bindVar (env, x)
                                          in
                                            mk (env, S.P_Var x')
                                          end
                                      | S.P_DCon(dc, tys) =>
                                          mk (env, S.P_DCon(dc, rnTys env tys))
                                      | S.P_Lit _ => mk (env, p)
                                    (* end case *)
                                  end
                            in
                              S.E_Case(xformAtom env arg,
                                List.map doRule rules,
                                rnTy env ty)
                            end
                        | S.E_Handle(e1, x, e2, ty) => let
                            val (x', env') = bindVar(env, x)
                            in
                              S.E_Handle(xform(env, e1), x', xform(env', e2), rnTy env ty)
                            end
                        | S.E_Raise(loc, atm, ty) =>
                            S.E_Raise(loc, xformAtom env atm, rnTy env ty)
                        | S.E_Atom atm => S.E_Atom(xformAtom env atm)
                      (* end case *))
                in
                (* adjust the argument's census counts, if it is a variable *)
                  case arg
                   of S.A_Var(x, _) => Census.replaceWith info (param, x)
                    | _ => ()
                  (* end case *);
                (* beta-expand the body *)
                  xform (initialEnv, body)
                end
          in
            reduce'
          end

  end

