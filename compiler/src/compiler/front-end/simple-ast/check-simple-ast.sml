(* check-simple-ast.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Check the correctness of the Simple AST IR.  We currently check
 * the following properties:
 *
 *      type variables are only used within their scope
 *
 *      variables are only used within their scope
 *
 *      type applications have the correct arity
 *
 * TODO:
 *      check that terms are type correct
 *)

structure CheckSimpleAST : sig

  (* check the validity of the program; this function dumps the IR to the log file
   * and exits if any errors are detected.
   *)
    val check : string * SimpleAST.comp_unit -> SimpleAST.comp_unit

  (* check the validity of the program, including the census data. This function
   * dumps the IR to the log file and exits if any errors are detected.
   *)
    val checkWithCensus : Census.t -> string * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure TyCon = SimpleTyCon
    structure Var = SimpleVar
    structure DataCon = SimpleDataCon
    structure TVSet = TyVar.Set
    structure VSet = Var.Set
    structure TyUtil = SimpleTypeUtil
    structure U = SimpleASTUtil

    datatype env = E of {
        tvs : TVSet.set,        (* bound type variables *)
        vs : VSet.set           (* bound variables *)
      }

    val empty = E{tvs = TVSet.empty, vs = VSet.empty}
    fun addTVs (E{tvs, vs}, l) = E{tvs = TVSet.addList (tvs, l), vs = vs}
    fun addVar (E{tvs, vs}, x) = E{tvs = tvs, vs = VSet.add(vs, x)}
    fun tvInScope (E{tvs, ...}, tv) = TVSet.member(tvs, tv)
    fun varInScope (E{vs, ...}, x) = VSet.member(vs, x)

    fun dumpEnv (E{tvs, vs}) = (
          print "Env{\n";
          print (concat[
              "  tvs = {", String.concatWithMap ", " TyVar.toString (TVSet.toList tvs),
              "}\n"
            ]);
          print (concat[
              "  vs = {", String.concatWithMap ", " Var.toString (VSet.toList vs),
              "}\n"
            ]);
          print "}\n")

  (* property for detecting duplicate bindings of a variable *)
    local
      val {getFn, setFn} = Var.newFlag()
    in
    val hasBinding = getFn
    fun markAsBound x = setFn(x, true)
    fun clrMark x = setFn(x, false)
    end (* local *)

    val pr = Log.msg
    fun cerror msg = pr ("== "::msg)

    fun error anyErrors = let
          fun err phase msg = (
                if !anyErrors then ()
                  else (
                    pr ["***** Bogus SimpleAST after ", phase, " *****\n"];
                    anyErrors := true);
                pr ("** " :: msg))
          in
            err
          end

    fun clearMarks fb = let
          fun clrExp (S.E(_, e)) = (case e
                 of S.E_Let(x, e1, e2) => (clrMark x; clrExp e1; clrExp e2)
                  | S.E_LetPoly(x, _, _, e2) => (clrMark x; clrExp e2)
                  | S.E_Fun(fbs, e) => (List.app clrFB fbs; clrExp e)
                  | S.E_If(_, _, e1, e2, _) => (clrExp e1; clrExp e2)
                  | S.E_Case(_, rules, _) => let
                      fun clrPat (S.P_DConApp(_, _, x)) = clrMark x
                        | clrPat (S.P_Var x) = clrMark x
                        | clrPat _ = ()
                      fun clrRule (S.RULE(_, p, e)) = (clrPat p; clrExp e)
                      in
                        List.app clrRule rules
                      end
                  | S.E_Handle(e1, x, e2, _) => (clrMark x; clrExp e1; clrExp e2)
                  | _ => ()
                (* end case *))
          and clrFB (S.FB(f, _, x, e)) = (clrMark f; clrMark x; clrExp e)
          in
            clrFB fb
          end

    fun tyArity (Ty.TyScheme(tvs, _)) = List.length tvs

  (* check if a function binding is a join function *)
    fun isJoinFB [S.FB(f, _, _, _)] = Var.isJoin f
      | isJoinFB _ = false

    fun check' anyErrors (phase, S.CU(cuFB as S.FB(_, _, cuParam, cuBody))) = let
          val error = error anyErrors phase
        (* check the validity of a type expression *)
          fun validTy (env, ty, cxt) = let
                fun err extra = (
                      error(cxt @ " has invalid type " :: TyUtil.toString ty :: extra);
                      false)
                fun valid (Ty.VarTy tv) = if not (tvInScope (env, tv))
                      then err ["; unbound type variable ", TyVar.toString tv, "\n"]
                      else true
                  | valid (Ty.ConTy(tys, tyc)) =
                      if TyCon.arityOf tyc <> length tys
                        then err ["; arity mismatch for ", TyCon.nameOf tyc, "\n"]
                        else List.all valid tys
                  | valid (Ty.FunTy(ty1, ty2)) = valid ty1 andalso valid ty2
                  | valid (Ty.TupleTy tys) = List.all valid tys
                in
                  ignore (valid ty)
                end
        (* check the validity of a type application *)
          fun chkTyApp (env, tyScm, tys, cxt) =
                if (tyArity tyScm <> List.length tys)
                  then error (cxt @ [" has type-arity mismatch\n"])
                  else validTy (env, TyUtil.applyScheme(tyScm, tys), cxt)
        (* check a binding occurrence of a variable *)
          fun chkVarBind (env, x, cxt) = (
                  if (hasBinding x)
                    then error [
                        "multiple bindings of ", Var.toString x, " in ", cxt, "\n"
                      ]
                    else markAsBound x;
                  addVar (env, x))
        (* check the type of a variable at its binding occurrence; this check
         * adds any bound type variables to the environment.
         *)
          fun chkVarBindTy (env, isMono, x) = let
                val tyScm = Var.typeOf x
                fun chkTyVar tv = if tvInScope (env, tv)
                      then (
                        error [
                            "type variable ", TyVar.toString tv,
                            " in ", TyUtil.schemeToString tyScm,
                            " is previously bound\n"
                          ];
                        false)
                      else true
                in
                  case (isMono, tyScm)
                   of (true, Ty.TyScheme([], ty)) => (
                        validTy (env, ty, ["type of ", Var.toString x]);
                        env)
                    | (false, Ty.TyScheme(tvs, ty)) => let
                        val _ = ignore (List.all chkTyVar tvs);
                        val env = addTVs (env, tvs)
                        in
                          validTy (env, ty, [" variable ", Var.toString x, "\n"]);
                          env
                        end
                    | (true, _) => (
                        error [
                            "expected mono-type for ", Var.toString x,
                            " but  found ", TyUtil.schemeToString tyScm, "\n"
                          ];
                        env)
                  (* end case *)
                end
        (* check a use occurrence of a variable *)
          fun chkVarUse (env, x, tys) = (
              (* check that x is in scope *)
                if not(varInScope(env, x))
                  then error ["unbound variable ", Var.toString x, "\n"]
                  else ();
              (* check the validity of the type *)
                chkTyApp (env, Var.typeOf x, tys, ["use of ", Var.toString x]))
        (* check the occurrence of a data constructor *)
          fun chkDCUse (env, dc, tys, hasArg) = (
                case (DataCon.isNullary dc, hasArg)
                 of (true, true) => error [
                        "application of nullary constructor ", DataCon.toString dc, "\n"
                      ]
                  | (false, false) => error [
                        "missing argument for constructor ", DataCon.toString dc, "\n"
                      ]
                  | _ => ()
                (* end case *);
                let val tyScm = DataCon.typeOf dc
                in
                (* check arity and if that is okay, check the validity of the type *)
                  chkTyApp (env, tyScm, tys, ["use of ", DataCon.toString dc])
                end)
        (* check an atom *)
          fun chkAtom env (S.A_Var(x, tys)) = chkVarUse (env, x, tys)
            | chkAtom env (S.A_DCon(dc, tys)) = chkDCUse (env, dc, tys, false)
            | chkAtom env (S.A_Lit(_, ty)) = validTy(env, ty, ["literal"])
            | chkAtom _ (S.A_Unit) = ()
        (* check an expression *)
          fun chkExp (env, S.E(_, e)) = (case e
                 of S.E_Let(x, e1, e2) => let
                      val _ = chkExp (env, e1)
                      val env' = chkVarBindTy (chkVarBind (env, x, "let"), true, x)
                      in
                        chkExp (env', e2)
                      end
                  | S.E_LetPoly(x, tvs, e1, e2) => let
                      val env' = addTVs(env, tvs)
                      val _ = chkExp (addTVs(env, tvs), e1)
                      val env' = chkVarBindTy (chkVarBind (env, x, "letpoly"), false, x)
                      in
                      (* check that e1 is a value *)
                        case e1
                         of S.E(_, S.E_DConApp _) => ()
                          | S.E(_, S.E_Tuple _) => ()
                          | S.E(_, S.E_Select _) => ()
                          | S.E(_, S.E_Atom _) => ()
                          | _ => error [
                                "rhs of `letpoly ", Var.toString x,
                                " = ...`, is not a value\n"
                              ]
                        (* end case *);
                        chkExp (env', e2)
                      end
                  | S.E_Fun(fbs, e) => let
                      fun pass1 (S.FB(f, _, _, _), env) = chkVarBind (env, f, "fun")
                      val env = List.foldl pass1 env fbs
                      fun pass2 (S.FB(f, _, x, e)) = let
                            val env' = chkVarBindTy (env, false, f)
                            val env' = chkVarBind (env', x, "fun")
                            val _ = chkVarBindTy (env', true, x)
                            in
                              chkExp (env', e)
                            end
                      in
                      (* if this is the binding of a join point, then the expression
                       * `e` cannot be a `let`, `letpoly`, or non-join `fun` binding.
                       *)
                        if isJoinFB fbs
                          then let
                            fun err c = let
                                  val [S.FB(f, _, _, _)] = fbs
                                  in
                                    error [
                                        "continuation of join ", Var.toString f,
                                        " is a `", c, "` binding\n"
                                      ]
                                  end
                            in
                              case e
                               of S.E(_, S.E_Let _) => err "let"
                                | S.E(_, S.E_LetPoly _) => err "letpoly"
                                | S.E(_, S.E_Fun(fbs', _)) => if isJoinFB fbs'
                                    then ()
                                    else err "fun"
                                | _ => ()
                              (* end case *)
                            end
                          else ();
                        List.app pass2 fbs;
                        chkExp (env, e)
                      end
                  | S.E_Apply(f, tys, arg) => (
                      chkVarUse (env, f, tys);
                      chkAtom env arg)
                  | S.E_DConApp(dc, tys, arg) => (
                      chkDCUse (env, dc, tys, true);
                      chkAtom env arg)
                  | S.E_Prim(rator, tys, args) => let
                      val cxt = ["application of ", U.primToString rator]
                      in
(* TODO: check arity of rator against number of arguments *)
                        List.app (fn ty => validTy(env, ty, cxt)) tys;
                        List.app (chkAtom env) args
                      end
                  | S.E_Tuple atms => List.app (chkAtom env) atms
                  | S.E_Select(i, x, tys) => chkVarUse (env, x, tys)
                  | S.E_If(tst, args, e1, e2, ty) => (
                      List.app (chkAtom env) args;
                      validTy (env, ty, ["if expression"]);
                      chkExp (env, e1);
                      chkExp (env, e2))
                  | S.E_Case(arg, rules, ty) => let
                      fun chkRule (S.RULE(_, pat, e)) = let
                            val env = (case pat
                                   of S.P_DConApp(dc, tys, x) => (
                                        chkDCUse (env, dc, tys, true);
                                        chkVarBindTy (chkVarBind (env, x, "pat"), true, x))
                                    | S.P_Var x =>
                                        chkVarBindTy (chkVarBind (env, x, "pat"), true, x)
                                    | S.P_DCon(dc, tys) => (
                                        chkDCUse (env, dc, tys, false);
                                        env)
                                    | S.P_Lit(_, ty) => (
                                        validTy(env, ty, ["literal pattern"]);
                                        env)
                                  (* end case *))
                            in
                              chkExp (env, e)
                            end
                      in
                        chkAtom env arg;
                        validTy (env, ty, ["case expression"]);
                        List.app chkRule rules
                      end
                  | S.E_Handle(e, ex, h, ty) => let
                      val _ = chkExp (env, e)
                      val env = chkVarBind (env, ex, "handle")
                      val _ = chkVarBindTy (env, true, ex)
                      in
                        chkExp (env, h)
                      end
                  | S.E_Raise(_, atm, ty) => (
                     chkAtom env atm;
                   (* check that the declared type is valid *)
                     validTy (env, ty, ["raise ", U.atomToString atm]))
                     (* check that the atom's type is exn *)
                  | S.E_Atom atm => chkAtom env atm
                 (* end case *))
        (* the initial environment *)
          val env = chkVarBind (empty, cuParam, "compilation unit")
          in
            chkExp (env, cuBody);
            clearMarks cuFB;
            !anyErrors
          end (* check *)

    fun checkWithCensus' info (phase, cu) = let
          val anyErrors = ref false
          val error = error anyErrors phase
          val _ = Census.check error (cu, info)
          in
            check' anyErrors (phase, cu)
          end

    val check = Log.after {
            dumpCtl = Ctl.dumpSimple,
            checkCtl = Ctl.checkSimple,
            output = PrintSimpleAST.output,
            checkIR = check' (ref false),
            fail = fn msg => (
                TextIO.output (TextIO.stdErr, msg);
                OS.Process.exit OS.Process.failure)
          }

    fun checkWithCensus info = Log.after {
            dumpCtl = Ctl.dumpSimple,
            checkCtl = Ctl.checkSimple,
            output = PrintSimpleAST.output,
            checkIR = checkWithCensus' info,
            fail = fn msg => (
                TextIO.output (TextIO.stdErr, msg);
                OS.Process.exit OS.Process.failure)
          }

  end
