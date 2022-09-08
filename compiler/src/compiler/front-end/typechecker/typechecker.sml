(* typechecker.sml
 *
 * COPYRIGHT (c) 2007 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * CMSC 22610 Sample code (Winter 2007)
 *)

structure Typechecker : sig

    val check : Error.err_stream * BindTree.comp_unit -> AST.comp_unit

  end = struct

    structure BT = BindTree
    structure E = Env
    structure U = Unify
    structure TU = TypeUtil
    structure C = Context
    structure ASet = AtomSet

    fun debug () = Controls.get Ctl.debugTypeChk
    fun say s = Log.msg("[TY] " :: s)

  (* error reporting *)
    datatype token = datatype TypeError.token
    val warning = Context.warning
    val error = Context.error

    val chkTy = ChkType.check
    val chkExp = ChkExp.check
    val chkValDcl = ChkExp.checkValDecl

  (* typecheck a datatype definition.  This requires two passes, since the
   * definition might consist of mutually recursive types.
   *
   * For processing a datatype declaration, we need to be a bit careful about
   * the order of things.  At the end, we want the constructors and datatype in
   * the environment, but not the type variables.  On the other hand, both the
   * type variables and datatype need to be in the environment to type check
   * the constructors.
   *)
    fun chkDataty (cxt, dts) = let
        (* the first pass establishes the type constructors *)
          fun pass1 ({span, tree=(tvs, tycId, _)}, (cxt, tycs)) = let
                val (tvs', cxt') = ChkType.bindTyVars (cxt, tvs)
                val tyc = TyCon.newDataTyc(tycId, tvs')
                in
                  if debug()
                    then say [
                        "chkDataty: `datatype ", TyCon.toString tyc, " = ...`\n"
                      ]
                    else ();
                  (C.insertTyCon(cxt', tycId, tyc), (tvs', tyc)::tycs)
                end
          val (cxt', tycs) = List.foldr pass1 (cxt, []) dts
        (* in the second pass, we check the types of the constructors for each datatype
         * and build the context that we are going to return.
         *)
          fun pass2 ((tvs, tyc), {span, tree=(_, id, cons)}, acc) = let
              (* context for checking the types of constructors *)
                val newCon = DataCon.new tyc
                fun chkCons cxt (BT.MarkConDecl{span, tree}, (allCons, cxtWithCons)) =
                      chkCons (C.setSpan(cxt, span)) (tree, (allCons, cxtWithCons))
                  | chkCons cxt (BT.ConDecl(conid, optTy), (allCons, cxtWithCons)) = let
                      val optTy' = Option.map (fn ty => chkTy(cxt, ty)) optTy
                      val con' = newCon(conid, optTy')
                      in
                        (con' :: allCons, C.insertDCon (cxtWithCons, conid, con'))
                      end
                in
                  List.foldr (chkCons cxt') acc cons
                end
          val (allCons, cxtWithCons) = ListPair.foldr pass2 ([], cxt') (tycs, dts)
        (* insert the type constructors into the result context *)
          val resCxt = ListPair.foldl
                (fn ({tree=(_, tyc, _), ...}, (_, tyc'), cxt) => C.insertTyCon(cxt, tyc, tyc'))
                  cxtWithCons (dts, tycs)
          in
            (List.map AST.DConTopDec allCons, resCxt)
          end

  (* typecheck top-level declarations as described in Sections 6.2 and 6.3 *)
    fun chkTopDcl (cxt, decl) = (case decl
           of BT.MarkDecl{span, tree} => chkTopDcl (C.setSpan(cxt, span), tree)
            | BT.StructDecl(strId, sign, strDef) => (
                if debug()
                  then say [
                      "chkTopDcl: `structure ", BT.StrId.toString strId, " = ...`\n"
                    ]
                  else ();
                chkStrExp (cxt, strId, sign, strDef))
            | BT.LocalDecl(dcls1, dcls2) => let
                val cxt = C.localBegin cxt
                val (dcls1', cxt) = chkTopDcls (cxt, dcls1)
                val cxt = C.localIn cxt
                val (dcls2', cxt) = chkTopDcls (cxt, dcls2)
                val cxt = C.localEnd cxt
                in
                  (dcls1' @ dcls2', cxt)
                end
            | BT.TyDecl(tvs, id, ty) => let
                val _ = if debug()
                    then say [
                        "chkTopDcl: `type ",
                        case tvs
                         of [] => ""
                          | [tv] => (BT.TyVar.toString tv ^ " ")
                          | tvs => concat[
                                "(", String.concatWithMap "," BT.TyVar.toString tvs, ") "
                              ]
                        (* end case *),
                        BT.TycId.toString id, " = ",
                        BindTreeUtil.tyToString ty, "`\n"
                      ]
                    else ()
                val (tvs', cxt') = ChkType.bindTyVars (cxt, tvs)
                val ty' = chkTy (cxt', ty)
                in
                  ([], C.insertTyDef(cxt, id, AST.TyScheme(tvs', ty')))
                end
            | BT.DataDecl dts => chkDataty (cxt, dts)
            | BT.ExnDecl con => let
                fun chk (cxt, BT.MarkConDecl{span, tree}) = chk(C.setSpan(cxt, span), tree)
                  | chk (cxt, BT.ConDecl(conid, optTy)) = let
                      val optTy' = Option.map (fn ty => chkTy(cxt, ty)) optTy
                      val con' = Exn.new(conid, optTy')
                      in
                        ([AST.DConTopDec con'], C.insertDCon (cxt, conid, con'))
                      end
                in
                  chk (cxt, con)
                end
            | BT.ValueDecl valDcl => let
                val (valDcl', cxt') = ChkExp.checkValDecl (cxt, valDcl)
                fun chkMetas (AST.ValDecl(_, AST.TyScheme(_, ty), _)) = (
                      case TU.findMetas ty
                       of [] => ()
                        | mvs => (
                            warning (cxt, [
                                S "unresolved meta variables will be instantiated as `unit`"
                              ]);
                            List.app (TU.setMeta PrimTy.unitTy) mvs)
                      (* end case *))
                  | chkMetas _ = ()
                in
                  C.resolveOverloads cxt';
                  chkMetas valDcl';
                  ([AST.ValTopDec valDcl'], cxt')
                end
          (* end case *))

    and chkTopDcls (cxt, tops) : (AST.top_decl list * C.t) = let
          fun chk (top, (cxt, dcls)) = let
                val (dcls', cxt') = chkTopDcl (cxt, top)
                in
                  (cxt', List.revAppend(dcls', dcls))
                end
          val (cxt, tops') = List.foldl chk (cxt, []) tops
          in
            (List.rev tops', cxt)
          end

    and chkStrExp (cxt, strId, sign, BT.MarkStrExp{span, tree}) =
          chkStrExp (C.setSpan(cxt, span), strId, sign, tree)
      | chkStrExp (cxt, strId, sign, BT.IdStrExp qid) = (
          case ChkQualId.checkStrId(cxt, qid)
           of SOME(rhsId, modEnv) => let
                val strId' = StrId.new strId
                val cxt = C.insertStruct(cxt, strId, strId', modEnv)
                val dcl = AST.StructTopDec(strId', AST.IdStrExp rhsId)
                in
                  ([dcl], cxt)
                end
            | NONE => ([], cxt) (* the error was already reported! *)
          (* end case *))
      | chkStrExp (cxt, strId, sign, BT.DefStrExp tops) = let
          val cxt = C.structBegin cxt
          val (tops', cxt) = chkTopDcls (cxt, tops)
          val sign' = chkSign (cxt, sign)
          val (strId', strEnv, cxt) = C.structEnd (cxt, strId)
(* TODO: do something with the strEnv *)
          in
            ([AST.StructTopDec(strId', AST.DefStrExp(sign', tops'))], cxt)
          end
      | chkStrExp (cxt, _, _, BT.ErrorStrExp) = ([], cxt)

    and chkSign (C.Cxt{env, ...}, BT.Sign{strs, cons, vals, ...}) = let
          fun error (cxt, name) = raise Fail(concat[
                  "chkSign.", cxt, ": ", name, " is not bound"
                ])
          fun lookupStr id = (case Env.findStruct(env, id)
                 of SOME(strId, _) => strId
                  | NONE => error ("lookupStr", BT.StrId.nameOf id)
                (* end case *))
          fun lookupCon id = (case Env.findDCon(env, id)
                 of SOME conId => conId
                  | NONE => error ("lookupStr", BT.ConId.nameOf id)
                (* end case *))
          fun lookupVal id = (case Env.findVar(env, id)
                 of SOME(Env.Var valId) => valId
                  | _ => error ("lookupVal", BT.VarId.nameOf id)
                (* end case *))
          in
            AST.Sign{
                strs = List.map lookupStr strs,
                cons = List.map lookupCon cons,
                vals = List.map lookupVal vals
              }
          end

    fun check (errS, {span, tree}) = let
          val cxt = C.Cxt{
                  errS = errS, span = span,
                  env = Env.env0,
                  ovlds = Overloads.new()
                }
          in
            #1 (chkTopDcls (cxt, tree))
          end

  end
