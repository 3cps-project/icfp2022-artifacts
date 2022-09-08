(* print-simple-ast.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * TODO: add printing of expression labels
 *)

structure PrintSimpleAST : sig

    val output : TextIO.outstream * string * SimpleAST.comp_unit -> unit

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure Var = SimpleVar
    structure TypeUtil = SimpleTypeUtil
    structure DataCon = SimpleDataCon
    structure PP = TextIOPP

    fun isLet (S.E(_, S.E_Let _)) = true
      | isLet (S.E(_, S.E_LetPoly _)) = true
      | isLet (S.E(_, S.E_Fun _)) = true
      | isLet _ = false

    fun isCaseExp (S.E(_, S.E_Case _)) = true
      | isCaseExp (S.E(_, S.E_Handle _)) = true
      | isCaseExp _ = false

    fun output (outS, msg, S.CU fb) = let
          val showTys = Controls.get Ctl.showSimpleTypes
          val ppS = PP.openOut {dst = outS, wid = 90}
          val string = PP.string ppS
          fun nl () = PP.newline ppS
          fun sp () = PP.space ppS 1
          fun brk () = PP.break ppS {nsp=1, offset=0}
          fun ppType ty = string (TypeUtil.toString ty)
          fun ppTyScheme tyS= string (TypeUtil.schemeToString tyS)
          fun ppVar x = string(Var.toString x)
          fun ppVarBind x = if showTys
                then (
                  PP.openHBox ppS;
                    string "("; ppVar x; sp(); string ":"; sp();
                    ppTyScheme(Var.typeOf x); string ")";
                  PP.closeBox ppS)
                else ppVar x
          fun ppTyArgs [] = ()
            | ppTyArgs (ty1::tys) = if showTys
                then (
                  string "<";
                  ppType ty1;
                  List.app (fn ty => (string ","; ppType ty)) tys;
                  string ">")
                else ()
          fun ppAtom atm = (case atm
                 of S.A_Var(x, tys) => (ppVar x; ppTyArgs tys)
                  | S.A_DCon(dc, tys) => (string(DataCon.nameOf dc); ppTyArgs tys)
                  | S.A_Lit(lit, _) => string(Literal.toString lit)
                  | S.A_Unit => string "()"
                (* end case *))
          fun ppPat pat = (case pat
                 of S.P_DConApp(dc, tys, x) => (
                      PP.openHBox ppS;
                        string(DataCon.nameOf dc); ppTyArgs tys; sp(); ppVarBind x;
                      PP.closeBox ppS)
                  | S.P_Var x => ppVarBind x
                  | S.P_DCon(dc, tys) => (string(DataCon.nameOf dc); ppTyArgs tys)
                  | S.P_Lit(lit, _) => string(Literal.toString lit)
                (* end case *))
          fun ppExp (exp as S.E(lab, e)) = (case e
                 of S.E_Let _ => ppBindings exp
                  | S.E_LetPoly _ => ppBindings exp
                  | S.E_Fun _ => ppBindings exp
                  | S.E_Apply(f, tys, arg) => (
                      PP.openHBox ppS;
                        ppVar f; ppTyArgs tys; sp(); ppAtom arg;
                      PP.closeBox ppS)
                  | S.E_DConApp(dc, tys, arg) => (
                      PP.openHBox ppS;
                        string(DataCon.nameOf dc); ppTyArgs tys; sp(); ppAtom arg;
                      PP.closeBox ppS)
                  | S.E_Prim(rator, tys, args) => (
                      PP.openHBox ppS;
                        string(SimpleASTUtil.primToString rator); ppTyArgs tys;
                        sp(); string "(";
                        case args
                         of [] => ()
                          | [atm] => ppAtom atm
                          | (atm::atms) => (
                              ppAtom atm;
                              List.app (fn atm => (string ","; ppAtom atm)) atms)
                        (* end case *);
                        string ")";
                      PP.closeBox ppS)
                  | S.E_Tuple[] => string "()"
                  | S.E_Tuple(atm::atms) => (
                      PP.openHBox ppS;
                        string "("; ppAtom atm;
                        List.app (fn atm => (string ","; ppAtom atm)) atms;
                        string ")";
                      PP.closeBox ppS)
                  | S.E_Select(n, x, tys) => (
                      PP.openHBox ppS;
                        string "#"; string(Int.toString n); sp();
                        ppVar x; ppTyArgs tys;
                      PP.closeBox ppS)
                  | S.E_If(tst, args, e1, e2, _) => let
                      fun ppIf (ppPrefix, tst, args, e1, e2) = (
                            PP.openHBox ppS;
                              ppPrefix(); string "if"; sp();
                              case (tst, args)
                               of (_, [atm]) => (string(PrimOp.Test.toString tst); sp(); ppAtom atm)
                                | (_, atm::atms) => (
                                    string(PrimOp.Test.toString tst);
                                    string "(";
                                    ppAtom atm;
                                    List.app (fn atm => (string ","; ppAtom atm)) atms;
                                    string ")")
                              (* end case *);
                            PP.closeBox ppS;
                            brk();
                            PP.openHBox ppS;
                              string "then"; sp(); ppExp e1;
                            PP.closeBox ppS;
                            brk();
                            ppElse e2)
                      and ppElse (S.E(lab, S.E_If(tst, args, e1, e2, _))) =
                            ppIf (fn () => (string "else"; sp()), tst, args, e1, e2)
                        | ppElse e = (
                            PP.openHBox ppS;
                              string "else"; sp(); ppExp e;
                            PP.closeBox ppS)
                      in
                        PP.openHOVBox ppS (PP.Abs 2);
                          ppIf (Fn.id, tst, args, e1, e2);
                        PP.closeBox ppS
                      end
                  | S.E_Case(atm, rules, _) => let
                      fun ppRule (S.RULE(_, pat, e), prefix) = (
                            nl();
                            PP.openHBox ppS;
                              string prefix; sp(); ppPat pat; sp(); string "=>"; sp();
                              PP.openHOVBox ppS (PP.Abs 4);
                                if isCaseExp e
                                  then (string "("; ppExp e; string ")")
                                  else ppExp e;
                              PP.closeBox ppS;
                            PP.closeBox ppS;
                            " |")
                      in
                        PP.openVBox ppS (PP.Abs 1);
                          PP.openHBox ppS;
                            string "case"; sp(); ppAtom atm;
                          PP.closeBox ppS;
                          ignore (List.foldl ppRule "of" rules);
                        PP.closeBox ppS
                      end
                  | S.E_Handle(e, ex, hdlr, _) => (
                      PP.openVBox ppS (PP.Abs 2);
                        PP.openHBox ppS;
                          ppExp e;
                        PP.closeBox ppS;
                        nl();
                        PP.openVBox ppS (PP.Abs 2);
                          PP.openHBox ppS;
                            string "handle"; sp(); ppVar ex;
                            sp(); string "=>"; sp(); ppExp hdlr;
                          PP.closeBox ppS;
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | S.E_Raise(_, atm, _) => (
                      PP.openHBox ppS;
                        string "raise"; sp(); ppAtom atm;
                      PP.closeBox ppS)
                  | S.E_Atom atm => ppAtom atm
                (* end case *))
          and ppBindings e = let
                fun ppValBind (lhs, tvs, rhs, e) = (
                      if isLet rhs
                        then (
                          PP.openHOVBox ppS (PP.Abs 6);
                            PP.openHBox ppS;
                              string "val"; sp();
                              case tvs
                               of NONE => ()
                                | SOME tvs => (
                                    string "<";
                                    string (String.concatWithMap "," TyVar.toString tvs);
                                    string ">"; sp())
                              (* end case *);
                              ppVarBind lhs;
                              sp(); string "="; sp(); string "let";
                            PP.closeBox ppS;
                            ppLet (false, rhs);
                          PP.closeBox ppS)
                        else (
                          PP.openHBox ppS;
                            string "val"; sp();
                            case tvs
                             of NONE => ()
                              | SOME tvs => (
                                  string "<";
                                  string (String.concatWithMap "," TyVar.toString tvs);
                                  string ">"; sp())
                            (* end case *);
                            ppVarBind lhs;
                            sp(); string "=";
                            sp(); ppExp rhs;
                          PP.closeBox ppS);
                      nl();
                      ppBinds e)
                and ppBinds (S.E(lab, S.E_Let(lhs, rhs, e))) =
                      ppValBind(lhs, NONE, rhs, e)
                  | ppBinds (S.E(lab, S.E_LetPoly(lhs, tvs, rhs, e))) =
                      ppValBind(lhs, SOME tvs, rhs, e)
                  | ppBinds (S.E(lab, S.E_Fun(fbs, e))) = let
                      fun pp (prefix, fb::fbs) = (
                            ppFB (prefix, fb);
                            nl();
                            pp ("and", fbs))
                        | pp (_, []) = ppBinds e
                      in
                        pp ("fun", fbs)
                      end
                  | ppBinds e = e
                and ppLet (needLet, e) = (
                      PP.openVBox ppS (PP.Abs 0);
                        if needLet then string "let" else (); nl();
                        let val body = ppBinds e
                        in
                          string "in";
                          PP.openVBox ppS (PP.Abs 2);
                            nl();
                            ppExp body;
                          PP.closeBox ppS;
                          nl();
                          string "end"
                        end;
                      PP.closeBox ppS)
                in
                  ppLet (true, e)
                end
          and ppFB (prefix, S.FB(f, _, param, body)) = (
                PP.openHOVBox ppS (PP.Abs 6);
                  PP.openHBox ppS;
                    string prefix; sp();
                    case Var.typeOf f
                     of Ty.TyScheme([], _) => ()
                      | Ty.TyScheme(tvs, _) => (
                          string "<";
                          string(String.concatWithMap "," TyVar.toString tvs);
                          string ">"; sp())
                    (* end case *);
                    ppVar f;
                    if Var.isJoin f then string "%JOIN" else ();
                    if Var.alwaysInline f then string "%INL" else ();
                    sp();
                    ppVarBind param; sp(); string "=";
                  PP.closeBox ppS;
                  sp(); ppExp body;
                PP.closeBox ppS)
          in
            PP.openVBox ppS (PP.Abs 0);
              string (concat ["===== Simple AST: ", msg, " ====="]);
              nl(); ppFB ("fun", fb);
              nl(); string "====="; nl();
            PP.closeBox ppS;
            PP.closeStream ppS
          end

  end
