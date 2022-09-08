(* print-ast.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Pretty printer for AST representation
 *)

structure PrintAST : sig

    val output : TextIO.outstream * string * AST.comp_unit -> unit

  end = struct

    structure A = AST
    structure Ty = Types
    structure PP = TextIOPP

    fun isAtomicExp e = (case e
           of A.LetExp _ => true
            | A.IfExp _ => false
            | A.CaseExp _ => false
            | A.HandleExp _ => false
            | A.RaiseExp _ => false
            | A.FunExp _ => true        (* enclosed in "( )" *)
            | A.ApplyExp _ => false
            | A.TupleExp _ => true
            | A.ConstExp _ => true
            | A.SeqExp _ => false
            | A.VarExp _ => true
            | A.OverloadExp _ => true
          (* end case *))

    fun isApplyExp (A.ApplyExp _) = true
      | isApplyExp _ = false

    fun isTupleExp (A.TupleExp _) = true
      | isTupleExp _ = false

    fun isCaseExp (A.CaseExp _) = true
      | isCaseExp (A.HandleExp _) = true
      | isCaseExp _ = false

    fun pp (ppS, showTys, tops) = let
          val string = PP.string ppS
          fun nl () = PP.newline ppS
          fun sp () = PP.space ppS 1
          fun brk () = PP.break ppS {nsp=1, offset=0}
          fun ppType ty = string(TypeUtil.toString ty)
          fun ppTyScheme tyS = string(TypeUtil.schemeToString tyS)
          fun ppTyArgs [] = ()
            | ppTyArgs (ty1::tys) = if showTys
                then (
                  string "<";
                  ppType ty1;
                  List.app (fn ty => (string ","; ppType ty)) tys;
                  string ">")
                else ()
          fun ppConst c = (case c
                 of A.DConst(dc, tys) => (string(DataCon.nameOf dc); ppTyArgs tys)
                  | A.LConst(lit, _) => string(Literal.toString lit)
                (* end case *))
          fun ppVarBind x = (
                PP.openHBox ppS;
                  string(Var.toString x);
                  if showTys
                    then (sp(); string ":"; sp(); ppTyScheme(Var.typeOf x))
                    else ();
                PP.closeBox ppS)
          fun ppPat pat = (case pat
                 of A.VarPat x => ppVarBind x
                  | A.WildPat ty => (
                      PP.openHBox ppS;
                        string "_";
                        if showTys
                          then (sp(); string ":"; sp(); ppType ty)
                          else ();
                      PP.closeBox ppS)
                  | A.AsPat(x, p) => (
                      PP.openHBox ppS;
                        string(Var.toString x);
                        if showTys
                          then (sp(); string ":"; sp(); ppTyScheme(Var.typeOf x))
                          else ();
                        sp(); string "as"; sp(); ppPat p;
                      PP.closeBox ppS)
                  | A.ConstPat c => ppConst c
                  | A.ConPat(dc, tys, pat) => (
                      string(DataCon.nameOf dc);
                      ppTyArgs tys;
                      case pat
                       of A.ConPat _ => ppAtomicPat pat
                        | A.TuplePat _ => ppPat pat
                        | _ => (sp(); ppPat pat)
                      (* end case *))
                  | A.TuplePat[] => string "()"
                  | A.TuplePat(pat :: pats) => (
                      string "(";
                      ppPat pat;
                      List.app (fn p => (string ","; sp(); ppPat p)) pats;
                      string ")")
                (* end case *))
        (* print an atomic pattern, which means putting "( )" around non-atomic patterns *)
          and ppAtomicPat pat = (case pat
                 of A.VarPat _ => if showTys
                      then (string "("; ppPat pat; string ")")
                      else ppPat pat
                  | A.ConPat _ => (string "("; ppPat pat; string ")")
                  | _ => ppPat pat
                (* end case *))
          fun ppExp e = (case e
                 of A.LetExp _ => ppBindings e
                  | A.IfExp(e1, e2, e3, _) => let
                      fun ppIf (ppPrefix, e1, e2, e3) = (
                            PP.openHBox ppS;
                              ppPrefix(); string "if"; sp(); ppExp e1;
                            PP.closeBox ppS;
                            brk();
                            PP.openHBox ppS;
                              string "then"; sp(); ppExp e2;
                            PP.closeBox ppS;
                            brk();
                            ppElse e3)
                      and ppElse (A.IfExp(e1', e2', e3', _)) =
                            ppIf (fn () => (string "else"; sp()), e1', e2', e3')
                        | ppElse e = (
                            PP.openHBox ppS;
                              string "else"; sp(); ppExp e;
                            PP.closeBox ppS)
                      in
                        PP.openHOVBox ppS (PP.Abs 2);
                          ppIf (Fn.id, e1, e2, e3);
                        PP.closeBox ppS
                      end
                  | A.CaseExp(e, cases, _) => (
                      PP.openVBox ppS (PP.Abs 1);
                        PP.openHBox ppS;
                          string "case"; sp(); ppExp e;
                        PP.closeBox ppS;
                        ignore (List.foldl ppCase "of" cases);
                      PP.closeBox ppS)
                  | A.HandleExp(e, cases, _) => (
                      PP.openVBox ppS (PP.Abs 2);
                        PP.openHBox ppS;
                          ppExp e;
                        PP.closeBox ppS;
                        nl();
                        PP.openVBox ppS (PP.Abs 5);
                          ignore (List.foldl ppCase "handle" cases);
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | A.RaiseExp(_, e, _) => (
                      PP.openHBox ppS;
                        string "raise"; sp(); ppExp e;
                      PP.closeBox ppS)
                  | A.FunExp(x, body, _) => (
                      PP.openHBox ppS;
                        string "(fn"; sp(); string(Var.toString x); sp();
                        string "=>"; sp(); ppExp body; string ")";
                      PP.closeBox ppS)
                  | A.ApplyExp(e1, e2, _) => (
                      PP.openHOVBox ppS (PP.Abs 2);
                        ppAtomicExp e1;
                        if isTupleExp e2
                          then ppExp e2
                        else if isAtomicExp e2 orelse isApplyExp e2
                          then (brk(); ppExp e2)
                          else ppAtomicExp e2;
                      PP.closeBox ppS)
                  | A.TupleExp[] => string "()"
                  | A.TupleExp(e::es) => (
                      string "(";
                      ppExp e;
                      List.app (fn e => (string ","; sp(); ppExp e)) es;
                      string ")")
                  | A.ConstExp c => ppConst c
                  | A.SeqExp _ => let
                      fun pp (A.SeqExp(e1, e2)) = (
                            ppExp e1; string ";"; brk(); pp e2)
                        | pp e = ppExp e
                      in
                        PP.openHOVBox ppS (PP.Abs 0);
                          pp e;
                        PP.closeBox ppS
                      end
                  | A.VarExp(x, tyArgs) => (
                      PP.openHBox ppS;
                        string (Var.toString x);
                        ppTyArgs tyArgs;
                      PP.closeBox ppS)
                  | A.OverloadExp(ref(A.Unknown _)) => string "<overload>"
                  | A.OverloadExp(ref(A.Instance x)) => string (Var.toString x)
                (* end case *))
          and ppCase ((pat, e), prefix) = (
                nl();
                PP.openVBox ppS (PP.Abs 3);
                  PP.openHBox ppS;
                    string prefix; sp(); ppPat pat; sp(); string "=>"; sp();
                    if isCaseExp e then ppAtomicExp e else ppExp e;
                  PP.closeBox ppS;
                PP.closeBox ppS;
                " |")
          and ppAtomicExp e = if isAtomicExp e
                then ppExp e
                else (string "("; ppExp e; string ")")
          and ppBindings e = let
                fun ppBinds (A.LetExp(vdec, e)) = (
                      nl ();
                      ppValDecl vdec;
                      ppBinds e)
                  | ppBinds e = e
                in
                  PP.openVBox ppS (PP.Abs 0);
                    string "let";
                    let val body = ppBinds e
                    in
                      nl(); string "in";
                      PP.openVBox ppS (PP.Abs 2);
                        nl();
                        ppExp body;
                      PP.closeBox ppS;
                      nl();
                      string "end"
                    end;
                  PP.closeBox ppS
                end
          and ppValDecl (A.ValDecl(lhs, _, rhs)) = (
                PP.openHBox ppS;
                  string "val"; sp(); ppPat lhs; sp(); string "="; sp(); ppExp rhs;
                PP.closeBox ppS)
            | ppValDecl (A.FunDecl fbs) = let
                fun pp (prefix, (f, params, body)::fbs) = (
                      PP.openHOVBox ppS (PP.Abs 6);
                        PP.openHBox ppS;
                          string prefix;
                          if showTys
                            then (case Var.typeOf f
                               of Ty.TyScheme([], _) => ()
                                | Ty.TyScheme([tv], _) => (sp(); string(TyVar.toString tv))
                                | Ty.TyScheme(tv::tvr, _) => (
                                    sp(); string "("; string(TyVar.toString tv);
                                    List.app (fn tv => (string ","; string(TyVar.toString tv))) tvr;
                                    string ")")
                              (* end case *))
                            else ();
                          sp(); string(Var.toString f);
                          if Var.isJoin f then string "%JOIN" else (); sp();
                          List.app (fn x => (ppAtomicPat (A.VarPat x); sp())) params;
(* TODO: return type when showTys is true *)
                          string "=";
                        PP.closeBox ppS;
                        sp(); ppExp body;
                      PP.closeBox ppS;
                      nl();
                      pp ("and", fbs))
                  | pp (_, []) = ()
                in
                  pp ("fun", fbs)
                end
          fun ppTopDecl top = (case top
                 of A.StructTopDec(strid, strExp) => let
                      fun ppLHS () = (
                            string "structure"; sp(); string(StrId.toString strid);
                            sp(); string "="; sp())
                      in
                        nl();
                        case strExp
                         of A.IdStrExp strid' => (
                              PP.openHBox ppS;
                                ppLHS (); string(StrId.toString strid');
                              PP.closeBox ppS)
                          | A.DefStrExp(_, tops) => (
                              PP.openVBox ppS (PP.Abs 2);
                                PP.openHBox ppS;
                                  ppLHS(); string "struct";
                                PP.closeBox ppS;
                                PP.openVBox ppS (PP.Abs 2);
                                  List.app ppTopDecl tops;
                                PP.closeBox ppS;
                                nl(); string "end";
                              PP.closeBox ppS)
                        (* end case *)
                      end
                  | A.DConTopDec con => (
                      nl();
                      PP.openHBox ppS;
                        string "con"; sp(); string(DataCon.nameOf con);
                        sp(); string ":"; sp(); ppTyScheme(DataCon.typeOf con);
                      PP.closeBox ppS)
                  | A.ValTopDec vdec => (nl(); ppValDecl vdec)
                (* end case *))
          in
            List.app ppTopDecl tops
          end

    fun output (outS, msg, tops) = let
          val ppS = PP.openOut {dst = outS, wid = 90}
          in
            PP.openVBox ppS (PP.Abs 0);
              PP.string ppS (concat ["===== AST: ", msg, " ====="]); PP.newline ppS;
              pp (ppS, Controls.get Ctl.showASTTypes, tops);
              PP.newline ppS;
              PP.string ppS "====="; PP.newline ppS;
            PP.closeBox ppS;
            PP.closeStream ppS
          end

  end
