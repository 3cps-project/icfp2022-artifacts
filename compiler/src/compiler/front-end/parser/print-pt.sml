(* print-pt.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Functions to convert parse trees to strings.
 *)

structure PrintPT : sig

    val output : TextIO.outstream * string * ParseTree.comp_unit -> unit

end = struct

    structure PT = ParseTree
    structure Lit = Literal

    fun output (outS, msg, {span, tree}) = let
          fun pr s = TextIO.output(outS, s)
          fun prl s = pr(String.concat s)
          fun prIndent 0 = ()
            | prIndent n = (pr "  "; prIndent(n-1))
          fun indent i = prIndent i
          fun prList toS [] = ()
            | prList toS [x] = toS x
            | prList toS l = let
                fun prL [] = ()
                  | prL [x] = toS x
                  | prL (x::r) = (toS x; pr ","; prL r)
                in
                  prL l
                end
          fun prPList toS [] = pr "()"
            | prPList toS [x] = toS x
            | prPList toS l = let
                fun prL [] = ()
                  | prL [x] = toS x
                  | prL (x::r) = (toS x; pr ","; prL r)
                in
                  pr "("; prL l; pr ")"
                end
          fun prBList toS [] = pr "[]"
            | prBList toS [x] = toS x
            | prBList toS l = let
                fun prL [] = ()
                  | prL [x] = toS x
                  | prL (x::r) = (toS x; pr ","; prL r)
                in
                  pr "["; prL l; pr "]"
                end
          fun prId a = pr (Atom.toString a)
          fun prQId(prefix, id) = pr (String.concatWithMap "." Atom.toString (prefix @ [id]))
          fun prDecl (decl : PT.decl) = (case decl
                 of PT.MarkDecl{tree,...} => prDecl tree
                  | PT.StructDecl(mb, module) => (
                    pr "structure "; prId mb;
                    pr " = "; prStruct module; pr "\n")
                  | PT.LocalDecl (decls1, decls2) => (
                    pr "local\n"; List.app prDecl decls1;
                    pr "in\n"; List.app prDecl decls2;
                    pr "end\n")
                  | PT.TyDecl(tyvars, tyb, ty) => (
                    pr "type "; prId tyb; pr " "; prPList prId tyvars;
                    pr " : "; prTy ty; pr "\n")
                  | PT.DataDecl dts => let
                      fun prDt ({span, tree=(tyvars, name, cons)}, prefix) = (
                            pr prefix; pr " "; prId name;
                            pr " "; prPList prId tyvars; pr " ";
                            prPList (prConDecl "con") cons; pr "\n";
                            "and")
                    in
                      ignore (List.foldl prDt "datatype" dts)
                    end
                  | PT.ExnDecl con => prConDecl "exception" con
                  | PT.ValueDecl (vald) => prValDecl vald
                (* end case *))
          and prStruct module = (case module
                 of PT.MarkStrExp{tree,...} => prStruct tree
                  | PT.IdStrExp modid => (prQId modid; pr "\n")
                  | PT.DefStrExp (decls) => (
                      pr "struct\n"; List.app prDecl decls; pr "end")
                (* end case *))
          and prConDecl prefix con = (case con
               of PT.MarkConDecl {tree,...} => prConDecl prefix tree
                | PT.ConDecl (binder, tyOpt) => (
                  pr prefix; pr " "; prId binder;
                  case tyOpt
                   of SOME ty => (pr " of "; prTy ty)
                    | _ => ();
                  pr "\n"))
          and prValDecl vald = (case vald
                 of PT.MarkVDecl{tree,...} => prValDecl tree
                  | PT.ValVDecl(pat, exp) => (
                    pr "val "; prPat pat; pr " = ";
                    prExp exp; pr "\n")
                  | PT.FunVDecl funs => let
                      fun prFun (PT.MarkFunct{tree, ...}, prefix) = prFun(tree, prefix)
                        | prFun (PT.Funct clauses, prefix) = let
                            fun prFn ({tree=(name, pats, optTy, e), span}, prefix) = (
                                  pr prefix; pr " "; prId name; prPList prPat pats;
                                  case optTy
                                   of SOME ty => (pr " : "; prTy ty)
                                    | _ => ()
                                  (* end case *);
                                  pr " = \n"; prExp e; pr "\n";
                                  "  |")
                            in
                              ignore (List.foldl prFn prefix clauses);
                              "and"
                            end
                      in
                        ignore (List.foldl prFun "fun" funs)
                      end
                (* end case *))
          and prTy ty = (case ty
               of PT.MarkTy {tree,...} => prTy tree
                | PT.NamedTy([], name) => prQId name
                | PT.NamedTy(tys, name) => (
                    prPList prTy tys; pr " "; prQId name)
                | PT.VarTy tyvar => prId tyvar
                | PT.TupleTy tys => prPList prTy tys
                | PT.FunTy(argsTy, retTy) => (
                    prTy argsTy; pr " -> "; prTy retTy))
          and prExp exp = (case exp
                 of PT.MarkExp{tree,...} => prExp tree
                  | PT.LetExp (valdecls, exp) => (
                    pr "let\n";
                    List.app prValDecl valdecls;
                    pr "in\n";
                    prExp exp; pr "end\n")
                  | PT.IfExp (c, t, e) => (
                    pr "if "; prExp c; pr "\n";
                    pr "then "; prExp t; pr "\n";
                    pr "else "; prExp e; pr "\n")
                  | PT.FnExp matches => (
                      pr "fn "; prPList prMatch matches)
                  | PT.CaseExp (e, matches) => (
                    pr "case "; prExp e; pr "\n";
                    List.app prMatch matches)
                  | PT.HandleExp (exp, matches) => (
                    prExp exp; pr " handle "; prPList prMatch matches)
                  | PT.RaiseExp (exp) => (
                    pr "raise "; prExp exp)
                  | PT.AndAlsoExp (e1, e2) => (
                    prExp e1; pr " andalso "; prExp e2)
                  | PT.OrElseExp  (e1, e2) => (
                    prExp e1; pr " orelse "; prExp e2)
                  | PT.BinaryExp (e1, oper, e2) => (
                    prExp e1; pr " "; prId oper; pr " "; prExp e2)
                  | PT.ApplyExp (e1, e2) => (
                    prExp e1; pr "("; prExp e2; pr ")")
                  | PT.ConstExp const => prConst const
                  | PT.TupleExp exps => prPList prExp exps
                  | PT.ListExp exps => prBList prExp exps
                  | PT.SeqExp (exps) => prList prExp exps
                  | PT.IdExp v => prQId v
                  | PT.ConstraintExp(e, ty) => (prExp e; pr " : "; prTy ty)
                (* end case *))
          and prMatch match = (case match
               of PT.MarkMatch {tree,...} => prMatch tree
                | PT.CaseMatch (pat, exp) => (
                    pr "match "; prPat pat; pr " "; prExp exp))
          and prPat pat = (case pat
                 of PT.MarkPat {tree,...} => prPat tree
                  | PT.ConPat(con, pat) => (
                      prQId con; pr " "; prPat pat)
                  | PT.ConsPat(pat1, pat2) => (
                      prPat pat1; pr " :: "; prPat pat2)
                  | PT.TuplePat pats => prPList prPat pats
                  | PT.ListPat pats => prBList prPat pats
                  | PT.WildPat => pr "_"
                  | PT.IdPat var => prQId var
                  | PT.AsPat (p1, p2) => (pr "("; prPat p1; pr " as "; prPat p2; pr ")")
                  | PT.ConstPat (const) => (pr "("; prConst const; pr ")")
                  | PT.ConstraintPat (pat, ty) => (prPat pat; pr " : "; prTy ty)
                (* end case *))
          and prConst (Lit.Int ii) = pr (IntInf.toString ii)
            | prConst (Lit.Real f) = pr (FloatLit.toString f)
            | prConst (Lit.Char c) = prl ["#\"", Char.toString c, "\""]
            | prConst (Lit.String s) = prl ["\"", String.toString s, "\""]
          in
            prl ["===== Parse Tree: ", msg, " =====\n"];
            List.app prDecl tree;
            pr "\n"
          end

end
