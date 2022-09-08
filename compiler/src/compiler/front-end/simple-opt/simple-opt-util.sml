(* simple-opt-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Utility functions for the Simple AST Optimizer.
 *)

structure SimpleOptUtil : sig

  (* flatten out unnecessary block-nesting *)
    val denestFB : SimpleAST.lambda -> SimpleAST.lambda

  (* make a let binding with denesting support. *)
    val mkLet : SimpleVar.t * SimpleAST.exp * SimpleAST.exp -> SimpleAST.exp

  end = struct

    structure S = SimpleAST
    structure TyVar = SimpleTyVar
    structure Var = SimpleVar
    structure TyU = SimpleTypeUtil
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
      val newCntr = ST.Counter.new SimpleOptStats.group
    in
    val cntLetFloat     = newCntr "let-float"
    end (* local *)

    fun denest e = let
          fun doE (exp as S.E(lab, e), k) = (case e
                 of S.E_Let(x, e1, e2) => let
                      fun k' e'' = S.E(lab, S.E_Let(x, e'', doE(e2, k)))
                      in
                        doE (e1, k')
                      end
                  | S.E_LetPoly(x, tvs, e1, e2) =>
                      S.E(lab, S.E_LetPoly(x, tvs, e1, doE(e2, k)))
                  | S.E_Fun(fbs, e) => let
                      val fbs = List.map denestFB fbs
                      fun denestFB () = S.E(lab, S.E_Fun(fbs, doE(e, k)))
                      in
                        case fbs
                         of [(S.FB(f, _, _, _))] => if Var.isJoin f
                              then k (S.E(lab, S.E_Fun(fbs, denest e)))
                              else denestFB ()
                          | _ => denestFB ()
                      end
                  | S.E_If(tst, xs, e1, e2, ty) =>
                      k (S.E(lab, S.E_If(tst, xs, denest' e1, denest' e2, ty)))
                  | S.E_Case(x, rules, ty) =>
                      k (S.E(lab, S.E_Case(x, List.map doRule rules, ty)))
                  | S.E_Handle(e, ex, hdlr, ty) =>
                      k (S.E(lab, S.E_Handle(denest' e, ex, denest' hdlr, ty)))
                  | _ => k exp
                (* end case *))
          and doRule (S.RULE(lab, p, e)) = S.RULE(lab, p, denest' e)
          and denest' e = doE (e, fn e' => e')
          in
            denest' e
          end

    and denestFB (S.FB(f, lab, param, body)) = S.FB(f, lab, param, denest body)

  (* make a let binding with denesting support.  Note that we do not denest
   * functions that have been marked as "join" points, since that will break
   * CPS conversion.
   *)
    fun mkLet (x, S.E(lab, S.E_Let(y, e1, e2)), e3) = (
          ctlSay [
              "float `let ", v2s x, " = let ",
              v2s y, " = ... in ... end in ... end`\n"
            ];
          ST.Counter.tick cntLetFloat;
          S.E(lab, S.E_Let(y, e1, mkLet(x, e2, e3))))
      | mkLet (x, S.E(lab, S.E_LetPoly(y, tvs, e1, e2)), e3) = (
          ctlSay [
              "float `let ", v2s x, " = letpoly ",
              v2s y, " = ", tvs2s tvs, " ... in ... end in ... end`\n"
            ];
          ST.Counter.tick cntLetFloat;
          S.E(lab, S.E_LetPoly(y, tvs, e1, mkLet(x, e2, e3))))
      | mkLet (x, rhs as S.E(lab, S.E_Fun(fbs, e1)), e2) = let
          fun denest () = (
                ctlSay ["float `let ", v2s x, " = fun ... in ... end in ... end`\n"];
                ST.Counter.tick cntLetFloat;
                S.E(lab, S.E_Fun(fbs, S.mkLet(x, e1, e2))))
          in
            case fbs
             of [S.FB(f, _, _, _)] => if Var.isJoin f
                  then S.mkLet(x, rhs, e2)
                  else denest()
              | _ => denest()
            (* end case *)
          end
      | mkLet (x, e1, e2) = S.mkLet(x, e1, e2)

  end
