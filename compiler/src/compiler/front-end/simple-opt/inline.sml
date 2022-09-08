(* inline.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Expansive inlining for Simple AST.
 *
 * Currently, we only inline those functions that are marked as "alwaysInline".
 *)

structure Inline : sig

    val transform : Census.t * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure Var = SimpleVar
    structure ST = Stats

  (* debug messages *)
    fun say msg = Log.msg("[S-INL] " :: msg)
    fun ctlSay msg = if Controls.get Ctl.debugSimpleOpt
          then say msg
          else ()
    val v2s = Var.toString
    fun tys2s tys = concat[
            "<", String.concatWithMap "," SimpleTypeUtil.toString tys, ">"
          ]

  (* counters for optimizations *)
    val cntrs = ST.Group.newWithPri SimpleOptStats.group ("inline", [5])
    local
      val newCntr = ST.Counter.new cntrs
    in
    val cntInline       = newCntr "beta"
    end (* local *)

  (* property to track function definitions for functions that should be inlined *)
    local
      val {setFn : Var.t * S.lambda -> unit, peekFn, clrFn, ...} =
            Var.newProp (fn _ => raise Fail "fun-def")
    in
    val recordDef = setFn
    val clrDef = clrFn
    val findDef = peekFn
    end (* local *)

  (* make a let binding with denesting support *)
    fun mkLet (x, S.E(lab, S.E_Let(y, e1, e2)), e3) =
          S.E(lab, S.E_Let(y, e1, mkLet(x, e2, e3)))
      | mkLet (x, S.E(lab, S.E_LetPoly(y, tvs, e1, e2)), e3) =
          S.E(lab, S.E_LetPoly(y, tvs, e1, mkLet(x, e2, e3)))
      | mkLet (x, S.E(lab, S.E_Fun(fbs, e1)), e2) =
          S.E(lab, S.E_Fun(fbs, mkLet(x, e1, e2)))
      | mkLet (x, e1, e2) = S.mkLet(x, e1, e2)

    fun transform (info, S.CU(S.FB(main, mainLab, mainParam, mainBody))) = let
          val decUse = Census.decUse info
          val decApp = Census.decApp info
          val inline = Beta.reduce info
          fun xform (exp as S.E(lab, e)) = (case e
                 of S.E_Let(x, e1, e2) => mkLet(x, xform e1, xform e2)
                  | S.E_LetPoly(x, tvs, e1, e2) =>
                      S.E(lab, S.E_LetPoly(x, tvs, xform e1, xform e2))
                  | S.E_Fun(fbs, e) => let
                      fun bindFB (fb as S.FB(f, _, _, _)) =
                            if Var.alwaysInline f then recordDef(f, fb) else ();
                      val _ = List.app bindFB fbs
                      fun xformFB (S.FB(f, lab, x, e)) = S.FB(f, lab, x, xform e)
                      val fbs' = List.map xformFB fbs
                      in
                        S.E(lab, S.E_Fun(fbs', xform e))
                          before List.app (fn (S.FB(f, _, _, _)) => clrDef f) fbs'
                      end
                  | S.E_Apply(f, tys, arg) => (case findDef f
                       of SOME fb => (
                            ctlSay [
                                "beta reduce ", Var.toString f, tys2s tys, " (",
                                SimpleASTUtil.atomToString arg, ")\n"
                              ];
                            ST.Counter.tick cntInline;
                            decUse f; decApp f;
                            inline (fb, tys, arg))
                        | NONE => exp
                      (* end case *))
                  | S.E_DConApp _ => exp
                  | S.E_Prim _ => exp
                  | S.E_Tuple _ => exp
                  | S.E_Select _ => exp
                  | S.E_If(p, args, e1, e2, ty) =>
                      S.E(lab, S.E_If(p, args, xform e1, xform e2, ty))
                  | S.E_Case(atm, rules, ty) => let
                      fun xformRule (S.RULE(lab, p, e)) = S.RULE(lab, p, xform e)
                      in
                        S.E(lab, S.E_Case(atm, List.map xformRule rules, ty))
                      end
                  | S.E_Handle(e1, x, e2, ty) =>
                      S.E(lab, S.E_Handle(xform e1, x, xform e2, ty))
                  | S.E_Raise _ => exp
                  | S.E_Atom _ => exp
                (* end case *))
          in
            ctlSay ["***** Inlining ******\n"];
            S.CU(S.FB(main, mainLab, mainParam, xform mainBody))
          end

  end
