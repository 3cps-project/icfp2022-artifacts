(* simple-free-vars.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Free-variable analysis for the SimpleAST.  The results of the analysis
 * are recorded as properties of the labels of lambdas.  Note that the
 * free variables of a lambda will not include its parameter or the function
 * identifiers bound in the "fun" binding.
 *)

structure SimpleFreeVars : sig

  (* compute and record the free variables of the lambdas in the program *)
    val analyze : SimpleAST.comp_unit -> unit

  (* return the free variables that were recorded for a lambda. *)
    val freeOf : Label.t -> SimpleVar.Set.set

  (* clear the recorded results of the analysis *)
    val clear : SimpleAST.comp_unit -> unit

  end = struct

    structure S = SimpleAST
    structure Set = SimpleVar.Set

  (* debug messages *)
    fun say msg = Log.msg("[S-FV] " :: msg)
    val v2s = SimpleVar.toString
    val debug = Ctl.debugSimpleFreeVars

  (* the property on labels for recording free-variable info *)
    val {peekFn : Label.t -> Set.set option, setFn, clrFn, ...} =
          Label.newProp (fn _ => raise Fail "no free vars for label")

    fun doExp (S.E(_, e), fvs) = (case e
           of S.E_Let(x, e1, e2) =>
                Set.subtract(doExp (e2, doExp (e1, fvs)), x)
            | S.E_LetPoly(x, _, e1, e2) =>
                Set.subtract(doExp (e2, doExp (e1, fvs)), x)
            | S.E_Fun(fbs, e) => let
              (* the set of function names bound here *)
                val fs = List.foldl
                      (fn (S.FB(f, _, _, _), s) => Set.add(s, f))
                        Set.empty fbs
              (* compute the union of the free-variables of each function body *)
                val fnFVs = let
                      fun doFB (S.FB(_, _, x, e), fvs) = Set.subtract (doExp(e, fvs), x)
                      in
                      (* we get the free vars of the lambdas and then remove any recursive
                       * references.
                       *)
                        Set.difference (List.foldl doFB Set.empty fbs, fs)
                      end
              (* record the free variables of the lambda *)
                fun record (S.FB(f, lab, _, _)) = setFn (lab, fnFVs)
                val _ = List.app record fbs
                in
                  if Controls.get debug
                    then say [
                        "FVs(fun ",
                        String.concatWithMap " and " (fn (S.FB(f, lab, _, _)) => v2s f ^ Label.toString lab) fbs,
                        ") = {", String.concatWithMap "," v2s (Set.toList fnFVs), "}\n"
                      ]
                    else ();
                (* now compute the free variables for the whole expression *)
                  Set.difference (doExp (e, Set.union (fnFVs, fvs)), fs)
                end
            | S.E_Apply(f, _, atm) => doAtom (atm, Set.add(fvs, f))
            | S.E_DConApp(_, _, atm) => doAtom (atm, fvs)
            | S.E_Prim(_, _, atms) => List.foldl doAtom fvs atms
            | S.E_Tuple atms => List.foldl doAtom fvs atms
            | S.E_Select(_, x, _) => Set.add(fvs, x)
            | S.E_If(_, atms, e1, e2, _) =>
                doExp (e2, doExp (e1, List.foldl doAtom fvs atms))
            | S.E_Case(atm, rules, _) => List.foldl doRule (doAtom (atm, fvs)) rules
            | S.E_Handle(e1, x, e2, _) => Set.subtract (doExp (e2, doExp (e1, fvs)), x)
            | S.E_Raise(_, arg, _) => doAtom(arg, fvs)
            | S.E_Atom atm => doAtom(atm, fvs)
          (* end case *))

    and doAtom (S.A_Var(x, _), fvs) = Set.add(fvs, x)
      | doAtom (_, fvs) = fvs

  (* analyze a case rule *)
    and doRule (S.RULE(_, p, e), fvs) = let
          val fvs = doExp (e, fvs)
          in
            case p
             of S.P_DConApp(_, _, x) => Set.subtract(fvs, x)
              | S.P_Var x => Set.subtract(fvs, x)
              | _ => fvs
            (* end case *)
          end

    fun analyze (S.CU(S.FB(_, _, _, e))) = ignore (doExp (e, Set.empty))

    fun freeOf (lab) = (case peekFn lab
           of SOME fvs => fvs
            | NONE => raise Fail("no free variables recorded for " ^ Label.toString lab)
          (* end case *))

    fun clear (S.CU(S.FB(_, _, _, e))) = let
          fun clrExp (S.E(_, e)) = (case e
                 of S.E_Let(x, e1, e2) => (clrExp e1; clrExp e2)
                  | S.E_LetPoly(x, _, e1, e2) => (clrExp e1; clrExp e2)
                  | S.E_Fun(fbs, e) => (
                      List.app (fn (S.FB(_, lab, _, _)) => clrFn lab) fbs; clrExp e)
                  | S.E_If(_, _, e1, e2, _) => (clrExp e1; clrExp e2)
                  | S.E_Case(_, rules, _) => List.app (fn (S.RULE(_, _, e)) => clrExp e) rules
                  | S.E_Handle(e1, _, e2, _) => (clrExp e1; clrExp e2)
                  | _ => ()
                (* end case *))
          in
            clrExp e
          end
  end
