(* var-analysis.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * A simple syntactic analysis to classify the extent of variables.  The rules are
 *
 *      1) a variable that is locally bound in a function and is not live across a
 *         function call is classified as a register variable.
 *
 *      2) a variable that is locally bound and is only used in the function in which
 *         it is bound, is classified as a stack variable.
 *
 *      3) all other variables are classified as heap variables.
 *
 * TODO: be smart about functions that serve as join points (e.g., introduced by pattern-match
 *       code generation) and loops.
 *)

structure VarAnalysis : sig

    val analyze : SimpleAST.comp_unit -> unit

  (* get a variable's extent *)
    val getExtent : SimpleVar.t -> Extent.t
  (* set a variable's extent *)
    val setExtent : SimpleVar.t * Extent.t -> unit

  end = struct

    structure S = SimpleAST
    structure V = SimpleVar
    structure VSet = V.Set
    structure Ex = Extent

    val debug = Ctl.debugVarAnalysis
    val say = Log.msg

(* DEBUG *)
    fun setToString set = String.concat [
            "{", String.concatWithMap "," V.toString (VSet.toList set), "}"
          ]
(* DEBUG *)

  (* property to track variable extents *)
    val {getFn = getExtent, setFn = setExtent, ...} = V.newProp (fn _ => Ex.HEAP)

  (* add a pattern-bound variable to a set *)
    fun addPatVar (S.P_DConApp(_, _, x), vs) = VSet.add(vs, x)
      | addPatVar (S.P_Var x, vs) = VSet.add(vs, x)
      | addPatVar (_, vs) = vs

    fun analFB (S.FB(f, _, x, body)) = let
        (* first pass constructs three sets of variables:
         *    `lbvs`    -- locally bound variables
         *    `fvs`     -- free variables
         *    `enclFVs` -- free variables of enclosed functions
         * The lbvs and fvs sets are disjoint, but the lbvs and enclFVs sets
         * may overlap.
         *)
          val (lbvs, fvs, enclFVs) = let
                fun analV (x, lbvs, fvs) =
                      if VSet.member(lbvs, x) then fvs else VSet.add(fvs, x)
                fun analA (S.A_Var(x, _), lbvs, fvs) = analV (x, lbvs, fvs)
                  | analA (_, _, fvs) = fvs
                fun analAtms (atms, lbvs, fvs) = List.foldl
                      (fn (atm, fvs) => analA(atm, lbvs, fvs))
                        fvs atms
                fun analE (S.E(_, e), lbvs, fvs, enclFVs) = (case e
                       of S.E_Let(x, e1, e2) => let
                            val (lbvs, fvs, enclFVs) = analE (e1, lbvs, fvs, enclFVs)
                            val lbvs = VSet.add(lbvs, x)
                            in
                              analE (e2, lbvs, fvs, enclFVs)
                            end
                        | S.E_LetPoly(x, _, e1, e2) => let
                            val (lbvs, fvs, enclFVs) = analE (e1, lbvs, fvs, enclFVs)
                            val lbvs = VSet.add(lbvs, x)
                            in
                              analE (e2, lbvs, fvs, enclFVs)
                            end
                        | S.E_Fun(fbs, e) => let
                          (* add the function IDs to the locally-bound variables *)
                            val lbvs = List.foldl
                                  (fn (S.FB(f, _, _, _), lbvs) => VSet.add(lbvs, f))
                                    lbvs fbs
                          (* analyze the function bindings and get their free variables *)
                            val enclFVs' = List.foldl
                                  (fn (fb, vs) => VSet.union(vs, analFB fb))
                                    VSet.empty fbs
                          (* extend the free-variable set for this function by adding the
                           * enclosed free variables that are not locally bound.
                           *)
                            val fvs = VSet.union(fvs, VSet.difference(enclFVs', lbvs))
                          (* add the enclosed free variables to the accumulator *)
                            val enclFVs = VSet.union(enclFVs, enclFVs')
                            in
                              analE (e, lbvs, fvs, enclFVs)
                            end
                        | S.E_Apply(f, _, atm) =>
                            (lbvs, analA(atm, lbvs, analV(f, lbvs, fvs)), enclFVs)
                        | S.E_DConApp(_, _, atm) =>
                            (lbvs, analA(atm, lbvs, fvs), enclFVs)
                        | S.E_Prim(_, _, atms) =>
                            (lbvs, analAtms(atms, lbvs, fvs), enclFVs)
                        | S.E_Tuple atms =>
                            (lbvs, analAtms(atms, lbvs, fvs), enclFVs)
                        | S.E_Select(_, x, _) =>
                            (lbvs, analV(x, lbvs, fvs), enclFVs)
                        | S.E_If(_, atms, e1, e2, _) => let
                            val fvs = analAtms(atms, lbvs, fvs)
                            val (lbvs, fvs, enclFVs) = analE (e1, lbvs, fvs, enclFVs)
                            val (lbvs, fvs, enclFVs) = analE (e2, lbvs, fvs, enclFVs)
                            in
                              (lbvs, fvs, enclFVs)
                            end
                        | S.E_Case(atm, rules, _) => let
                            fun analRule (S.RULE(_, pat, e), (lbvs, fvs, enclFVs)) =
                                  analE (e, addPatVar(pat, lbvs), fvs, enclFVs)
                            in
                              List.foldl analRule
                                (lbvs, analA(atm, lbvs, fvs), enclFVs) rules
                            end
                        | S.E_Handle(e, x, hndlr, _) => let
                            val (lbvs, fvs, enclFVs) = analE (e, lbvs, fvs, enclFVs)
                            val lbvs = VSet.add(lbvs, x)
                            in
                              analE (hndlr, lbvs, fvs, enclFVs)
                            end
                        | S.E_Raise(_, atm, _) => (lbvs, analA(atm, lbvs, fvs), enclFVs)
                        | S.E_Atom atm => (lbvs, analA(atm, lbvs, fvs), enclFVs)
                      (* end case *))
                in
                  analE (body, VSet.singleton x, VSet.empty, VSet.empty)
                end
        (* the variables in the set `lbvs \ enclFVs` can be stack allocated. *)
          val stackVars = VSet.difference (lbvs, enclFVs)
          val _ = VSet.app (fn x => setExtent(x, Ex.STK)) stackVars
        (* the second pass figures out which of the stack variables are eligible
         * to be register allocated.  We walk the code in execution order recording
         * the bound variables (`lbvs`) that do not occur in the enclFVS set that
         * was computed during Pass 1.  When we get to an application, we add the
         * `lbvs` set to the set of potential register variables (`prvs`).  When
         * we see an occurrence of a variable in `prvs`, we remove it from the set
         * (since there is an application between its binding and use).
         *)
          val regVars = let
                fun bindV (x, lbvs) = if VSet.member(enclFVs, x)
                      then lbvs
                       else VSet.add(lbvs, x)
                fun analV (x, prvs) = VSet.subtract(prvs, x)
                fun analA (S.A_Var(x, _), prvs) = analV(x, prvs)
                  | analA (_, prvs) = prvs
                fun analAtms (atms, prvs) = List.foldl analA prvs atms
              (* reset the local variables to empty and update the potential
               * register variables.  This function is called for applications,
               * so we return true for the `hasApp` flag.
               *)
                fun reset (lbvs, prvs) =
                      (VSet.empty, VSet.union (prvs, lbvs), true)
                fun analE (S.E(_, e), lbvs, prvs) = (case e
                       of S.E_Let(x, e1, e2) => let
                            val (lbvs, prvs, hasApp1) = analE (e1, lbvs, prvs)
                            val (lbvs, prvs, hasApp2) = analE (e2, bindV(x, lbvs), prvs)
                            in
                              (lbvs, prvs, hasApp1 orelse hasApp2)
                            end
                        | S.E_LetPoly(x, _, e1, e2) => let
                            val (lbvs, prvs, hasApp1) = analE (e1, lbvs, prvs)
                            val (lbvs, prvs, hasApp2) = analE (e2, bindV(x, lbvs), prvs)
                            in
                              (lbvs, prvs, hasApp1 orelse hasApp2)
                            end
                        | S.E_Fun(fbs, e) => let
                          (* add the function IDs to the locally-bound variables *)
                            val lbvs = List.foldl
                                  (fn (S.FB(f, _, _, _), lbvs) => bindV(f, lbvs))
                                    lbvs fbs
                            in
                              analE (e, lbvs, prvs)
                            end
                        | S.E_Apply(f, _, atm) => reset (lbvs, analA (atm, analV (f, prvs)))
                        | S.E_DConApp(_, _, atm) => (lbvs, analA (atm, prvs), false)
(* FIXME: if a primop can cause an exception to be raised, then we should treat it like a throw! *)
                        | S.E_Prim(_, _, atms) => (lbvs, analAtms (atms, prvs), false)
                        | S.E_Tuple atms => (lbvs, analAtms (atms, prvs), false)
                        | S.E_Select(_, x, _) => (lbvs, analV (x, prvs), false)
                        | S.E_If(_, atms, e1, e2, _) => let
                            val prvs = analAtms (atms, prvs)
                            val (lbvs1, prvs1, hasApp1) = analE (e1, lbvs, prvs)
                            val (lbvs2, prvs2, hasApp2) = analE (e2, lbvs, prvs)
                            val hasApp = hasApp1 orelse hasApp2
                          (* compute `lbvs` set for the case where there was an application
                           * in one of the arms.  In this case, the variables that were locally
                           * bound coming into the `if` need to be discarded, but the other
                           * variables that are locally bound coming out of the branches
                           * are candidates for register allocation, so we include them in
                           * the `lbvs` set.
                           *)
                            fun computeLBVs () = VSet.difference(VSet.union(lbvs1, lbvs2), lbvs)
                            val prvs = VSet.intersection(prvs1, prvs2)
                            in
                              case (hasApp1, hasApp2)
                               of (true, true) => (VSet.union(lbvs1, lbvs2), prvs, true)
                                | (false, true) => (computeLBVs(), prvs, true)
                                | (true, false) => (computeLBVs (), prvs, true)
                                | (false, false) =>
                                  (* no applications, so all locally bound variables are
                                   * preserved.
                                   *)
                                    (VSet.union(lbvs1, lbvs2), prvs, false)
                              (* end case *)
                            end
                        | S.E_Case(atm, rules, _) => let
                            val prvs = analA (atm, prvs)
                            fun analRule (S.RULE(_, pat, e), (lbvs, prvs, hasApp)) = let
                                  val (lbvs', prvs', hasApp') =
                                        analE (e, addPatVar(pat, lbvs), prvs)
                                  in (
                                    VSet.union(lbvs, lbvs'),
                                    VSet.intersection(prvs, prvs'),
                                    hasApp orelse hasApp'
                                  ) end
                            val (lbvs', prvs, hasApp) =
                                  List.foldl analRule (lbvs, prvs, false) rules
                            in
                              if hasApp
                                then (VSet.difference(lbvs, lbvs'), prvs, hasApp)
                                else (lbvs, prvs, hasApp)
                            end
                        | S.E_Handle(e, x, hndlr, _) => let
                            val (lbvs1, prvs1, hasApp1) = analE (e, lbvs, prvs)
                            val (lbvs2, prvs2, hasApp2) =
                                  analE (hndlr, VSet.empty, VSet.union(prvs, lbvs))
                            in (
                              VSet.union(lbvs1, lbvs2),
                              VSet.intersection(prvs1, prvs2),
                              hasApp1 orelse hasApp2
                            ) end
                        | S.E_Raise(_, atm, _) => reset (lbvs, analA(atm, prvs))
                        | S.E_Atom atm => (lbvs, analA(atm, prvs), false)
                      (* end case *))
                val (_, prvs, _) = analE (body, VSet.empty, VSet.empty)
                in
                  prvs
                end
          val _ = if Controls.get Ctl.debugVarAnalysis
                then (
                  say[V.toString f, ": lbvs = ", setToString lbvs, "\n"];
                  say[V.toString f, ": fvs = ", setToString fvs, "\n"];
                  say[V.toString f, ": enclFVs = ", setToString enclFVs, "\n"];
                  say[V.toString f, ": stkVars = ", setToString stackVars, "\n"];
                  say[V.toString f, ": regVars = ", setToString regVars, "\n"])
                else ()
          val _ = VSet.app (fn x => setExtent(x, Ex.REG)) regVars
          in
            if Controls.get debug
              then (
                say ["VarAnalysis: ", V.toString f, " (", V.toString x, ")\n"];
                say ["  fvs = {", String.concatWithMap "," V.toString (VSet.toList fvs), "}\n"];
                say [
                    "  locals = {",
                    String.concatWithMap ","
                      (fn x => V.toString x ^ Ex.suffix(getExtent x))
                        (VSet.toList lbvs),
                    "}\n"
                  ])
              else ();
          (* return the free variables of the function *)
            fvs
          end

    fun analyze (S.CU fb) = if Controls.get Ctl.varAnalysis
          then ignore (analFB fb)
          else ()

  end
