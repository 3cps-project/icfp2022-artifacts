(* fix-fix.sml
 *
 * COPYRIGHT (c) 2022 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * This pass fixes up the recursive function bindings so that functions are
 * defined in the same binding group only when they are mutually recursive.
 * Specifically, a group of functions `f1`, `f2`, ..., `fn` are mutually recursive
 * iff the directed graph formed by edges from use occurrences to functions
 * in the bodies of `f1`, `f2`, ..., `fn` form a connected component.
 *)

structure FixFix : sig

    val transform : SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure L = Label
    structure V = SimpleVar
    structure VSet = V.Set
    structure ST = Stats

  (* debug messages (DEBUG) *)
    fun say msg = Log.msg("[S-FF] " :: msg)
    val v2s = V.toString

  (* counters for optimizations *)
    val cntrs = ST.Group.newWithPri SimpleOptStats.group ("fix-fix", [3,5])
    local
      val newCntr = ST.Counter.new cntrs
    in
    val cntRecGrp       = newCntr "group"
    val cntSplit        = newCntr "split"
    end (* local *)

  (***** Analysis *****
   *
   * The analysis phase walks the program and adds a node for each function that is
   * currently in an `E_Fun` with two, or more, lambdas.
   *)

    structure Nd =
      struct
        (* `FN(f, succs)` represents the function `f` and the other recursive functions
         * that it mentions.
         *)
        datatype t = FN of V.t * t list ref
        type ord_key = t
        (* create a new node *)
        fun new f = FN(f, ref[])
        (* return the successors of a node *)
        fun follow (FN(_, succs)) = !succs
        (* add an edge between nodes *)
        fun addEdge (FN(_, succs), nd as FN(g, _)) = succs := nd :: !succs
        fun compare (FN(f, _), FN(g, _)) = V.compare(f, g)
      end

    structure SCC = GraphSCCFn (Nd)

    (* convert a node to a string (DEBUG) *)
    fun nd2s (Nd.FN(f, _)) = V.toString f

    (* convert a component to a string (DEBUG) *)
    fun comp2s (SCC.SIMPLE nd) = concat ["{", nd2s nd, "}"]
      | comp2s (SCC.RECURSIVE nds) = concat [
            "{", String.concatWithMap "," nd2s nds, "}"
          ]

    (* property to track the components of an E_Fun binding, when there are more
     * than one.
     *)
    val {peekFn=peekSCCs, setFn=setSCCs : L.t * SCC.component list -> unit, clrFn=clrSCCs, ...} =
          L.newProp (fn _ => raise Fail "uninitialized SCC property")

  (* analyse the program body for `E_Fun` bindings that should be split into multiple
   * binding groups.  Return `true` if such bindings exist and `false` otherwise.
   *)
    fun analyze e = let
          val anySplits = ref false
          fun analVar (inside, x) = if VSet.member(inside, x)
                then VSet.singleton x
                else VSet.empty
          fun analAtm (inside, S.A_Var(x, _)) = analVar (inside, x)
            | analAtm _ = VSet.empty
          fun analAtms (inside, atms) = let
                fun anal (S.A_Var(x, _), fvs) = if VSet.member(inside, x)
                      then VSet.add (fvs, x)
                      else fvs
                  | anal (_, fvs) = fvs
                in
                  List.foldl anal VSet.empty atms
                end
  (* `analE (inside, exp)` takes a set of the `E_Fun` bound variables that `exp` is nested
   * under and returns the subset of them that are referenced in `exp` (i.e., are free in
   * `exp`).  At `E_Fun` nodes that bind more than one function, we construct a reference
   * graph where each bound function `f` has has a node `nd_f` and if a function `g` that
   * is in the `E_Fun` group references another function `f` in the same group, then there
   * is an edge from `nd_g` to `nd_f`.  We compute the SCC for this graph and mark it
   * for splitting if there is more than one component.
   *)
          fun analE (inside, S.E(lab, e)) = (case e
                 of S.E_Let(_, e1, e2) => VSet.union(analE(inside, e1), analE(inside, e2))
                  | S.E_LetPoly(_, _, e1, e2) => VSet.union(analE(inside, e1), analE(inside, e2))
                  | S.E_Fun(fbs, e) => VSet.union(analFunBind(lab, inside, fbs), analE(inside, e))
                  | S.E_Apply(f, _, atm) => VSet.union(analVar(inside, f), analAtm(inside, atm))
                  | S.E_DConApp(_, _, atm) => analAtm(inside, atm)
                  | S.E_Prim _ => VSet.empty (* no primops work on function values *)
                  | S.E_Tuple atms => analAtms (inside, atms)
                  | S.E_Select _ => VSet.empty (* cannot select from a function *)
                  | S.E_If(_, _, e1, e2, _) => VSet.union(analE(inside, e1), analE(inside, e2))
                  | S.E_Case(_, rules, _) => let
                      fun analRule (S.RULE(_, _, e), fvs) = VSet.union(fvs, analE(inside, e))
                      in
                        List.foldl analRule VSet.empty rules
                      end
                  | S.E_Handle(e1, _, e2, _) => VSet.union(analE(inside, e1), analE(inside, e2))
                  | S.E_Raise _ => VSet.empty (* exceptions are not functions *)
                  | S.E_Atom atm => analAtm (inside, atm)
                (* end case *))
          and analFunBind (_, inside, [S.FB(_, _, _, e)]) = analE(inside, e)
            | analFunBind (lab, inside, fbs) = let
                val fns = List.map (fn (S.FB(f, _, _, _)) => f) fbs
                (* add this group of functions to the inside set for processing the function
                 * bodies.
                 *)
                val grp = List.foldl VSet.add' VSet.empty fns
                val inside' = VSet.union(inside, grp)
                (* create a list of nodes for the group *)
                val nds = List.map Nd.new fns
                (* construct the graph by analyzing each function body and adding edges from
                 * the corresponding node to the nodes belonging to the other functions in
                 * the group.  We also compute the union of the free function references,
                 * which gets passed up as the result of `analFunBind`.
                 *)
                fun doFB (S.FB(f, _, _, e), nd_f, allFVs) = let
                      val fvs = analE (inside', e)
                      fun maybeAddEdge (nd_g as Nd.FN(g, _))  =
                            if V.same(f, g) orelse not(VSet.member(fvs, g))
                              then () (* no edge from f to g *)
                              else Nd.addEdge (nd_f, nd_g)
                      in
                        List.app maybeAddEdge nds;
                        VSet.union (allFVs, fvs)
                      end
                val allFVs = ListPair.foldl doFB VSet.empty (fbs, nds)
                (* compute the components of the graph *)
                val components = SCC.topOrder' {roots = nds, follow = Nd.follow}
                in
                  ST.Counter.tick cntRecGrp;
                  case components
                   of [comp] => (* only one component, so no splitting required *)
                        if Controls.get Ctl.debugFixFix
                          then say [
                              "no split: ", comp2s comp, "\n"
                            ]
                          else ()
                    | comps => (
                        if Controls.get Ctl.debugFixFix
                          then say [
                              "split: ", String.concatWithMap "; " comp2s (List.rev comps), "\n"
                            ]
                          else ();
                        anySplits := true;
                        ST.Counter.tick cntSplit;
                        setSCCs (lab, comps))
                  (* end case *);
                  VSet.difference (allFVs, grp)
                end
          in
            analE (VSet.empty, e);
            !anySplits
          end

  (* walk the program body and split any `E_Fun` bindings that require splitting; we also
   * clear the "SCC" property on the associated labels.
   *)
    fun split (exp as S.E(lab, e)) = let
          fun mkE e = S.E(lab, e)
          in
            case e
             of S.E_Let(lhs, e1, e2) => mkE(S.E_Let(lhs, split e1, split e2))
              | S.E_LetPoly(lhs, tvs, e1, e2) => mkE(S.E_LetPoly(lhs, tvs, split e1, split e2))
              | S.E_Fun(fbs, e) => let
                  fun splitFB (S.FB(f, lab, x, e)) = S.FB(f, lab, x, split e)
                  val e' = split e
                  in
                    case List.map splitFB fbs
                     of [fb'] => mkE(S.E_Fun([fb'], e'))
                      | fbs' => (case peekSCCs lab
                           of SOME comps => let
                              (* map a node to its corresponding lambda *)
                                fun ndToFB (Nd.FN(f, _)) = (
                                      case List.find (fn (S.FB(g, _, _, _)) => V.same(f, g)) fbs'
                                       of SOME fb' => fb'
                                        | NONE => raise Fail "impossible: missing lambda"
                                      (* end case *))
                              (* each component corresponds to an E_Fun binding
                               * in inner-to-outer nesting-order.
                               *)
                                fun doComp (SCC.SIMPLE nd, e) = S.mkFun([ndToFB nd], e)
                                  | doComp (SCC.RECURSIVE nds, e) = S.mkFun(List.map ndToFB nds, e)
                                in
                                  clrSCCs lab; (* clear the property, since we are done with it *)
                                  List.foldl doComp e' comps
                                end
                            | NONE => mkE(S.E_Fun(fbs', e'))
                          (* end case *))
                    (* end case *)
                  end
              | S.E_If(tst, args, e1, e2, ty) => mkE(S.E_If(tst, args, split e1, split e2, ty))
              | S.E_Case(arg, rules, ty) => let
                  fun splitRule (S.RULE(lab, p, e)) = S.RULE(lab, p, split e)
                  in
                    mkE(S.E_Case(arg, List.map splitRule rules, ty))
                  end
              | S.E_Handle(e1, x, e2, ty) => mkE(S.E_Handle(split e1, x, split e2, ty))
              | _ => exp
            (* end case *)
          end

    fun transform (cu as S.CU(S.FB(main, lab, param, body))) =
          if analyze body
            then S.CU(S.FB(main, lab, param, split body))
            else cu

  end
