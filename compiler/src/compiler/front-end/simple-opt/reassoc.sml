(* reassoc.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * An optimization pass that re-associates applications of data constructors (e.g., `::`)
 * to reduce the number of live variables.  For example, consider the sml expression
 *
 *      [(1,2), (2,3), (3,4)]
 *
 * This expression is represented as the following Simple AST term (annotated with the
 * live variables):
 *
 *      let
 *      val t1 = (1,2)          { t1 }
 *      val t4 = (2,3)          { t1, t4 }
 *      val t7 = (3,4)          { t1, t4, t7 }
 *      val t6 = (t7, nil)      { t1, t4, t6 }
 *      val t5 = :: t6          { t1, t4, t5 }
 *      val t3 = (t4, t5)       { t1, t3 }
 *      val t2 = :: t3          { t1, t2 }
 *      val t0 = (t1, t2)       { t0 }
 *      in
 *        :: t0
 *      end
 *
 * which has a maximum of three live variables, whereas if we reassociate the construction
 * of the list as follows, we can reduce the live-variable pressure:
 *
 *      let
 *      val t7 = (3,4)          { t7 }
 *      val t6 = (t7, nil)      { t6 }
 *      val t5 = :: t6          { t5 }
 *      val t4 = (2,3)          { t4 }
 *      val t3 = (t4, t5)       { t3 }
 *      val t2 = :: t3          { t2 }
 *      val t1 = (1,2)          { t1 }
 *      val t0 = (t1, t2)       { t0 }
 *      in
 *        :: t0
 *      end
 *
 * The algorithm is basically Sethi-Ullman register allocation [JACM; 1970] extended to
 * arbitrary arity operators (as described by Appel and Supowit [unpublished; 1986].
 *)

structure Reassoc : sig

    val transform : Census.t * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST

  (* `T(x, n, nd)` is the tree representation of a constructed term, where
   * `x` is the variable bound to the term, `n` is the number of live variables
   * required to build the term, and `nd` is the root of the term.
   *)
    datatype term = T of Var.t * int * node

    and node
      = LEAF of S.atom
      | TPL of term list
      | DCON of DataCon.t * Types.ty list * term

(*
    fun analalyze (S.FB(f, x, e)) = let
          fun analExp exp= (case exp
                 of S.E_Let(x, e1, e2) =>
                  | S.E_Fun(fbs, e) =>
                  | S.E_Apply(f, tys, arg) =>
                  | S.E_DConApp(dc, tys, arg) =>
                  | S.E_Prim(rator, args) =>
                  | S.E_Tuple args =>
                  | S.E_Select(i, x, tys) =>
                  | S.E_If(tst, args, e1, e2, ty) =>
                  | S.E_Case(arg, cases, ty) =>
                  | S.E_Handle(body, ex, hndlr, ty) =>
                  | S.E_Raise(loc, arg, ty) =>
                  | S.E_Atom atm =>
                (* end case *))

          fun xformFB (env, S.FB(f, x, e)) =
          and xformExp (env, exp) = (case exp
                 of S.E_Let(x, e1, e2) =>
                  | S.E_Fun(fbs, e) =>
                  | S.E_Apply(f, tys, arg) =>
                  | S.E_DConApp(dc, tys, arg) =>
                  | S.E_Prim(rator, args) =>
                  | S.E_Tuple args =>
                  | S.E_Select(i, x, tys) =>
                  | S.E_If(tst, args, e1, e2, ty) =>
                  | S.E_Case(arg, cases, ty) =>
                  | S.E_Handle(body, ex, hndlr, ty) =>
                  | S.E_Raise(loc, arg, ty) =>
                  | S.E_Atom atm =>
                (* end case *))

*)

    fun transform (info, S.CU lambda) = S.CU lambda

  end
