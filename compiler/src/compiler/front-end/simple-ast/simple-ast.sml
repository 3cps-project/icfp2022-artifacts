(* simple-ast.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Simplified AST.  All arguments are atoms (variables or constants) and patterns
 * have at most one level of data constructor.  Let-bindings of polymorphic
 * variables implicitly bind the type variables of the variable's type scheme.
 *)

structure SimpleAST =
  struct

    type var = SimpleVar.t
    type dcon = SimpleDataCon.t
    type ty = SimpleTypes.ty
    type tyvar = SimpleTyVar.t

    datatype atom
      = A_Var of var * ty list
      | A_DCon of dcon * ty list
      | A_Lit of Literal.t * ty
      | A_Unit                          (* perhaps we don't need this *)

    datatype prim_op
      = Pure of PrimOp.pure
      | Arith of PrimOp.arith
      | Getter of PrimOp.getter
      | Setter of PrimOp.setter

  (* a labeled expression *)
    datatype exp = E of Label.t * exp_rep

    and exp_rep
      = E_Let of var * exp * exp
      | E_LetPoly of var * tyvar list * exp * exp       (* rhs must be "value" *)
      | E_Fun of lambda list * exp
      | E_Apply of var * ty list * atom
      | E_DConApp of dcon * ty list * atom
      | E_Prim of prim_op * ty list * atom list
      | E_Tuple of atom list
      | E_Select of int * var * ty list
      | E_If of PrimOp.test * atom list * exp * exp * ty
      | E_Case of atom * rule list * ty
      | E_Handle of exp * var * exp * ty
      | E_Raise of Error.location * atom * ty
      | E_Atom of atom

  (* a function definition *)
    and lambda = FB of var * Label.t * var * exp

  (* a rule in a case expression *)
    and rule = RULE of Label.t * pat * exp

  (* simple patterns *)
    and pat
      = P_DConApp of dcon * ty list * var
      | P_Var of var
      | P_DCon of dcon * ty list
      | P_Lit of Literal.t * ty

  (* a compilation unit is represented as a function
   *
   *    fun f inputs = ...
   *
   * where `inputs` are the imported modules and the result of `f`
   * is a tuple representing its exported value bindings.
   *)
    datatype comp_unit = CU of lambda

  (* constructor functions for making labeled expressions; these also set
   * the binding labels for variables where necessary.
   *)
    local
      fun mkExp con arg = let val lab = Label.new() in E(lab, con arg) end
      fun mkBind con arg = let val lab = Label.new() in E(lab, con(lab, arg)) end
      fun var lab x = (SimpleVar.setBindingLabel(x, lab); x)
      fun pat lab p = (
            case p
             of P_DConApp(_, _, x) => SimpleVar.setBindingLabel(x, lab)
              | P_Var x => SimpleVar.setBindingLabel(x, lab)
              | _ => ()
            (* end case *);
            p)
    in
    val mkLet = mkBind (fn (lab, (x, e1, e2)) => E_Let(var lab x, e1, e2))
    val mkLetPoly =
          mkBind (fn (lab, (x, tvs, e1, e2)) => E_LetPoly(var lab x, tvs, e1, e2))
    val mkFun = mkBind (fn (lab, (fbs, e)) => (
          List.app (fn (FB(f, _, _, _)) => SimpleVar.setBindingLabel(f, lab)) fbs;
          E_Fun(fbs, e)))
    val mkApply = mkExp E_Apply
    val mkDConApp = mkExp E_DConApp
    val mkPrim = mkExp E_Prim
    val mkTuple = mkExp E_Tuple
    val mkSelect = mkExp E_Select
    val mkIf = mkExp E_If
    val mkCase = mkExp E_Case
    val mkHandle = mkExp E_Handle
    val mkRaise = mkExp E_Raise
    val mkAtom = mkExp E_Atom
  (* Note: we map the parameter `x` to the label of the lambda, but `f` will be
   * mapped to the label of the enclosing `E_Fun` expression.
   *)
    fun mkFB (f, x, e) = let val lab = Label.new()in FB(f, lab, var lab x, e) end
    fun mkRULE (p, e) = let val lab = Label.new() in RULE(lab, pat lab p, e) end
    end

  end
