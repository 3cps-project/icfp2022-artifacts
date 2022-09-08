(* simple-ast-util.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure SimpleASTUtil : sig

    val unitTy : SimpleTypes.ty

    val typeOfAtom : SimpleAST.atom -> SimpleTypes.ty

    val atomToString : SimpleAST.atom -> string

    val patToString : SimpleAST.pat -> string

    val primToString : SimpleAST.prim_op -> string

  end = struct

    structure S = SimpleAST
    structure TyUtil = SimpleTypeUtil

    val unitTy = SimpleTypes.TupleTy[]

    fun typeOfAtom (S.A_Var(x, tys)) = TyUtil.applyScheme(SimpleVar.typeOf x, tys)
      | typeOfAtom (S.A_DCon(dc, tys)) = TyUtil.applyScheme(SimpleDataCon.typeOf dc, tys)
      | typeOfAtom (S.A_Lit(_, ty)) = ty
      | typeOfAtom S.A_Unit = unitTy

    fun atomToString (S.A_Var(x, [])) = SimpleVar.toString x
      | atomToString (S.A_Var(x, tys)) = concat[
            SimpleVar.toString x, "<", String.concatWithMap "," TyUtil.toString tys, ">"
          ]
      | atomToString (S.A_DCon(dc, [])) = SimpleDataCon.nameOf dc
      | atomToString (S.A_DCon(dc, tys)) = concat[
            SimpleDataCon.nameOf dc, "<", String.concatWithMap "," TyUtil.toString tys, ">"
          ]
      | atomToString (S.A_Lit(lit, _)) = Literal.toString lit
      | atomToString S.A_Unit = "()"

    fun patToString (S.P_DConApp(dc, _, x)) = concat[
            SimpleDataCon.toString dc, " ", SimpleVar.toString x
          ]
      | patToString (S.P_Var x) = SimpleVar.toString x
      | patToString (S.P_DCon(dc, _)) = SimpleDataCon.toString dc
      | patToString (S.P_Lit(lit, _)) = Literal.toString lit

    fun primToString (S.Pure rator) = PrimOp.Pure.toString rator
      | primToString (S.Arith rator) = PrimOp.Arith.toString rator
      | primToString (S.Getter rator) = PrimOp.Getter.toString rator
      | primToString (S.Setter rator) = PrimOp.Setter.toString rator

  end
