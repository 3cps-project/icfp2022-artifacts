(* ast-util.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ASTUtil : sig

  (* smart tuple constructors *)
    val tuplePat : AST.pat list -> AST.pat
    val tupleExp : AST.exp list -> AST.exp

  (* is an epression a syntactic value? *)
    val isValue : AST.exp -> bool

  (* is a pattern a variable or wild card? *)
    val isVarPat : AST.pat -> bool

    exception Empty

  (* compute the intersection of two patterns.  This function raises
   * the Empty exception when the intersection is empty.
   *)
    val patIntersect : AST.pat * AST.pat -> AST.pat

  (* are two patterns compatible, which means that they have a non-empty
   * intersection.
   *)
    val compatiblePats : AST.pat * AST.pat -> bool

    val typeOfExp : AST.exp -> Types.ty

    val typeOfPat : AST.pat -> Types.ty

    val typeOfConst : AST.const -> Types.ty

    val sameConst : AST.const * AST.const -> bool

  (* convert to strings for debugging *)
    val constToString : AST.const -> string
    val patToString : AST.pat -> string
    val expToString : AST.exp -> string

  (* print a pattern matrix *)
    val prPatMatrix : TextIO.outstream * AST.pat list list -> unit

    structure ConstSet : ORD_SET where type Key.ord_key = AST.const

  end = struct

    structure A = AST
    structure Ty = Types
    structure L = Literal

    fun tys2s [] = ""
      | tys2s tys = concat ["<", String.concatWithMap "," TypeUtil.toString tys, ">"]

    fun constToString (A.DConst(dc, tys)) = DataCon.nameOf dc ^ tys2s tys
      | constToString (A.LConst(lit, _)) = Literal.toString lit

    fun patToString p = (case p
           of A.VarPat x => Var.toString x
            | A.WildPat _ => "_"
            | A.ConstPat c => constToString c
            | A.ConPat(dc, tys, p as A.ConPat _) => concat [
                  DataCon.nameOf dc, tys2s tys, "(", patToString p, ")"
                ]
            | A.ConPat(dc, tys, p as A.TuplePat _) => concat[
                  DataCon.nameOf dc, tys2s tys, patToString p
                ]
            | A.ConPat(dc, tys, p) => concat[
                  DataCon.nameOf dc, tys2s tys, " ", patToString p
                ]
            | A.TuplePat ps => concat[
                  "(", String.concatWithMap "," patToString ps, ")"
                ]
            | A.AsPat(x, p) => concat[
                  "(", Var.toString x, " as ", patToString p, ")"
                ]
          (* end case *))

    fun expToString e = (case e
           of A.LetExp(A.ValDecl(p, _, e1), e2) => concat[
                  "let val ", patToString p, " = ... in ..."
                ]
            | A.LetExp(A.FunDecl _, _) => "let fun ..."
            | A.IfExp(e1, _, _, _) => concat[
                  "if ", expToString e1, " then ... else ..."
                ]
            | A.CaseExp(e1, cases, _) => concat[
                  "case ", expToString e1, " of ..."
                ]
            | A.HandleExp(e1, cases, _) => "<handle>"
            | A.RaiseExp(_, e, _) => "<raise>"
            | A.FunExp(x, e, _) => "<fn>"
            | A.ApplyExp(e1, e2 as A.TupleExp _, _) => concat [
                  expToString e1, " ", expToString e2
                ]
            | A.ApplyExp(e1, e2, _) => concat [
                  expToString e1, " (", expToString e2, ")"
                ]
            | A.TupleExp es => concat [
                  "(", String.concatWithMap "," expToString es, ")"
                ]
            | A.ConstExp c => constToString c
            | A.SeqExp(e1, e2) => "<seq>"
            | A.VarExp(x, tys) => Var.toString x ^ tys2s tys
            | A.OverloadExp(ref(A.Instance x)) => Var.toString x
            | A.OverloadExp _ => "<overload>"
          (* end case *))

    val unitTy = Ty.ConTy([], TyCon.unitTyc)

    fun tuplePat [p] = p
      | tuplePat ps = AST.TuplePat ps

    fun tupleExp [e] = e
      | tupleExp es = AST.TupleExp es

    fun isValue (A.FunExp _) = true
      | isValue (A.TupleExp es) = List.all isValue es
      | isValue (A.ApplyExp(A.ConstExp _, arg, _)) = isValue arg
      | isValue (A.ConstExp _) = true
      | isValue (A.VarExp _) = true
      | isValue _ = false

    fun isVarPat (A.VarPat _) = true
      | isVarPat (A.WildPat _) = true
      | isVarPat _ = false

    exception Empty

    fun patIntersect (p1, p2) = (case (p1, p2)
           of (A.WildPat _, _) => p2
            | (_, A.WildPat _) => p1
            | (A.VarPat _, _) => p2
            | (_, A.VarPat _) => p1
            | (A.ConstPat(A.DConst(dc1, _)), A.ConstPat(A.DConst(dc2, _))) =>
                if DataCon.same(dc1, dc2) then p1 else raise Empty
            | (A.ConstPat(A.LConst(lit1, _)), A.ConstPat(A.LConst(lit2, _))) =>
                if Literal.same(lit1, lit2) then p1 else raise Empty
            | (A.ConPat(dc1, tys, p1), A.ConPat(dc2, _, p2)) =>
                if DataCon.same(dc1, dc2)
                  then A.ConPat(dc1, tys, patIntersect(p1, p2))
                  else raise Empty
            | (A.TuplePat ps1, A.TuplePat ps2) =>
                A.TuplePat(ListPair.mapEq patIntersect (ps1, ps2))
            | (A.AsPat(_, p1), p2) => patIntersect(p1, p2)
            | (p1, A.AsPat(_, p2)) => patIntersect(p1, p2)
            | _ => raise Empty
          (* end case *))

  (* are two patterns compatible (i.e., does there exist a value that they both match)? *)
    fun compatiblePats (A.VarPat _, _) = true
      | compatiblePats (_, A.VarPat _) = true
      | compatiblePats (A.WildPat _, _) = true
      | compatiblePats (_, A.WildPat _) = true
      | compatiblePats (A.TuplePat pats1, A.TuplePat pats2) =
          ListPair.allEq compatiblePats (pats1, pats2)
      | compatiblePats (A.ConstPat(A.DConst(dc1, _)), A.ConstPat(A.DConst(dc2, _))) =
          DataCon.same(dc1, dc2)
      | compatiblePats (A.ConstPat(A.LConst(lit1, _)), A.ConstPat(A.LConst(lit2, _))) =
          Literal.same(lit1, lit2)
      | compatiblePats (A.ConPat(dc1, _, p1), A.ConPat(dc2, _, p2)) =
          DataCon.same(dc1, dc2) andalso compatiblePats (p1, p2)
      | compatiblePats (A.AsPat(_, p1), p2) = compatiblePats(p1, p2)
      | compatiblePats (p1, A.AsPat(_, p2)) = compatiblePats(p1, p2)
      | compatiblePats _ = false

    fun typeOfConst c = (case c
           of A.DConst(dc, tys) => TypeUtil.applyScheme(DataCon.typeOf dc, tys)
            | A.LConst(_, ty) => ty
          (* end case *))

    fun typeOfPat p = (case p
           of A.VarPat x => Var.monoTypeOf x
            | A.WildPat ty => ty
            | A.ConstPat c => typeOfConst c
            | A.ConPat(dc, tys, p) => (case TypeUtil.applyScheme(DataCon.typeOf dc, tys)
                 of Ty.FunTy(_, ty) => ty
                  | _ => raise Fail "expected function type"
                (* end case *))
            | A.TuplePat[] => unitTy
            | A.TuplePat ps => Ty.TupleTy(List.map typeOfPat ps)
            | A.AsPat(x, _) => Var.monoTypeOf x
          (* end case *))
    val typeOfPat = fn p => TypeUtil.prune(typeOfPat p)

    fun typeOfExp exp = (case exp
           of A.LetExp(_, e) => typeOfExp e
            | A.IfExp(_, _, _, ty) => ty
            | A.CaseExp(_, _, ty) => ty
            | A.HandleExp(_, _, ty) => ty
            | A.RaiseExp(_, _, ty) => ty
            | A.FunExp(x, _, ty) => Ty.FunTy(Var.monoTypeOf x, ty)
            | A.ApplyExp(_, _, ty) => ty
            | A.TupleExp[] => unitTy
            | A.TupleExp es => Ty.TupleTy(List.map typeOfExp es)
            | A.ConstExp c => typeOfConst c
            | A.SeqExp(_, e) => typeOfExp e
            | A.VarExp(x, []) => let
              (* because recursive instances of polymorphic functions do not have
               * the necessary type arguments in the AST, we just return the type,
               * instead of applying the scheme.
               *)
                val Ty.TyScheme(_, ty) = Var.typeOf x
                in
                  ty
                end
            | A.VarExp(x, tys) => TypeUtil.applyScheme(Var.typeOf x, tys)
            | A.OverloadExp(ref(A.Unknown(ty, _))) => ty
            | A.OverloadExp(ref(A.Instance x)) => Var.monoTypeOf x
          (* end case *))
    val typeOfExp = fn e => TypeUtil.prune(typeOfExp e)

    fun prPatMatrix (outS, []) = TextIO.output(outS, "<empty-matrix>\n")
      | prPatMatrix (outS, pmat as row::_) = let
          fun pr s = TextIO.output(outS, s)
          val ncols = List.length row
          val wids = Array.array(ncols, 0)
          fun doCol (i, p) = let
                val s = patToString p
                in
                  if size s > Array.sub(wids, i)
                    then Array.update(wids, i, size s)
                    else ();
                  s
                end
          fun doRow prow = List.mapi doCol prow
          fun prRow rowStrs = let
                fun prStr (i, s) = (
                      if (i > 0) then pr "  " else ();
                      pr (StringCvt.padRight #" " (Array.sub(wids, i)) s))
                in
                  pr "| ";
                  List.appi prStr rowStrs;
                  pr " |\n"
                end
          in
            List.app prRow (List.map doRow pmat)
          end

    fun sameConst (A.DConst(dc1, _), A.DConst(dc2, _)) = DataCon.same(dc1, dc2)
      | sameConst (A.LConst(lit1, ty1), A.LConst(lit2, ty2)) =
          L.same(lit1, lit2) andalso TypeUtil.same(ty1, ty2)

    fun cmpConst (A.DConst(dc1, _), A.DConst(dc2, _)) = DataCon.compare(dc1, dc2)
      | cmpConst (A.DConst _, _) = LESS
      | cmpConst (_, A.DConst _) = GREATER
(* FIXME: if we add literal overloading, then we will need a comparison for the type *)
      | cmpConst (A.LConst(lit1, _), A.LConst(lit2, _)) = L.compare(lit1, lit2)

    structure ConstSet = RedBlackSetFn (
      struct
        type ord_key = A.const
        val compare = cmpConst
      end)

  end
