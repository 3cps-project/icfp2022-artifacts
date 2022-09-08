(* cps-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSUtil : sig

    val labelOfLambda : CPS.lambda -> Label.t
    val labelOfCLambda : CPS.clambda -> Label.t
    val labelOfExp : CPS.exp -> Label.t

    val typeOfAtom : CPS.atom -> CPSTypes.t

  (* prim-op result types *)
    val typeOfPure : PrimOp.pure * CPSTypes.t list -> CPSTypes.t
    val typeOfArith : PrimOp.arith -> CPSTypes.t
    val typeOfGetter : PrimOp.getter * CPSTypes.t list -> CPSTypes.t
    val typeOfSetter : PrimOp.setter -> CPSTypes.t

    val atomToString : CPS.atom -> string

    val lvarsToStrings : LVar.Set.set -> string list

    val cvarsToStrings : CVar.Set.set -> string list

    val lvarMapToStrings : 'a LVar.Map.map * ('a -> string) -> string list

    val cvarMapToStrings : 'a CVar.Map.map * ('a -> string) -> string list

  (* Returns the expression constructor and label as string, with color (if enabled).  *)
    val expName : CPS.exp -> string

  end = struct

    structure C = CPS
    structure P = PrimOp
    structure Ty = CPSTypes
    structure PTy = CPSPrimTy

    fun labelOfLambda (_, l, _, _, _) = l
    fun labelOfCLambda (_, l, _, _) = l
    fun labelOfExp (C.EXP(l, _)) = l

    fun typeOfAtom (C.LVAR(x, tys)) = CPSTypeUtil.applyScheme(LVar.typeOf x, tys)
      | typeOfAtom (C.LIT(_, ty)) = ty
      | typeOfAtom (C.DCON(dc, tys)) = CPSTypeUtil.applyScheme(CPSDataCon.typeOf dc, tys)
      | typeOfAtom C.UNIT = Ty.TupleTy[]

    fun typeOfPure (rator, tys) = (case rator
           of P.NumOp(rator, _) => (case rator
                 of P.Pure.WAdd => PTy.wordTy
                  | P.Pure.WSub => PTy.wordTy
                  | P.Pure.WMul => PTy.wordTy
                  | P.Pure.WDiv => PTy.wordTy
                  | P.Pure.WMod => PTy.wordTy
                  | P.Pure.WNeg => PTy.wordTy
                  | P.Pure.Andb => PTy.wordTy
                  | P.Pure.Orb => PTy.wordTy
                  | P.Pure.XOrb => PTy.wordTy
                  | P.Pure.Notb => PTy.wordTy
                  | P.Pure.LShift => PTy.wordTy
                  | P.Pure.RShift => PTy.wordTy
                  | P.Pure.RShiftL => PTy.wordTy
                  | P.Pure.FAdd => PTy.realTy
                  | P.Pure.FSub => PTy.realTy
                  | P.Pure.FMul => PTy.realTy
                  | P.Pure.FDiv => PTy.realTy
                  | P.Pure.FNeg => PTy.realTy
                (* case *))
            | P.ZExt _ => PTy.intTy
            | P.SExt _ => PTy.intTy
            | P.IntToReal _ => PTy.realTy
            | P.Array0 => (case tys
                 of [ty] => PTy.arrayTy ty
                  | _ => raise Fail "typeOfPure(Array0, -)"
                (* end case *))
            | P.ArrayAlloc => (case tys
                 of [ty] => PTy.arrayTy ty
                  | _ => raise Fail "typeOfPure(ArrayAlloc, -)"
                (* end case *))
            | P.ArrayLength => PTy.intTy
            | P.Ref => (case tys
                 of [ty] => PTy.refTy ty
                  | _ => raise Fail "typeOfPure(Ref, -)"
                (* end case *))
            | P.StrSize => PTy.intTy
            | P.CharToStr => PTy.stringTy
            | P.SAppend => PTy.stringTy
            | P.Implode => PTy.stringTy
            | P.MathOp _ => PTy.realTy
            | _ => raise Fail(concat["typeOfPure(", P.Pure.toString rator, ", -)"])
          (* end case *))

    fun typeOfArith (P.IntOp _) = PTy.intTy
      | typeOfArith (P.Floor _) = PTy.intTy
      | typeOfArith P.StrSub = PTy.charTy

    fun typeOfGetter (P.ArraySub, [ty]) = ty
      | typeOfGetter (P.Deref, [ty]) = ty
      | typeOfGetter (rator, tys) = raise Fail(concat[
            "typeOfGetter(", P.Getter.toString rator, ", ",
            CPSTypeUtil.tysToString tys, ")"
          ])

    fun typeOfSetter _ = PTy.unitTy

    fun atomToString (C.LVAR(x, [])) = LVar.toString x
      | atomToString (C.LVAR(x, tys)) = concat [
            LVar.toString x, CPSTypeUtil.tysToString tys
          ]
      | atomToString (C.LIT(lit, _)) = Literal.toString lit
      | atomToString (C.DCON(dc, [])) = CPSDataCon.toString dc
      | atomToString (C.DCON(dc, tys)) = concat[
            CPSDataCon.toString dc, CPSTypeUtil.tysToString tys
          ]
      | atomToString C.UNIT = "()"

    fun lvarsToStrings set =
          "{" ::
            LVar.Set.foldr
                (fn (x, acc) => LVar.toString x :: "," :: acc)
                ["}"] set

    fun cvarsToStrings set =
          "{" ::
            CVar.Set.foldr
                (fn (x, acc) => CVar.toString x :: "," :: acc)
                ["}"] set

    fun lvarMapToStrings (map, toS) =
          "[" ::
            LVar.Map.foldri
                (fn (x, y, acc) => LVar.toString x :: " => " :: toS y :: "," :: acc)
                ["]"] map

    fun cvarMapToStrings (map, toS) =
          "[" ::
            CVar.Map.foldri
                (fn (x, y, acc) => CVar.toString x :: " => " :: toS y :: "," :: acc)
                ["]"] map

  (* Returns a string that gives a random foreground/background pair, deterministic on i *)
    local
      fun style i = let
            val it = i mod 56
            val color = it mod 7
            val bg = it mod 8
            val underline = (i mod 128) > 64
            val bold = (i mod 256) > 128
            val bg = 0
            in {
                fg = SOME(if color >= bg then color+1 else 0),
                bg = SOME bg,
                bf = bold,
                ul = underline
            } end
      fun expName' e = (case e
             of C.LETFUN _ => "letrec"
              | C.LETCONT _ => "letcont"
              | C.IF _ => "if"
              | C.SWITCH _ => "switch"
              | C.APPLY _ => "apply"
              | C.DCAPPLY _ => "dcapply"
              | C.PURE _ => "pure-prim"
              | C.ARITH _ => "arith-prim"
              | C.GET _ => "get-prim"
              | C.SET _ => "set-prim"
              | C.THROW _ => "throw"
              | C.TUPLE _ => "tuple"
              | C.SELECT _ => "select"
              | C.ATOM _ => "atom"
            (* end case *))
    in
    fun expName (C.EXP(l, e)) = let
          val i = Word.toIntX (Label.hash l)
          in
            ANSIText.fmt ({fg=SOME 7, bg=NONE, bf=true, ul=true}, expName' e) ^
            ANSIText.fmt (style i, concat["<", Label.toString l, ">"])
          end
    end (* local *)

    fun expMapToStrings (map, toS) =
          "{" ::
            C.Map.foldri
              (fn (x, y, acc) => expName x :: " => " :: toS y :: "," :: acc)
              ["}"] map

  end
