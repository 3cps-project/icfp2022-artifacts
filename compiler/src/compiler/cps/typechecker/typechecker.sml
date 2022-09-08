(* typechecker.sml
 *
 * A type checker for the CPS language.
 *
 * TODO: rewrite for new primops
 *       rename as CheckCPS
 *       move to cps directory
 *)

structure CPSTypeChecker : sig

    exception CPSTypeCheck
    val check : CPS.comp_unit -> unit

end = struct

    exception CPSTypeCheck

    structure C = CPS
    structure T = CPSTypes
    structure U = CPSTypeUtil
    structure PT = CPSPrimTy
    structure P = PrimOp

    fun type_error msg =
        (Verbose.say [msg, "\n"];
         raise CPSTypeCheck)

    fun typeSame msg (ty1, ty2) =
        case T.compare (ty1, ty2)
         of EQUAL => ()
          | _ => type_error (String.concatWith " " [msg, T.toString ty1, T.toString ty2])

    fun typeSameK msg (ty1, ty2) =
        case T.cmpCTy (ty1, ty2)
         of EQUAL => ()
          | _ => type_error msg

    fun removeTyScheme msg (T.TyScheme (tvars, ty)) =
        if List.null tvars
        then ty
        else type_error (msg ^ " non-zero ty vars")

    fun checkApply (f, tys, xs, ks) = let
        val targs = List.map LVar.typeOf xs
        val targs = List.map (removeTyScheme "APPLY") targs
        val targKs = List.map CVar.typeOf ks
    in
        case U.applyScheme (LVar.typeOf f, tys)
         of T.FunTy (targs, targKs) => let
             val targs' = List.map LVar.typeOf xs
             val targKs' = List.map CVar.typeOf ks
             val targs' = List.map (removeTyScheme "APPLY args") targs'
             val () = ListPair.app (typeSame "APPLY args") (targs, targs')
             val () = ListPair.app (typeSameK "APPLY argKs") (targKs, targKs')
         in () end
          | _ => type_error "APPLY not given FunTy"
    end

    fun checkThrow (k, xs) = let
        val (T.ContTy targs) = CVar.typeOf k
        val targs' = List.map LVar.typeOf xs
        val targs' = List.map (removeTyScheme "THROW") targs'
        val () = ListPair.app (typeSame "THROW") (targs, targs')
    in () end

    fun instantiateTyc (tycon, tys) =
        raise Fail "TODO"

    fun checkAtom (x, arg) = let
        val ty = removeTyScheme "ATOM" (LVar.typeOf x)
    in
        case arg
         of C.LVAR (y, tys) => let
             val ty' = U.applyScheme (LVar.typeOf y, tys)
         in typeSame "ATOM LVAR" (ty, ty') end
          | C.LIT (lit, ty') =>
            typeSame "ATOM LIT" (ty, ty')
          | C.DCON (T.DCon dcon, tys) => let
              val ty' = T.ConTy (tys, #owner dcon)
          in typeSame "ATOM DCON" (ty, ty') end
          | UNIT => let
              val ty' = PT.unitTy
          in typeSame "ATOM UNIT " (ty, ty') end
    end

    fun checkTest (oper, args) = let
        val tys = List.map LVar.typeOf args
        val tys = List.map (removeTyScheme "Test") tys
        val same = typeSame (P.Test.toString oper)
    in ()
    (*
      case (oper, tys)
       of (P.ICmp (rator, prec), args) => (case (rator, args)
           of (P.Test.ILt, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
            | (P.Test.ILte, [ty1, ty2]) => PE.ile (prec, ty1, ty2)
            | (P.Test.IEq, [ty1, ty2]) => ty1 = ty2
            | (P.Test.INeq, [ty1, ty2]) => ty1 <> ty2
            | (P.Test.IGt, [ty1, ty2]) => PE.igt (prec, ty1, ty2)
            | (P.Test.IGte, [ty1, ty2]) => PE.ige (prec, ty1, ty2)

            | (P.Test.ULt, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | (P.Test.ULte, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | (P.Test.IEq, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | (P.Test.INeq, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | (P.Test.UGt, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | (P.Test.UGte, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
            | _ => primFail (P.Test.toString oper) d_args)
        | (P.FCmp (rator, prec), args) => (case (rator, args)
           of (P.Test.FLt, [VB.FLOAT f1, VB.FLOAT f2]) => PE.flt (prec, f1, f2)
            | (P.Test.FLte, [VB.FLOAT f1, VB.FLOAT f2]) => PE.fle (prec, f1, f2)
            | (P.Test.FEq, [VB.FLOAT f1, VB.FLOAT f2]) => PE.feq (prec, f1, f2)
            | (P.Test.FNeq, [VB.FLOAT f1, VB.FLOAT f2]) => PE.fne (f1, f2)
            | (P.Test.FGt, [VB.FLOAT f1, VB.FLOAT f2]) => PE.fgt (prec, f1, f2)
            | (P.Test.FGte, [VB.FLOAT f1, VB.FLOAT f2]) => PE.fge (prec, f1, f2)
            | _ => primFail (P.Test.toString oper) d_args)

        | (P.SLt, [VB.STRING s1, VB.STRING s2]) => s1 < s2
        | (P.SLte, [VB.STRING s1, VB.STRING s2]) => s1 <= s2
        | (P.SEq, [VB.STRING s1, VB.STRING s2]) => s1 = s2
        | (P.SNEq, [VB.STRING s1, VB.STRING s2]) => s1 <> s2
        | (P.SGte, [VB.STRING s1, VB.STRING s2]) => s1 >= s2
        | (P.SGt, [VB.STRING s1, VB.STRING s2]) => s1 > s2

        | (P.PolyEq, [d1, d2]) => poly_equal (d1, d2, load_addr)
        | (P.PolyNEq, [d1, d2]) => not (poly_equal (d1, d2, load_addr))
        | (P.PtrEq, [VB.ARRAY addrs1, VB.ARRAY addrs2]) => 
          (case List.collate A.compare (addrs1, addrs2)
            of EQUAL => true
             | _ => false)
        | (P.PtrEq, [VB.REF a1, VB.REF a2]) => 
          (case A.compare (a1, a2)
            of EQUAL => true
             | _ => false)

              (*
        | (P.Test, [VB.DATA (dcon, ao)]) =>
          if (substring (ThreeCPSDataValue.toString (dcon, ao), 0, 8)) = "(dv true"
          then true
          else if (substring (ThreeCPSDataValue.toString (dcon, ao), 0, 9)) = "(dv false"
          then false
          else primFail (P.Test.toString oper) d_args
          *)
        | _ => primFail (P.Test.toString oper) d_args


        case (oper, tys)
         of (P.Test.CLt,  [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
          | (P.Test.CLte, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
          | (P.Test.CEq,  [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
          | (P.Test.CNEq, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
          | (P.Test.CGte, [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))
          | (P.Test.CGt,  [ty1, ty2]) => (same (ty1, PT.charTy); same (ty2, PT.charTy))

          | (P.Test.ILt,  [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
          | (P.Test.ILte, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
          | (P.Test.IEq,  [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
          | (P.Test.INEq, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
          | (P.Test.IGte, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
          | (P.Test.IGt,  [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))

          | (P.Test.WLt,  [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
          | (P.Test.WLte, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
          | (P.Test.WEq,  [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
          | (P.Test.WNEq, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
          | (P.Test.WGte, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
          | (P.Test.WGt,  [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))

          | (P.Test.FLt,  [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
          | (P.Test.FLte, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
          | (P.Test.FEq,  [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
          | (P.Test.FNEq, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
          | (P.Test.FGte, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
          | (P.Test.FGt,  [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))

          | (P.Test.SLt,  [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
          | (P.Test.SLte, [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
          | (P.Test.SEq,  [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
          | (P.Test.SNEq, [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
          | (P.Test.SGte, [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
          | (P.Test.SGt,  [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))

          | (P.Test.PtrEq, [ty1, ty2]) => raise Fail "TODO"
          | (P.Test.PtrNEq, [ty1, ty2]) => raise Fail "TODO"
          | (P.Test.PolyEq, [ty1, ty2]) => raise Fail "TODO"
          | (P.Test.PolyNEq, [ty1, ty2]) => raise Fail "TODO"
          | (P.Test.Test, [ty]) => raise Fail "TODO"
          | _ => type_error ""
        (* end case *)
*)
    end

    fun checkPure (x, oper, args) = let
        val _ =
            (* cases where there may be polymorphism... *)
            case oper
             of P.Pure.Array0 => raise Fail "TODO"
              | P.Pure.ArrayAlloc => raise Fail "TODO"
              | P.Pure.ArrayLength => raise Fail "TODO"
              | P.Pure.Ref => raise Fail "TODO"
              | _ => ()
        val tys = List.map LVar.typeOf args
        val tys = List.map (removeTyScheme "Pure") tys
        val same = typeSame (P.Pure.toString oper)
    in () (* case (oper, tys)
        of (P.Pure.WAdd, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
         | (P.Pure.WSub, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
         | (P.Pure.WMul, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
         | (P.Pure.WDiv, [ty1, ty2]) => (same (ty1, PT.wordTy); same (ty2, PT.wordTy))
         | (P.Pure.WMod, [ty]) => same (ty, PT.wordTy)
         | (P.Pure.WNeg, [ty]) => same (ty, PT.wordTy)
         | (P.Pure.Andb, [ty1, ty2]) => raise Fail "TODO"
         | (P.Pure.Orb, [ty1, ty2]) => raise Fail "TODO"
         | (P.Pure.XOrb, [ty1, ty2]) => raise Fail "TODO"
         | (P.Pure.Notb, [ty]) => raise Fail "TODO"
         | (P.Pure.LShift, [ty]) => raise Fail "TODO"
         | (P.Pure.RShift, [ty]) => raise Fail "TODO"
         | (P.Pure.RShiftL, [ty]) => raise Fail "TODO"
         | (P.Pure.FAdd, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.FSub, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.FMul, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.FDiv, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.FNeg, [ty]) => same (ty, PT.realTy)
         | (P.Pure.CharToInt, [ty]) => same (ty, PT.charTy)
         | (P.Pure.IntToReal, [ty]) => same (ty, PT.intTy)
         | (P.Pure.StrSize, [ty]) => same (ty, PT.stringTy)
         | (P.Pure.CharToStr, [ty]) => same (ty, PT.charTy)
         | (P.Pure.SAppend, [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.stringTy))
         | (P.Pure.Sqrt, [ty]) => same (ty, PT.realTy)
         | (P.Pure.Ln, [ty]) => same (ty, PT.realTy)
         | (P.Pure.Exp, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.Pow, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | (P.Pure.Sin, [ty]) => same (ty, PT.realTy)
         | (P.Pure.Cos, [ty]) => same (ty, PT.realTy)
         | (P.Pure.Tan, [ty]) => same (ty, PT.realTy)
         | (P.Pure.ASin, [ty]) => same (ty, PT.realTy)
         | (P.Pure.ACos, [ty]) => same (ty, PT.realTy)
         | (P.Pure.ATan, [ty]) => same (ty, PT.realTy)
         | (P.Pure.ATan2, [ty1, ty2]) => (same (ty1, PT.realTy); same (ty2, PT.realTy))
         | _ => raise Fail "CPSTypeChecker.unknown-pure-primop"
        *)
    end

    fun checkArith (x, oper, args) = let
        val tys = List.map LVar.typeOf args
        val tys = List.map (removeTyScheme "Arith") tys
        val same = typeSame (P.Arith.toString oper)
    in () (* case (oper, tys)
        of (P.Arith.IAdd, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
         | (P.Arith.ISub, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
         | (P.Arith.IDiv, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
         | (P.Arith.IMod, [ty1, ty2]) => (same (ty1, PT.intTy); same (ty2, PT.intTy))
         | (P.Arith.INeg, [ty]) => same (ty, PT.intTy)
         | (P.Arith.Floor, [ty]) => same (ty, PT.realTy)
         | (P.Arith.StrSub, [ty1, ty2]) => (same (ty1, PT.stringTy); same (ty2, PT.intTy))
         | _ => raise Fail "CPSTypeChecker.unknown-arith-primop"
           *)
    end

    fun checkGet (x, oper, args) = raise Fail "TODO"

    fun checkSet (x, oper, args) = let
        val _ =
            case oper
             of P.Setter.ArrayUpdate => raise Fail "TODO"
              | P.Setter.Assign => raise Fail "TODO"
              | _ => ()
        val tys = List.map LVar.typeOf args
        val tys = List.map (removeTyScheme "Set") tys
        val same = typeSame (P.Setter.toString oper)
    in () (*case (oper, tys)
        of (P.Setter.Print, [ty]) => same (ty, PT.stringTy)
         | _ => raise Fail "CPSTypeChecker.unknown-set-primop"
           *)
    end

    fun checkTuple (x, args) = let
        val ty = removeTyScheme "TUPLE var" (LVar.typeOf x)
        val tys = List.map LVar.typeOf args
        val tys = List.map (removeTyScheme "TUPLE arg") tys
        val ty' = T.TupleTy tys
    in typeSame "TUPLE var" (ty, ty') end

    fun checkSelect (x, arg, offset) = let
        val ty = removeTyScheme "SELECT var" (LVar.typeOf x)
        val tup_ty = removeTyScheme "SELECT arg" (LVar.typeOf arg)
    in case tup_ty
        of T.TupleTy tys =>
           typeSame "SELECT var" (ty, List.nth (tys, offset-1))
         | _ => type_error ""
    end

    fun checkDCApply (x, T.DCon dcon, tys, arg) = let
       val argTy = case #argTy dcon
                    of SOME argTy => argTy
                     | NONE => raise Fail "impossible"
       val argTy' = LVar.typeOf arg
       val argTy' = removeTyScheme "DCAPPLY arg" argTy'
       val ty = removeTyScheme "DCAPPLY var" (LVar.typeOf x)
       val ty' = T.ConTy (tys, #owner dcon)
    in typeSame "DCAPPLY arg" (argTy, argTy'); typeSame "DCAPPLY var" (ty, ty') end

    fun checkSwitch (arg, pats) = let
        val switch_ty = removeTyScheme "SWITCH var" (LVar.typeOf arg)
        fun handle_pat (pat, _) =
            case pat
             of C.VPAT x => let
                 val ty = removeTyScheme "SWITCH VPAT" (LVar.typeOf x)
             in typeSame "SWITCH VPAT" (ty, switch_ty) end
              | C.LPAT (lit, ty) => typeSame "SWITCH LIT" (switch_ty, ty)
              | C.DCPAT (T.DCon dcon, tys, x_opt) => let
                  val () = case (x_opt, #argTy dcon)
                            of (SOME x, SOME ty') => let
                                val ty = removeTyScheme "SWITCH CASE" (LVar.typeOf x)
                            in typeSame "SWITCH CASE" (ty, ty') end
                             | (NONE, NONE) => ()
                             | _ => raise Fail "impossible"
                  val switch_ty' = T.ConTy (tys, #owner dcon)
              in typeSame "SWITCH con" (switch_ty, switch_ty') end
    in List.app handle_pat pats end

    fun checkFunType (f, xs, ks) =
        case LVar.typeOf f
         of T.TyScheme (tvars, T.FunTy (targs, targKs)) => let
             val targs' = List.map LVar.typeOf xs
             val targKs' = List.map CVar.typeOf ks
             val targs' = List.map (removeTyScheme "checkFunType") targs'
             val () = ListPair.app (typeSame "checkFunType") (targs, targs')
         in () end
          | _ => type_error ""

    fun checkContType (k, xs) = let
        val (T.ContTy targs) = CVar.typeOf k
        val targs' = List.map LVar.typeOf xs
        val targs' = List.map (removeTyScheme "checkContType") targs'
        val () = ListPair.app (typeSame "checkContType") (targs, targs')
    in () end

    fun check (C.CU lam0) = let
        fun check_exp (exp as C.EXP (lab_e, e)) =
            case e
             of C.LETFUN (bindings, body) =>
                (List.app (fn lam => check_lam lam) bindings;
                 check_exp body;
                 ())
              | C.LETCONT (bindingKs, body) =>
                (List.app (fn lamK => check_lamK lamK) bindingKs;
                 check_exp body;
                 ())
              | C.IF (oper, args, thn, els) =>
                (checkTest (oper, args);
                 check_exp thn;
                 check_exp els;
                 ())
              | C.ATOM (arg, x, e') =>
                (checkAtom (x, arg);
                 check_exp e';
                 ())

              | C.PURE (oper, args, x, e') =>
                (checkPure (x, oper, args);
                 check_exp e';
                 ())
              | C.ARITH (oper, args, x, e', e_exn) =>
                (checkArith (x, oper, args);
                 check_exp e';
                 check_exp e_exn;
                 ())
              | C.GET (oper, args, x, e') =>
                (checkGet (x, oper, args);
                 check_exp e';
                 ())
              | C.SET (oper, args, x, e') =>
                (checkSet (x, oper, args);
                 check_exp e';
                 ())

              | C.TUPLE(args, x, e') =>
                (checkTuple (x, args);
                 check_exp e';
                 ())
              | C.SELECT(offset, arg, x, e') =>
                (checkSelect (x, arg, offset);
                 check_exp e';
                 ())

              | C.DCAPPLY(dcon, tys, arg, x, e') =>
                (checkDCApply (x, dcon, tys, arg);
                 check_exp e';
                 ())
              | C.SWITCH(arg, pats) =>
                (checkSwitch (arg, pats);
                 List.app (fn (_, e') => check_exp e') pats;
                 ())

              | C.APPLY(f, tys, args, argKs) =>
                (checkApply (f, tys, args, argKs);
                 ())
              | C.THROW (k, args) =>
                (checkThrow (k, args);
                 ())
        and check_lamK (k, lamK_lab, xs, body) =
            (checkContType (k, xs);
             check_exp body;
             ())
        and check_lam (f, lam_lab, xs, ks, body) =
            (checkFunType (f, xs, ks);
             check_exp body;
             ())
        val () = check_lam lam0
    in () end

end
