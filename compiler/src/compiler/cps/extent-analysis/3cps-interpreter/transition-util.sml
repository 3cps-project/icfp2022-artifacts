(* transition-util.sml
 * 
 * Util functions for the concrete transitions.
 *)

structure ThreeCPSTransitionUtil =
struct

  structure C = CPS
  structure P = PrimOp
  structure LS = Label.Set
  structure LVS = LVar.Set

  structure A = ThreeCPSAddr
  structure VB = ThreeCPSValueBase
  structure V = ThreeCPSValue
  structure VKB = ThreeCPSValueKBase
  structure VK = ThreeCPSValueK

  type mutable_state = {stack_pointer : int ref,
                        heap_pointer : int ref,
                        stackK_pointer : int ref,
                        registers : V.t LVar.Tbl.hash_table,
                        stack : V.t UnboundedArray.t,
                        heap : V.t UnboundedArray.t,
                        stackK : VK.t UnboundedArray.t,
                        count_lvar_alloc : int LVar.Tbl.hash_table,
                        count_lam_alloc : int Label.Tbl.hash_table,
                        expsSeen : LS.set ref,
                        lvarsBound : LVS.set ref}

  type state = C.exp * (int LVar.Map.map) * (int CVar.Map.map) * (CPSTypes.t CPSTyVar.Map.map)

  fun literalToValueBase lit =
      (case lit
        of Literal.Int int_lit => VB.INT (int_lit)
         | Literal.Word word_lit => VB.WORD (Word.fromInt (IntInf.toInt word_lit))
         | Literal.Real float_lit => VB.FLOAT (valOf (Real.fromString (FloatLit.toString float_lit)))
         | Literal.Char c => VB.CHAR (IntInf.fromInt (Char.ord c))
         | Literal.String s => VB.STRING s
      (* end case *))

  fun literalToValue (mutable_state : mutable_state) (lit) =
      V.make (literalToValueBase lit)

  (* The helper function for evaluating (user) atoms *)
  fun evalAtom (mutable_state : mutable_state) (ae, env, load) =
      (case ae
        of C.LVAR (x, _) => load (x, env)
         | C.LIT(lit, _) => literalToValue mutable_state (lit)
         | C.DCON(dcon, _) => V.make (VB.DATA (dcon, NONE))
         | C.UNIT => V.make VB.UNIT
      (* end case *))

  fun primFail prim_str d_args =
      raise Fail(String.concat ["bad primop: ", prim_str, " with ", Int.toString (List.length d_args), " args: ", String.concatWithMap "" V.toString d_args])

  fun unhandledPrim prim_str d_args =
      raise Fail(String.concat ["knowingly unhandled primop: ", prim_str, " with ", Int.toString (List.length d_args), " args"])

  fun evalPurePrim (mutable_state : mutable_state) (oper, d_args, alloc_heap, store_addr) = let
      val d =
          case (oper, List.map V.base d_args)
           of (P.Pure.NumOp(rator, prec), args) => (case (rator, args)
                 of (P.Pure.FAdd, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (PrimEval.fadd (prec, x1, x2))
                  | (P.Pure.FSub, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (PrimEval.fsub (prec, x1, x2))
                  | (P.Pure.FMul, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (PrimEval.fmul (prec, x1, x2))
                  | (P.Pure.FDiv, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (PrimEval.fdiv (prec, x1, x2))
                  | (P.Pure.FNeg, [VB.FLOAT x]) => VB.FLOAT (PrimEval.fneg (prec, x))
                  | _ => primFail (P.Pure.toString oper) d_args
                (* end case *))
            | (P.Pure.IntToReal precs, [VB.INT i]) => VB.FLOAT (PrimEval.int2real (precs, i))
            (* QUESTION: are these the correct sml functions to use for these primops *)
            | (P.Pure.ZExt _, [VB.CHAR c]) => VB.INT c (* FIXME: patch up for precision *)
            | (P.Pure.CharToStr, [VB.CHAR c]) => VB.STRING (Char.toString (Char.chr (IntInf.toInt c)))
            | (P.Pure.StrSize, [VB.STRING s]) => VB.INT (IntInf.fromInt (String.size s)) (* FIXME: patch up for precision *)
            | (P.Pure.Implode, [arg]) => (* let
                fun data_to_list (VB.DATA (dcon, ao)) =
                    if CPSDataCon.same (dcon, 

                in end *) unhandledPrim (P.Pure.toString P.Pure.Implode) [arg]
            | (P.Pure.SAppend, [VB.STRING s1, VB.STRING s2]) => VB.STRING (s1 ^ s2)
            | (P.Pure.Ref, [_]) => let
                val a = A.HeapAddr (alloc_heap ())
                val d_ref = V.make (VB.REF a)
                val () = store_addr (a, hd d_args)
            in d_ref end
            | (P.Pure.Array0, []) => let
                val d = V.make (VB.ARRAY [])
            in d end
            | (P.Pure.ArrayAlloc, [VB.INT size, _]) => let
                val addrs = List.tabulate (IntInf.toInt size, (fn _ => A.HeapAddr (alloc_heap ()))) (* FIXME: patch up for precision *)
                val d_init = List.nth (d_args, 1)
                val d = V.make (VB.ARRAY addrs)
                val () = List.app (fn a => store_addr (a, d_init)) addrs
            in d end                                         
            | (P.Pure.ArrayLength, [VB.ARRAY addrs]) => VB.INT (IntInf.fromInt (List.length addrs)) (* FIXME: patch up for precision *)
	    | (P.Pure.MathOp(rator, _), args) => (case (rator, args)
                 of (P.Pure.Sqrt, [VB.FLOAT x]) => VB.FLOAT (Math.sqrt x)
                  | (P.Pure.Ln, [VB.FLOAT x]) => VB.FLOAT (Math.ln x)
                  | (P.Pure.Exp, [VB.FLOAT x]) => VB.FLOAT (Math.exp x)
                  | (P.Pure.Pow, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (Math.pow (x1, x2))
                  | (P.Pure.Sin, [VB.FLOAT x]) => VB.FLOAT (Math.sin x)
                  | (P.Pure.Cos, [VB.FLOAT x]) => VB.FLOAT (Math.cos x)
                  | (P.Pure.Tan, [VB.FLOAT x]) => VB.FLOAT (Math.tan x)
                  | (P.Pure.ASin, [VB.FLOAT x]) => VB.FLOAT (Math.asin x)
                  | (P.Pure.ACos, [VB.FLOAT x]) => VB.FLOAT (Math.acos x)
                  | (P.Pure.ATan, [VB.FLOAT x]) => VB.FLOAT (Math.atan x)
                  | (P.Pure.ATan2, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (Math.atan2 (x1, x2))
                  | _ => primFail (P.Pure.toString oper) d_args
                (* end case *))
            | _ => primFail (P.Pure.toString oper) d_args
  in V.make d end

  (* assuming no overflow; the main body will catch it if it occurs *)
  fun evalArithPrim (mutable_state : mutable_state) (oper, d_args) = let
      val d =
          case (oper, List.map V.base d_args)
	   of (P.IntOp(rator, prec), args) => (case (rator, args)
                 of (P.Arith.IAdd, [VB.INT i1, VB.INT i2]) => VB.INT (PrimEval.iadd (prec, i1, i2))
                  | (P.Arith.ISub, [VB.INT i1, VB.INT i2]) => VB.INT (PrimEval.isub (prec, i1, i2)) 
                  | (P.Arith.IMul, [VB.INT i1, VB.INT i2]) => VB.INT (PrimEval.imul (prec, i1, i2)) 
                  | (P.Arith.IDiv, [VB.INT i1, VB.INT i2]) => VB.INT (PrimEval.idiv (prec, i1, i2))
                  | (P.Arith.IMod, [VB.INT i1, VB.INT i2]) => VB.INT (PrimEval.imod (prec, i1, i2))
                  | (P.Arith.INeg, [VB.INT i]) => VB.INT (PrimEval.ineg (prec, i))
                  | _ => primFail (P.Arith.toString oper) d_args
                (* end case *))
            | (P.Arith.Floor precs, [VB.FLOAT x]) => VB.INT (PrimEval.floor(precs, x))
            | (P.Arith.StrSub, [VB.STRING s, VB.INT i]) => VB.CHAR (IntInf.fromInt (Char.ord (String.sub (s, IntInf.toInt i)))) (* FIXME: patch up for precision *)
            | _ => primFail (P.Arith.toString oper) d_args
  in V.make d end

  fun evalGetPrim (mutable_state : mutable_state) (oper, d_args, load_addr) =
      case (oper, List.map V.base d_args)
       of (P.Getter.Deref, [VB.REF a]) => load_addr a
        | (P.Getter.ArraySub, [VB.ARRAY addrs, VB.INT index]) => let
            val a = List.nth (addrs, IntInf.toInt index) (* FIXME: patch up for precision *)
                    handle Subscript =>
                           raise Fail ((Int.toString (List.length addrs)) ^ " " ^ (IntInf.toString index))
        in load_addr a end
        | _ => primFail (P.Getter.toString oper) d_args

  fun evalSetPrim (mutable_state : mutable_state) (oper, d_args, store_addr) = 
      case (oper, List.map V.base d_args)
       of (P.Setter.Assign, [VB.REF a, _]) => let
           val () = store_addr (a, hd(tl(d_args)))
       in V.make (VB.UNIT) end
        | (P.Setter.ArrayUpdate, [VB.ARRAY addrs, VB.INT index, _]) => let
            val a = List.nth (addrs, IntInf.toInt index) (* FIXME: patch up for precision *)
                    handle Subscript =>
                           raise Fail ((Int.toString (List.length addrs)) ^ " " ^ (IntInf.toString index))
            val () = store_addr (a, List.nth (d_args, 2))
        in V.make (VB.UNIT) end
        | (P.Setter.Print, [VB.STRING s]) => ((* print s; *) V.make VB.UNIT)
        | _ => primFail (P.Setter.toString oper) d_args

  fun poly_equal (d1, d2, load_addr) =
      case (d1, d2)
       of (VB.CLO clo1, VB.CLO clo2) => raise Fail "passed closures to poly_equal"
        | (VB.CLO _, _) => raise Fail "passed closures to poly_equal"
        | (_, VB.CLO _) => raise Fail "passed closures to poly_equal"
        | (VB.DATA (dc1, a1o), VB.DATA (dc2, a2o)) =>
          (case (CPSDataCon.compare (dc1, dc2), a1o, a2o)
            of (EQUAL, SOME a1, SOME a2) =>
               poly_equal (V.base (load_addr a1),
                           V.base (load_addr a2),
                           load_addr)
             | (EQUAL, NONE, NONE) => true
             | _ => false)
        | (VB.DATA _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.DATA _) => raise Fail "different types passed to poly_equal"
        | (VB.REF r1, VB.REF r2) => A.same (r1, r2)
        | (VB.REF _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.REF _) => raise Fail "different types passed to poly_equal"
        | (VB.ARRAY arr1, VB.ARRAY arr2) => ListPair.all A.same (arr1, arr2)
        | (VB.ARRAY _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.ARRAY _) => raise Fail "different types passed to poly_equal"
        | (VB.TUPLE t1, VB.TUPLE t2) =>
          ListPair.all
              (fn (a1, a2) =>
                  poly_equal (V.base (load_addr a1),
                              V.base (load_addr a2),
                              load_addr))
              (t1, t2)
        | (VB.TUPLE _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.TUPLE _) => raise Fail "different types passed to poly_equal"
        | (VB.UNIT, VB.UNIT) => true
        | (VB.UNIT, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.UNIT) => raise Fail "different types passed to poly_equal"
        | (VB.INT i1, VB.INT i2) => i1 = i2
        | (VB.INT _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.INT _) => raise Fail "different types passed to poly_equal"
        | (VB.WORD w1, VB.WORD w2) => w1 = w2
        | (VB.WORD _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.WORD _) => raise Fail "different types passed to poly_equal"
        | (VB.FLOAT f1, VB.FLOAT f2) => raise Fail "passed reals to poly_equal"
        | (VB.FLOAT _, _) => raise Fail "passed reals to poly_equal"
        | (_, VB.FLOAT _) => raise Fail "passed reals to poly_equal"
        | (VB.CHAR c1, VB.CHAR c2) => c1 = c2
        | (VB.CHAR _, _) => raise Fail "different types passed to poly_equal"
        | (_, VB.CHAR _) => raise Fail "different types passed to poly_equal"
        | (VB.STRING s1, VB.STRING s2) => s1 = s2
      
  fun evalTestPrim (oper, d_args, load_addr) =
      case (oper, List.map V.base d_args)
       of (P.ICmp (rator, prec), args) => (case (rator, args)
           of (P.Test.ILt, [VB.INT i1, VB.INT i2]) => PrimEval.ilt (prec, i1, i2)
            | (P.Test.ILte, [VB.INT i1, VB.INT i2]) => PrimEval.ile (prec, i1, i2)
            | (P.Test.IEq, [VB.INT i1, VB.INT i2]) => i1 = i2
            | (P.Test.INEq, [VB.INT i1, VB.INT i2]) => i1 <> i2
            | (P.Test.IGt, [VB.INT i1, VB.INT i2]) => PrimEval.igt (prec, i1, i2)
            | (P.Test.IGte, [VB.INT i1, VB.INT i2]) => PrimEval.ige (prec, i1, i2)

            | (P.Test.ULt, [VB.CHAR c1, VB.CHAR c2]) => PrimEval.ult (prec, c1, c2)
            | (P.Test.ULte, [VB.CHAR c1, VB.CHAR c2]) => PrimEval.ule (prec, c1, c2)
            | (P.Test.IEq, [VB.CHAR c1, VB.CHAR c2]) => c1 = c2
            | (P.Test.INEq, [VB.CHAR c1, VB.CHAR c2]) => c1 <> c2
            | (P.Test.UGt, [VB.CHAR c1, VB.CHAR c2]) => PrimEval.ugt (prec, c1, c2)
            | (P.Test.UGte, [VB.CHAR c1, VB.CHAR c2]) => PrimEval.uge (prec, c1, c2)
            | _ => primFail (P.Test.toString oper) d_args)
        | (P.FCmp (rator, prec), args) => (case (rator, args)
           of (P.Test.FLt, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.flt (prec, f1, f2)
            | (P.Test.FLte, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.fle (prec, f1, f2)
            | (P.Test.FEq, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.feq (prec, f1, f2)
            | (P.Test.FNEq, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.fne (prec, f1, f2)
            | (P.Test.FGt, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.fgt (prec, f1, f2)
            | (P.Test.FGte, [VB.FLOAT f1, VB.FLOAT f2]) => PrimEval.fge (prec, f1, f2)
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

  fun update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, new_bindings) =
      if not (Controls.get Ctl.checkAnalysisResults)
      then ()
      else 
      List.app (fn frm => Frame.Tbl.insert frm_bindingAlloc (frm, new_bindings @ (Frame.Tbl.lookup frm_bindingAlloc frm)))
               lexFrms

  fun update_frm_ldataAlloc (frm_ldataAlloc, lexFrms, new_values) =
      if not (Controls.get Ctl.checkAnalysisResults)
      then ()
      else 
      List.app (fn frm => Frame.Tbl.insert frm_ldataAlloc (frm, new_values @ (Frame.Tbl.lookup frm_ldataAlloc frm)))
               lexFrms

  fun popFrms (popTos : Frame.t list, wholeStack : Frame.t list) : (Frame.t list) * (Frame.t list) = 
      if not (Controls.get Ctl.checkAnalysisResults)
      then ([], [])
      else let
      fun search stack =
          case stack
           of [] =>
              if List.null popTos
              then ([], [])
              else raise (Fail "impossible")
            | (frm :: rst) =>
              if List.exists (fn popTo => Frame.same (frm, popTo)) popTos
              then ([], stack)
              else let
                  val (popped, notPopped) = search rst
              in (frm::popped, notPopped) end
  in search wholeStack end

  fun incr_lvar_count (mutable_state : mutable_state, x) : unit = let
      val tbl = #count_lvar_alloc mutable_state
      val count = LVar.Tbl.lookup tbl x
  in LVar.Tbl.insert tbl (x, count + 1) end

  fun incr_lam_count (mutable_state : mutable_state, lam) : unit = let
      val tbl = #count_lam_alloc mutable_state
      val count = Label.Tbl.lookup tbl lam
  in Label.Tbl.insert tbl (lam, count + 1) end

  fun removeScheme (CPSTypes.TyScheme (_, ty)) = ty

  fun instantiateTy (tenv, ty) =
      case ty
       of CPSTypes.VarTy xty =>
          (case CPSTyVar.Map.find (tenv, xty)
            of SOME ty' => ty'
             | NONE => ty)
        | CPSTypes.ConTy (tys, tycon) =>
          (* need to do anything with tycon? *)
          CPSTypes.ConTy (List.map (fn ty => instantiateTy (tenv, ty)) tys, tycon)
        | CPSTypes.TupleTy tys =>
          CPSTypes.TupleTy (List.map (fn ty => instantiateTy (tenv, ty)) tys)
        | CPSTypes.FunTy (tys, ctys) =>
          CPSTypes.FunTy (List.map (fn ty => instantiateTy (tenv, ty)) tys,
                          List.map (fn cty => instantiateCTy (tenv, cty)) ctys)

  and instantiateCTy (tenv, CPSTypes.ContTy tys) =
      CPSTypes.ContTy (List.map (fn ty => instantiateTy (tenv, ty)) tys)

  (* instantiates the types in tys_src and ctys_src, mapping type
     variables by looking them up in tenv, or by looking them up in tvars
     and mapping them to those in tys_hint *)
  fun instantiate (tenv, tvars, tys_hint, ty) = let
      fun handle_ty_hint (xty, ty_hint, tenv) = let
          val tenv = CPSTyVar.Map.insert (tenv, xty, instantiateTy (tenv, ty_hint))
      in tenv end
      val tenv = ListPair.foldl handle_ty_hint tenv (tvars, tys_hint)
  in instantiateTy (tenv, ty) end

  fun unify (ty1, ty2, acc) =
      case acc
       of NONE => NONE
        | SOME tenv =>
          (case (ty1, ty2)
            of (CPSTypes.ConTy (tys1, tycon1),
                CPSTypes.ConTy (tys2, tycon2)) =>
               (case CPSTyCon.compare (tycon1, tycon2)
                 of EQUAL => unify_list (tys1, tys2, acc)
                  | _ => NONE)
             | (CPSTypes.TupleTy tys1, CPSTypes.TupleTy tys2) =>
               unify_list (tys1, tys2, acc)
             | (CPSTypes.FunTy (tys1, ctys1), CPSTypes.FunTy (tys2, ctys2)) =>
               unify_list_c (ctys1, ctys2, unify_list (tys1, tys2, acc))
             | (CPSTypes.VarTy xty, _) =>
               (case CPSTyVar.Map.find (tenv, xty)
                 of NONE => SOME (CPSTyVar.Map.insert (tenv, xty, ty2))
                  | SOME ty2' =>
                    (case CPSTypes.compare (ty2, ty2')
                      of EQUAL => SOME tenv
                       | _ => NONE))
             (* There should not be any type variables in ty2 at this point *)
             | _ => NONE)

  and unify_list_c (ctys1, ctys2, acc) =
      case acc
       of NONE => NONE
        | _ => if (List.length ctys1 = List.length ctys2)
               then ListPair.foldl unify_c acc (ctys1, ctys2)
               else NONE

  and unify_list (tys1, tys2, acc) =
      case acc
       of NONE => NONE
        | _ => if (List.length tys1 = List.length tys2)
               then ListPair.foldl unify acc (tys1, tys2)
               else NONE

  and unify_c (CPSTypes.ContTy tys1, CPSTypes.ContTy tys2, acc) =
      case acc
       of NONE => NONE
        | _ => unify_list (tys1, tys2, acc)

  (* unify tys_src with tys_dst, obtaining mappings for type variables in tys_dst,
     and extending tenv with those mappings *)
  fun unifyAndExtend (tenv, ty_src, ty_dst) : (CPSTypes.t CPSTyVar.Map.map) option =
      unify (ty_dst, ty_src, SOME tenv)

  fun unifyCont (tenv, cty_src, cty_dst) =
      unify_c (cty_src, cty_dst, SOME tenv)

(*
  fun checkTypes (tenv, x, d) = let
      val CPSTypes.TyScheme (_, ty) = LVar.typeOf x
      val ty = U.instantiateTy (tenv, ty)
  in case V.base d
      of 


     handle _ => raise Fail (String.concat ["bad check type: ", (* fixme *)TEnv.toString tenv, " ", LVar.toString x, " ", V.toString d]);
     ()
  end
*)

end
