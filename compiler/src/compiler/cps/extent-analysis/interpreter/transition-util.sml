(* transition-util.sml
 *
 * Util functions for the concrete transitions.
 *)

structure CTransitionUtil =
struct

  structure C = CPS
  structure P = PrimOp
  structure LS = Label.Set
  structure LVS = LVar.Set

  structure A = CAddr
  structure AK = CAddrK
  structure VB = CValueBase
  structure V = CValue
  structure VKB = CValueKBase
  structure VK = CValueK

  type mutable_state = {
      frm_alloc : Label.t -> Frame.t,
      count_lvar_alloc : int LVar.Tbl.hash_table,
      count_lam_alloc : int Label.Tbl.hash_table,
      a_alloc : unit -> A.t,
      aK_alloc : unit -> AK.t,
      d_alloc : VB.t * Frame.Set.set -> V.t,
      dK_alloc : VKB.t * Frame.Set.set -> VK.t,
      memo : CLive.t,
      frm_bindingAlloc : (CBinding.t list) Frame.Tbl.hash_table, 
      frm_ldataAlloc : (V.t list) Frame.Tbl.hash_table, 
      frm_live : bool Frame.Tbl.hash_table,
      expsSeen : LS.set ref,
      lvarsBound : LVS.set ref
  }

  type state = C.exp * CEnv.t * CStore.t * CEnvK.t * CStoreK.t * (Frame.t list) * (Frame.t list)

  fun literalToValueBase lit =
      (case lit
        of Literal.Int int_lit => VB.INT (IntInf.toInt int_lit)
         | Literal.Word word_lit => VB.WORD (Word.fromInt (IntInf.toInt word_lit))
         | Literal.Real float_lit => VB.FLOAT (valOf (Real.fromString (FloatLit.toString float_lit)))
         | Literal.Char c => VB.CHAR c
         | Literal.String s => VB.STRING s
      (* end case *))

  fun literalToValue (mutable_state : mutable_state) (lit, lexFrms) =
      (#d_alloc mutable_state) (literalToValueBase lit, Frame.Set.fromList lexFrms)

  (* The helper function for evaluating (user) atoms *)
  fun evalAtom (mutable_state : mutable_state) (lab_e, ae, env, store, lexFrms) =
      (case ae
        of C.LVAR (x, _) => CStore.lookup (store, CEnv.lookup (env, x))
         | C.LIT(lit, _) => literalToValue mutable_state (lit, lexFrms)
         | C.DCON(dcon, _) => (#d_alloc mutable_state) (VB.DATA (lab_e, dcon, NONE), Frame.Set.fromList lexFrms)
         | C.UNIT => (#d_alloc mutable_state) (VB.UNIT, Frame.Set.fromList lexFrms)
      (* end case *))

  fun evalLVar (x, env, store) =
      CStore.lookup (store, CEnv.lookup (env, x))

  fun evalCVar (k, envK, storeK) =
      CStoreK.lookup (storeK, (CEnvK.lookup (envK, k)))

  (* A helper function for extending the various environments and stores *)
  fun extendMaps (x : LVar.t, a : A.t, d : V.t, env : CEnv.t, store : CStore.t) =
      (CEnv.extend (env, x, a), CStore.extend (store, a, d))

  (* A helper function for extending the various continuation environments and stores *)
  fun extendMapsK (k : CVar.t, aK : AK.t, dK : VK.t, envK : CEnvK.t, storeK : CStoreK.t) =
      (CEnvK.extend (envK, k, aK), CStoreK.extend (storeK, aK, dK))

  (* most primops follow a pattern (for example, do not touch the store)
   * this exception is to handle the non-standard ones
   *)
  exception ExceptionalPrim of V.t * CStore.t

  fun primFail prim_str d_args =
      raise Fail(String.concat ["bad primop: ", prim_str, " with ", Int.toString (List.length d_args), " args: ", String.concatWithMap "" CValue.toString d_args])

  fun unhandledPrim prim_str d_args =
      raise Fail(String.concat ["knowingly unhandled primop: ", prim_str, " with ", Int.toString (List.length d_args), " args"])

  fun evalPurePrim (mutable_state : mutable_state) (oper, d_args, store, lexFrms) = let
      val a_alloc = #a_alloc mutable_state
      val d_alloc = #d_alloc mutable_state
      val memo = #memo mutable_state
      val d = (case (oper, List.map V.base d_args)
	   of (P.Pure.NumOp(rator, _), args) => (case (rator, args)
		 of (P.Pure.FAdd, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (x1 + x2)
		  | (P.Pure.FSub, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (x1 - x2)
		  | (P.Pure.FMul, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (x1 * x2)
		  | (P.Pure.FDiv, [VB.FLOAT x1, VB.FLOAT x2]) => VB.FLOAT (x1 / x2)
		  | (P.Pure.FNeg, [VB.FLOAT x]) => VB.FLOAT (~ x)
                  | _ => primFail (P.Pure.toString oper) d_args
		(* end case *))
            | (P.Pure.IntToReal _, [VB.INT i]) => VB.FLOAT (real i)
            (* QUESTION: are these the correct sml functions to use for these primops *)
            | (P.Pure.ZExt _, [VB.CHAR c]) => VB.INT (Char.ord c)
            | (P.Pure.CharToStr, [VB.CHAR c]) => VB.STRING (Char.toString c)
            | (P.Pure.StrSize, [VB.STRING s]) => VB.INT (String.size s)
            | (P.Pure.Implode, [arg]) => unhandledPrim (P.Pure.toString P.Pure.Implode) [arg]
            | (P.Pure.SAppend, [VB.STRING s1, VB.STRING s2]) => VB.STRING (s1 ^ s2)
            | (P.Pure.Ref, [_]) => let
                val a = a_alloc ()
                val d = d_alloc (VB.REF a, Frame.Set.fromList lexFrms)
                val store' = CStore.extend(store, a, hd(d_args))
                val _ = CLive.add_a (memo, store', [a])
		in
		  raise ExceptionalPrim (d, store')
		end
            | (P.Pure.Array0, []) => let
                val d = d_alloc (VB.ARRAY [], Frame.Set.fromList lexFrms)
		in
		  raise ExceptionalPrim (d, store)
		end
            | (P.Pure.ArrayAlloc, [VB.INT size, _]) => let
                val addrs = List.tabulate (size, (fn _ => a_alloc ()))
                val d_init = List.nth (d_args, 1)
                val d = d_alloc (VB.ARRAY addrs, Frame.Set.fromList lexFrms)
                val store' = List.foldl
		      (fn (a, store) => CStore.extend(store, a, d_init))
			store addrs
		in
		  raise ExceptionalPrim (d, store')
		end
            | (P.Pure.ArrayLength, [VB.ARRAY addrs]) => VB.INT (List.length addrs)
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
	  (* end case *))
      in
	(d_alloc (d, Frame.Set.fromList lexFrms), store)
      end
	handle (ExceptionalPrim x) => x

  (* assuming no overflow; the main body will catch it if it occurs *)
  fun evalArithPrim (mutable_state : mutable_state) (oper, d_args, lexFrms) = let
      val d_alloc = #d_alloc mutable_state
      val d = (case (oper, List.map V.base d_args)
	   of (P.IntOp(rator, _), args) => (case (rator, args)
		 of (P.Arith.IAdd, [VB.INT i1, VB.INT i2]) => VB.INT (i1 + i2)
		  | (P.Arith.ISub, [VB.INT i1, VB.INT i2]) => VB.INT (i1 - i2)
		  | (P.Arith.IMul, [VB.INT i1, VB.INT i2]) => VB.INT (i1 * i2)
		  | (P.Arith.IDiv, [VB.INT i1, VB.INT i2]) => VB.INT (i1 div i2)
		  | (P.Arith.IMod, [VB.INT i1, VB.INT i2]) => VB.INT (i1 mod i2)
		  | (P.Arith.INeg, [VB.INT i]) => VB.INT (~ i)
		  | _ => primFail (P.Arith.toString oper) d_args
		(* end case *))
            | (P.Arith.Floor _, [VB.FLOAT x]) => VB.INT (floor x)
            | (P.Arith.StrSub, [VB.STRING s, VB.INT i]) => VB.CHAR (String.sub (s, i))
            | _ => primFail (P.Arith.toString oper) d_args
	  (* end case *))
      in
	d_alloc (d, Frame.Set.fromList lexFrms)
      end

  fun evalGetPrim (mutable_state : mutable_state) (oper, d_args, store) =
      case (oper, List.map V.base d_args)
       of (P.Getter.Deref, [VB.REF a]) => CStore.lookup (store, a)
        | (P.Getter.ArraySub, [VB.ARRAY addrs, VB.INT index]) => let
            val a = List.nth (addrs, index)
                    handle Subscript =>
                           raise Fail ((Int.toString (List.length addrs)) ^ " " ^ (Int.toString index))
        in CStore.lookup (store, a) end
        | _ => primFail (P.Getter.toString oper) d_args

  fun evalSetPrim (mutable_state : mutable_state) (oper, d_args, store, lexFrms) = let
      val d_alloc = #d_alloc mutable_state
      val memo = #memo mutable_state
  in
      case (oper, List.map V.base d_args)
       of (P.Setter.Assign, [VB.REF a, _]) => let
           val _ = CLive.reset memo
       in (d_alloc (VB.UNIT, Frame.Set.fromList lexFrms), CStore.extend(store, a, hd(tl(d_args)))) end
        | (P.Setter.ArrayUpdate, [VB.ARRAY addrs, VB.INT index, _]) => let
            val _ = CLive.reset memo
            val a = List.nth (addrs, index)
                    handle Subscript =>
                           raise Fail ((Int.toString (List.length addrs)) ^ " " ^ (Int.toString index))
        in (d_alloc (VB.UNIT, Frame.Set.fromList lexFrms), CStore.extend(store, a, List.nth (d_args, 2))) end
        | (P.Setter.Print, [VB.STRING s]) => (d_alloc (VB.UNIT, Frame.Set.fromList lexFrms), store)
        | _ => primFail (P.Setter.toString oper) d_args
  end

  fun poly_equal (d1, d2, store) = (case (d1, d2)
	 of (VB.CLO clo1, VB.CLO clo2) => raise Fail "passed closures to poly_equal"
	  | (VB.CLO _, _) => raise Fail "passed closures to poly_equal"
	  | (_, VB.CLO _) => raise Fail "passed closures to poly_equal"
	  | (VB.DATA (_, dc1, a1o), VB.DATA (_, dc2, a2o)) =>
	    (case (CPSDataCon.compare (dc1, dc2), a1o, a2o)
	      of (EQUAL, SOME a1, SOME a2) =>
		 poly_equal (V.base (CStore.lookup (store, a1)),
			     V.base (CStore.lookup (store, a2)),
			     store)
	       | (EQUAL, NONE, NONE) => true
	       | _ => false)
	  | (VB.DATA _, _) => raise Fail "different types passed to poly_equal"
	  | (_, VB.DATA _) => raise Fail "different types passed to poly_equal"
	  | (VB.REF r1, VB.REF r2) => CAddr.same (r1, r2)
	  | (VB.REF _, _) => raise Fail "different types passed to poly_equal"
	  | (_, VB.REF _) => raise Fail "different types passed to poly_equal"
	  | (VB.ARRAY arr1, VB.ARRAY arr2) => ListPair.all CAddr.same (arr1, arr2)
	  | (VB.ARRAY _, _) => raise Fail "different types passed to poly_equal"
	  | (_, VB.ARRAY _) => raise Fail "different types passed to poly_equal"
	  | (VB.TUPLE (_, t1), VB.TUPLE (_, t2)) =>
	    ListPair.all
		(fn (a1, a2) =>
		    poly_equal (V.base (CStore.lookup (store, a1)),
				V.base (CStore.lookup (store, a2)),
				store))
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
	(* end case *))

  fun evalTestPrim (oper, d_args, store) = (
        case (oper, List.map V.base d_args)
	 of (P.ICmp(P.Test.ILt, _), [VB.INT i1, VB.INT i2]) => i1 < i2
	  | (P.ICmp(P.Test.ILte, _), [VB.INT i1, VB.INT i2]) => i1 <= i2
	  | (P.ICmp(P.Test.IEq, _), [VB.INT i1, VB.INT i2]) => i1 = i2
	  | (P.ICmp(P.Test.INEq, _), [VB.INT i1, VB.INT i2]) => i1 <> i2
	  | (P.ICmp(P.Test.IGte, _), [VB.INT i1, VB.INT i2]) => i1 >= i2
	  | (P.ICmp(P.Test.IGt, _), [VB.INT i1, VB.INT i2]) => i1 > i2

	  | (P.ICmp(P.Test.ULt, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 < c2
	  | (P.ICmp(P.Test.ULte, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 <= c2
	  | (P.ICmp(P.Test.IEq, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 = c2
	  | (P.ICmp(P.Test.INEq, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 <> c2
	  | (P.ICmp(P.Test.UGte, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 >= c2
	  | (P.ICmp(P.Test.UGt, 8), [VB.CHAR c1, VB.CHAR c2]) => c1 > c2

	  | (P.FCmp(P.Test.FLt, _), [VB.FLOAT x1, VB.FLOAT x2]) => x1 < x2
	  | (P.FCmp(P.Test.FLte, _), [VB.FLOAT x1, VB.FLOAT x2]) => x1 <= x2
	  | (P.FCmp(P.Test.FEq, _), [VB.FLOAT x1, VB.FLOAT x2]) => Real.== (x1, x2)
	  | (P.FCmp(P.Test.FNEq, _), [VB.FLOAT x1, VB.FLOAT x2]) => not (Real.== (x1, x2))
	  | (P.FCmp(P.Test.FGte, _), [VB.FLOAT x1, VB.FLOAT x2]) => x1 >= x2
	  | (P.FCmp(P.Test.FGt, _), [VB.FLOAT x1, VB.FLOAT x2]) => x1 > x2

	  | (P.SLt, [VB.STRING s1, VB.STRING s2]) => s1 < s2
	  | (P.SLte, [VB.STRING s1, VB.STRING s2]) => s1 <= s2
	  | (P.SEq, [VB.STRING s1, VB.STRING s2]) => s1 = s2
	  | (P.SNEq, [VB.STRING s1, VB.STRING s2]) => s1 <> s2
	  | (P.SGte, [VB.STRING s1, VB.STRING s2]) => s1 >= s2
	  | (P.SGt, [VB.STRING s1, VB.STRING s2]) => s1 > s2

                                                              (*
        | (P.Test, [VB.DATA (dcon, ao)]) =>
          if (substring (CDataValue.toString (dcon, ao), 0, 8)) = "(dv true"
          then true
          else if (substring (CDataValue.toString (dcon, ao), 0, 9)) = "(dv false"
          then false
          else primFail (P.Test.toString oper) d_args
        | _ => primFail (P.Test.toString oper) d_args
        *)
	  | (P.PolyEq, [d1, d2]) => poly_equal (d1, d2, store)
	  | (P.PolyNEq, [d1, d2]) => not (poly_equal (d1, d2, store))
	  | (P.PtrEq, [VB.ARRAY addrs1, VB.ARRAY addrs2]) =>
	    (case List.collate CAddr.compare (addrs1, addrs2)
	      of EQUAL => true
	       | _ => false)
	  | (P.PtrEq, [VB.REF a1, VB.REF a2]) =>
	    (case CAddr.compare (a1, a2)
	      of EQUAL => true
	       | _ => false)
	  | _ => primFail (P.Test.toString oper) d_args
	(* end case *))

  fun update_frm_bindingAlloc (frm_bindingAlloc, lexFrms, new_bindings) =
      List.app (fn frm => Frame.Tbl.insert frm_bindingAlloc (frm, new_bindings @ (Frame.Tbl.lookup frm_bindingAlloc frm)))
               lexFrms

  fun update_frm_ldataAlloc (frm_ldataAlloc, lexFrms, new_values) =
      List.app (fn frm => Frame.Tbl.insert frm_ldataAlloc (frm, new_values @ (Frame.Tbl.lookup frm_ldataAlloc frm)))
               lexFrms

  fun popFrms (popTos : Frame.t list, wholeStack : Frame.t list) : (Frame.t list) * (Frame.t list) = let
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

end
