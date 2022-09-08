(* transition-util.sml
 *
 * Util functions for the state space transitions.
 *)

(* FIXME: needs signature *)

structure TransitionUtil = struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LM = Label.Map

  structure PInfo = CPSInformation
  structure P = PrimOp

  fun removeScheme (CPSTypes.TyScheme (_, ty)) = ty

  fun instantiateTy (tenv, ty) =
      case ty
       of CPSTypes.VarTy xty =>
          (case TEnv.find (tenv, xty)
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
          val tenv = TEnv.extend (tenv, xty, instantiateTy (tenv, ty_hint))
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
               (case TEnv.find (tenv, xty)
                 of NONE => SOME (TEnv.extend (tenv, xty, ty2))
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
  fun unifyAndExtend (tenv, ty_src, ty_dst) : TEnv.t option =
      unify (ty_dst, ty_src, SOME tenv)

  fun unifyCont (tenv, cty_src, cty_dst) =
      unify_c (cty_src, cty_dst, SOME tenv)

  (* allocate an abstract address *)
  fun alloc (x, tenv, aP) = Addr.alloc (x, aP)
  (* allocate an abstract continuation address *)
  fun allocK (x, tenv, aP) = AddrK.alloc (x, aP)
  (* allocate an abstract proxy address *)
  fun allocP (l, tenv', e, tenv) = AddrProxy.alloc (l, (tenv', e, tenv))

  (* The helper function for evaluating variables *)
  fun evalLVar (x : LVar.t, env, store) =
      Store.lookup (store, Env.lookup (env, x))

  (* The helper function for evaluating variables *)
  fun evalLVar_add (add_a, x : LVar.t, env, store) = let
      val a = Env.lookup (env, x)
      val () = add_a a
  in Store.lookup (store, a) end

  (* The helper functino for evaluating continuation variables *)
  fun evalCVar (k : CVar.t, envK, storeK) =
      StoreK.lookup (storeK, (EnvK.lookup (envK, k)))

  (* create a closure from a user lambda.
     Takes only the necessary bindings from the given environment. *)
  fun evalLam pinfo (lam, env, tenv) = let
      val env = LVS.foldl (fn (x, env') => Env.extend (env', x, Env.lookup (env, x)))
                          Env.empty (PInfo.fv_lam_lv pinfo (CU.labelOfLambda lam))
  in Value.add_clo (Value.empty (CPSTypes.FunTy ([], [])) (* TODO *), Clo.make (lam, env, tenv)) end

  (* create a continuation closure from a continuation lambda.
     Takes only the necessary bindings from the given environment. *)
  fun evalLamK pinfo (lamK, env, envK, tenv) = let
      val env = LVS.foldl (fn (x, env') => Env.extend (env', x, Env.lookup (env, x)))
                          Env.empty (PInfo.fv_lamK_lv pinfo (CU.labelOfCLambda lamK))
      val envK = CVS.foldl (fn (k, envK') => EnvK.extend (envK', k, EnvK.lookup (envK, k)))
                           EnvK.empty (PInfo.fv_lamK_cv pinfo (CU.labelOfCLambda lamK))
  in ValueK.from_cloK (CloK.make (lamK, env, envK, tenv)) end

  (* The helper function for evaluating atoms. *)
  fun evalAtom (lab_e, add_a, ae : C.atom, env, store) =
      (case ae
        of C.LVAR (x, _) => evalLVar_add (add_a, x, env, store)
         | C.LIT (Literal.Int _, ty) => Value.empty (ty) (* TODO *)
         | C.LIT (Literal.Word _, ty) => Value.empty (ty) (* TODO *)
         | C.LIT (Literal.Real _, ty) => Value.empty (ty) (* TODO *)
         | C.LIT (Literal.Char _, ty) => Value.empty (ty) (* TODO *)
         | C.LIT (Literal.String _, ty) => Value.empty (ty) (* TODO *)
         | C.DCON(dcon, _) => Value.add_dv (Value.empty (CPSTypes.ConTy ([], let val CPSTypes.DCon record = dcon in #owner record end)) (* TODO *),
                                            DataValue.make (lab_e, dcon, NONE))
         | C.UNIT => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.unitTyc)) (* TODO *)
      (* end case *))

  structure AP_Indices =
  struct
    type t = AddrProxy.t * (int list)
    fun compare ((aP1, lst1) : t, (aP2, lst2) : t) =
        case List.collate Int.compare (lst1, lst2)
         of EQUAL => AddrProxy.compare (aP1, aP2)
          | ord => ord
    fun same ((aP1, lst1) : t, (aP2, lst2) : t) =
        AddrProxy.same (aP1, aP2) andalso lst1 = lst2
    fun hash (aP, lst) =
        AddrProxy.hash aP
    local
        structure Key = struct type ord_key = t val compare = compare end
        structure HashKey = struct type hash_key = t val sameKey = same val hashVal = hash end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure Tbl = HashTableFn (HashKey)
    end
  end

  structure AP_Index =
  struct
    type t = AddrProxy.t * int
    fun compare ((aP1, index1), (aP2, index2)) =
        case Int.compare (index1, index2)
         of EQUAL => AddrProxy.compare (aP1, aP2)
          | ord => ord
    local
        structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end
  end

  fun select (indices, dKs) =
      List.map (fn index => List.nth (dKs, index)) indices

  fun valueK_isCloK dK =
      case dK
       of ValueK.CLOK _ => true
        | _ => false

  fun valueK_indexOf (dK) =
      (case dK
        of ValueK.INDEX index => index
         | _ => raise Fail "valueK_indexOf")

  fun valueK_cloKOf (dK) =
      (case dK
        of ValueK.CLOK cloKs => cloKs
         | _ => raise Fail "valueK_cloKOf")

  fun proxy_add_wl add_aP (pair, wl, seen) =
      if AP_Indices.Set.member (seen, pair)
      then (wl, seen)
      else (add_aP pair; (pair :: wl, AP_Indices.Set.add (seen, pair)))

  fun proxy_add_wl_single add_aP (pair, wl, seen) =
      if AP_Index.Set.member (seen, pair)
      then (wl, seen)
      else (add_aP (#1 pair, [#2 pair]); (pair :: wl, AP_Index.Set.add (seen, pair)))

  (* TODO:DOC *)
  fun poppedProxies_wl (initial, storeP) = let
      fun do_wl (wl, seen, acc) =
          (case wl
            of [] => acc
             | ((aP, indices) :: wl) => let
                 fun handle_proxy (proxy, (wl, seen, acc)) = let
                     val (e, dKs, aP) = Proxy.get proxy
                     val dKs = select (indices, dKs)
                 in if List.exists valueK_isCloK dKs
                    then (wl, seen, acc)
                    else let
                        val (wl, seen) = proxy_add_wl (fn _ => ()) ((aP, List.map valueK_indexOf dKs), wl, seen)
                    in (wl, seen, Label.Set.add (acc, CU.labelOfExp e)) end
                 end
                 val dP = StoreProxy.lookup (storeP, aP)
                 val acc = ValueProxy.fold_proxy handle_proxy (wl, seen, acc) dP
             in do_wl acc end)
  in do_wl initial end

  (* TODO:DOC *)
  fun poppedProxies_wl_single (initial, storeP) = let
      fun do_wl (wl, seen, acc) =
          (case wl
            of [] => acc
             | ((aP, index) :: wl) => let
                 fun handle_proxy (proxy, (wl, seen, acc)) = let
                     val (e, dKs, aP) = Proxy.get proxy
                     val dK = List.nth (dKs, index)
                 in if valueK_isCloK dK
                    then (wl, seen, acc)
                    else let
                        val (wl, seen) = proxy_add_wl_single (fn _ => ()) ((aP, valueK_indexOf dK), wl, seen)
                    in (wl, seen, Label.Set.add (acc, CU.labelOfExp e)) end
                 end
                 val dP = StoreProxy.lookup (storeP, aP)
                 val acc = ValueProxy.fold_proxy handle_proxy (wl, seen, acc) dP
             in do_wl acc end)
  in do_wl initial end

  (* TODO:DOC *)
  fun poppedProxies (proxy0, storeP) = let
      val (_, dKs0, aP0) = proxy0
      val (wl, seen, acc) = ([], AP_Indices.Set.empty, Label.Set.empty)
      val initial =
          if List.exists valueK_isCloK dKs0
          then (wl, seen, acc)
          else let
              val (wl, seen) = proxy_add_wl (fn _ => ()) ((aP0, List.map valueK_indexOf dKs0), wl, seen)
          in (wl, seen, Label.Set.add (acc, CU.labelOfExp (#1 proxy0))) end
  in poppedProxies_wl (initial, storeP) end

  (* TODO:DOC *)
  fun poppedProxies_valueK (dK, aP, storeP) = let
      val wl = []
      val seen = AP_Index.Set.empty
      val acc = Label.Set.empty
      val initial =
          case dK
           of ValueK.CLOK cloKs => (wl, seen, acc)
            | ValueK.INDEX index => let
                val dP = StoreProxy.lookup (storeP, aP)
                fun handle_proxy (proxy, (wl, seen, acc)) = let
                    val (e, dKs, aP) = Proxy.get proxy
                    val dK = List.nth (dKs, index)
                in if valueK_isCloK dK
                   then (wl, seen, acc)
                   else let
                       val (wl, seen) = proxy_add_wl_single (fn _ => ()) ((aP, valueK_indexOf dK), wl, seen)
                   in (wl, seen, Label.Set.add (acc, CU.labelOfExp e)) end
                end
            in ValueProxy.fold_proxy handle_proxy (wl, seen, acc) dP end
  in poppedProxies_wl_single (initial, storeP) end

  (* TODO:DOC *)
  fun popProxies_wl (add_aP, wl, seen, acc, any_unknown, storeP) = let
      fun do_wl (wl, seen, acc, any_unknown) =
          (case wl
            of [] => (acc, any_unknown)
             | ((aP, indices) :: wl) => let
                 fun handle_proxy (proxy, (wl, seen, acc)) = let
                     val (e, dKs, aP) = Proxy.get proxy
                     val dKs = select (indices, dKs)
                     val proxy = Proxy.make (e, dKs, aP)
                 in if List.exists valueK_isCloK dKs
                    then (wl, seen, Proxy.Set.add (acc, proxy)) (* update the proxy *)
                    else let
                        val (wl, seen) = proxy_add_wl add_aP ((aP, List.map valueK_indexOf dKs), wl, seen)
                    in (wl, seen, acc) end
                 end
                 val dP = StoreProxy.lookup (storeP, aP)
                 val (wl, seen, acc) = ValueProxy.fold_proxy handle_proxy (wl, seen, acc) dP
                 val any_unknown = any_unknown orelse ValueProxy.isUnknown dP
             in do_wl (wl, seen, acc, any_unknown) end)
  in do_wl (wl, seen, acc, any_unknown) end

  (* TODO:DOC *)
  fun popProxies_indices (add_aP, dP0, indices0, storeP) = let
      fun handle_proxy (proxy, (wl, seen, acc)) = let
          val (e, dKs, aP) = Proxy.get proxy
          val dKs = select (indices0, dKs)
          val proxy = Proxy.make (e, dKs, aP)
      in if List.exists valueK_isCloK dKs
         then (wl, seen, Proxy.Set.add (acc, proxy)) (* update the proxy *)
         else let
             val (wl, seen) = proxy_add_wl add_aP ((aP, List.map valueK_indexOf dKs), wl, seen)
         in (wl, seen, acc) end
      end
      val (wl, seen, acc) =
          ValueProxy.fold_proxy handle_proxy ([], AP_Indices.Set.empty, Proxy.Set.empty) dP0
      val any_unknown = ValueProxy.isUnknown dP0
  in popProxies_wl (add_aP, wl, seen, acc, any_unknown, storeP) end

  (* TODO:DOC *)
  fun popProxies (add_aP, proxy0, storeP) = let
      val (e0, dKs0, aP0) = Proxy.get proxy0
  in if List.exists valueK_isCloK dKs0
     then (Proxy.Set.singleton proxy0, false)
     else let
         val (wl, seen) =
             proxy_add_wl add_aP ((aP0, List.map valueK_indexOf dKs0), [], AP_Indices.Set.empty)
     in popProxies_wl (add_aP, wl, seen, Proxy.Set.empty, false, storeP) end
  end

  (* TODO:DOC *)
  fun cloKOf_wl (add_aP, wl, seen, acc, any_unknown, storeP)
      : ((CloK.t * AddrProxy.t) list * bool) = let
      fun do_wl (wl, seen, acc, any_unknown) =
          (case wl
            of [] => (acc, any_unknown)
             | ((aP, index) :: wl) => let
                 val dP = StoreProxy.lookup (storeP, aP)
                 fun handle_proxy (proxy, (wl, seen, acc)) = let
                     val (e, dKs, aP) = Proxy.get proxy
                     val dK = List.nth (dKs, index)
                 in
                     if valueK_isCloK dK
                     then let
                         val cloKs = (valueK_cloKOf dK)
                         fun add_cloK (cloK, acc) = (cloK, aP) :: acc
                         val acc = CloK.Set.foldl add_cloK acc cloKs
                     in (wl, seen, acc) end
                     else let
                         val (wl, seen) = proxy_add_wl_single add_aP ((aP, valueK_indexOf dK), wl, seen)
                     in (wl, seen, acc) end
                 end
                 val (wl, seen, acc) = ValueProxy.fold_proxy handle_proxy (wl, seen, acc) dP
                 val any_unknown = any_unknown orelse ValueProxy.isUnknown dP
             in do_wl (wl, seen, acc, any_unknown) end)
  in do_wl (wl, seen, acc, any_unknown) end

  (* TODO:DOC *)
  fun cloKOf_index (add_aP, dP0, index0, storeP) = let
      fun handle_proxy (proxy, (wl, seen, acc)) = let
          val (e, dKs, aP) = Proxy.get proxy
          val dK = List.nth (dKs, index0)
      in
          if valueK_isCloK dK
          then let
              val cloKs = (valueK_cloKOf dK)
              fun add_cloK (cloK, acc) = (cloK, aP) :: acc
              val acc = CloK.Set.foldl add_cloK acc cloKs
          in (wl, seen, acc) end
          else let
              val (wl, seen) = proxy_add_wl_single add_aP ((aP, valueK_indexOf dK), wl, seen)
          in (wl, seen, acc) end
      end
      val (wl, seen, acc) = ValueProxy.fold_proxy handle_proxy ([], AP_Index.Set.empty, []) dP0
      val any_unknown = ValueProxy.isUnknown dP0
  in cloKOf_wl (add_aP, wl, seen, acc, any_unknown, storeP) end

  (* TODO:DOC *)
  fun cloKOf (add_aP, dK, aP, storeP) =
      if valueK_isCloK dK
      then let
          val cloKs = (valueK_cloKOf dK)
          fun add_cloK (cloK, acc) = (cloK, aP) :: acc
          val acc = CloK.Set.foldl add_cloK [] cloKs
      in (acc, false) end
      else let
          val index = valueK_indexOf dK
          val (wl, seen) = proxy_add_wl_single add_aP ((aP, index), [], AP_Index.Set.empty)
     in cloKOf_wl (add_aP, wl, seen, [], false, storeP) end

  (* Used as control flow for primops that have non-standard behavior.
     Currently only used for ref allocations. *)
  exception ExceptionalPrim of Value.t * (Addr.t * Value.t) list

  (* Used to signal that an unknown primop, or a primop with a bad
     number of arguments, was seen in the CPS. *)
  fun primFail (prim_str : string) (args : Value.t list) =
      raise Fail(String.concat ["bad primop: ", prim_str, " with ", Int.toString (List.length args), " args"])

  (* The helper function for Pure primops.
     Takes the side_effect_table, label of the primop expression, and
     store to extend in case of the possibility of allocating ref
     cells. Returns a possibly extended store and the value of the
     primop application. *)
  fun performPurePrim (sideEffectVars : LVar.t Label.Map.map, l : Label.t,
                       oper : P.Pure.t, args : Value.t list,
                       tenv : TEnv.t, aP : AddrProxy.t,
                       store_exts : (Addr.t * Value.t) list)
      : Value.t * (Addr.t * Value.t) list = let
      val d = (case (oper, args)
           of (P.Pure.NumOp(rator, _), _) => (case rator
                 of P.Pure.FAdd => Value.empty(CPSTypes.ConTy([], CPSPrimTy.realTyc)) (* TODO *)
                  | P.Pure.FSub => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
                  | P.Pure.FMul => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
                  | P.Pure.FDiv => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
                  | P.Pure.FNeg => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
                  | _ => primFail (P.Pure.toString oper) args
                (* end case *))
            | (P.Pure.ZExt _, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
            | (P.Pure.SExt _, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
            | (P.Pure.Trunc _, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
            | (P.Pure.IntToReal _, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
            | (P.Pure.StrSize, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
            | (P.Pure.CharToStr, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.stringTyc)) (* TODO *)
            | (P.Pure.SAppend, [arg1, arg2]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.stringTyc)) (* TODO *)
            | (P.Pure.Implode, [arg]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.stringTyc)) (* FIXME; no list type in prim! TODO *)
            | (P.Pure.Ref, [d]) => let
                val x_ref = LM.lookup (sideEffectVars, l)
                val a = alloc (x_ref, tenv, aP)
                val d_ref = Value.add_ref (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.refTyc)) (* TODO *), a)
                val store_exts =  (a, d) :: store_exts
                in
                  raise ExceptionalPrim (d_ref, store_exts)
                end
            | (P.Pure.Array0, []) => let
                val _ = raise Fail "cannot handle Array0"
                val x_arr = LM.lookup (sideEffectVars, l)
                val a = alloc (x_arr, tenv, aP)
                val d_arr = Value.add_arr (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.arrayTyc)) (* TODO *), a)
                val store_exts = (* TODO *) store_exts (* the array is empty, so there shouldn't be anything here *)
                in
                  raise ExceptionalPrim (d_arr, store_exts)
                end
            | (P.Pure.ArrayAlloc, [size, init]) => let
                val x_arr = LM.lookup (sideEffectVars, l)
                val a = alloc (x_arr, tenv, aP)
                val d_arr = Value.add_arr (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.arrayTyc)) (* TODO *), a)
                val store_exts = (a, init) :: store_exts
                in
                  raise ExceptionalPrim (d_arr, store_exts)
                end
            | (P.Pure.ArrayLength, [_]) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
            | (P.Pure.MathOp _, _) => Value.empty (CPSTypes.ConTy ([], CPSPrimTy.realTyc)) (* TODO *)
            | _ => primFail (P.Pure.toString oper) args
          (* end case *))
  in (d, store_exts) end handle (ExceptionalPrim z) => z

  (* The helper function for Arith primops.
     Returns the result of applying the primop. *)
  fun performArithPrim (oper : P.Arith.t, args : Value.t list) : Value.t = (
        case (oper, args)
         of (P.Arith.IntOp _, _) =>
            Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
          | (P.Arith.Floor _, [_]) =>
            Value.empty (CPSTypes.ConTy ([], CPSPrimTy.intTyc)) (* TODO *)
          | (P.Arith.StrSub, [_, _]) => 
            Value.empty (CPSTypes.ConTy ([], CPSPrimTy.charTyc)) (* TODO *)
          | _ => primFail (P.Arith.toString oper) args
        (* end case *))

  (* The helper function for Get primops.
     Takes a function f which addresses are applied to to obtain a
     value. Returns the result of applying the primop. *)
  fun performGetPrim (f : Addr.t * 'a -> 'a) base (oper : P.Getter.t, args : Value.t list) : 'a =
      case (oper, args)
       of (P.Getter.Deref, [d_ref]) => let
           val base = Value.fold_refs (fn (a, base) => f (a, base)) base d_ref
       in base end
        | (P.Getter.ArraySub, [d_array, _]) => let
            val base = Value.fold_arrs (fn ((_, a_mem), base) => f (a_mem, base)) base d_array
        in base end
        | _ => primFail (P.Getter.toString oper) args

  (* The helper function for Get primops.
     Takes a store to extend, and returns the result of applying the
     primop, any values that were passed to the unknown, as well as
     the possibly extended store. *)
  fun performSetPrim (oper : P.Setter.t, args : Value.t list, store_exts : (Addr.t * Value.t) list) : Value.t * Value.t list * (Addr.t * Value.t) list =
      case (oper, args)
       of (P.Setter.Assign, [d_ref, d]) => let
           fun extend (a, store_exts) = (a, d) :: store_exts
           val store_exts = Value.fold_refs extend store_exts d_ref
           val passed_to_unknown = Value.fold_unknown (fn acc => d :: acc) [] d_ref
       in (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.unitTyc)) (* TODO *), passed_to_unknown, store_exts) end
       | (P.Setter.ArrayUpdate, [d_array, _, d]) => let
           fun extend ((_, a), store_exts) = (a, d) :: store_exts
           val store_exts = Value.fold_arrs extend store_exts d_array
           val passed_to_unknown = Value.fold_unknown (fn acc => d :: acc) [] d_array
       in (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.unitTyc)) (* TODO *), passed_to_unknown, store_exts) end
        | (P.Setter.Print, [arg]) => (Value.empty (CPSTypes.ConTy ([], CPSPrimTy.unitTyc)) (* TODO *), [], store_exts)
        | _ => primFail (P.Setter.toString oper) args

end
