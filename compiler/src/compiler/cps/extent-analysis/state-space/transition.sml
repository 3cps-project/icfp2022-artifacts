(* transition.sml
 *
 * Transitions an abstract state.
 *
 * Instead of completely transitioning a state, computes the next
 * possible configurations under the given stores and returns the
 * _extensions_ to the stores that occur for those transitions.
 *)

structure Transition : sig

    type ty_addrs = {a_unit : Addr.t, a_int : Addr.t, a_real : Addr.t,
                     a_char : Addr.t, a_string : Addr.t, a_word : Addr.t}
    type sideEffect_vars = LVar.t Label.Map.map
    type util_addrs = {tyAddrs : ty_addrs,
                       sideEffectVars : sideEffect_vars}

    (* new configurations *)
    type next_configs = Config.t list
    (* store extensions *)
    type store_exts = (Addr.t * Value.t) list
    (* continuation store extensions *)
    type storeK_exts = (AddrK.t * ValueK.t) list
    (* proxy store extensions *)
    type storeP_exts = (AddrProxy.t * ValueProxy.t) list

    type transitionResult = next_configs *
                            store_exts * storeK_exts * storeP_exts *
                            Value.t list * CloK.t list

    type add_a = Addr.t -> unit
    type add_aP = AddrProxy.t * (int list) -> unit

    val trans
        : CPSInformation.t * add_a * add_a * add_aP * util_addrs *
          Config.t * Store.t * StoreK.t * StoreProxy.t
          -> transitionResult

    val transUpdate_a_primary
        : CPSInformation.t * add_a * add_a * add_aP * util_addrs *
          Config.t * Store.t * StoreK.t * StoreProxy.t * Addr.t * Value.t
          -> transitionResult

    val transUpdate_a_secondary
        : CPSInformation.t * add_a * add_a * add_aP * util_addrs *
          Config.t * Store.t * StoreK.t * StoreProxy.t * Addr.t * Value.t
          -> transitionResult

    val transUpdate_aP
        : CPSInformation.t * add_a * add_a * add_aP * util_addrs *
          Config.t * Store.t * StoreK.t * StoreProxy.t * AddrProxy.t * (int list) * ValueProxy.t
          -> transitionResult

    val passed_to_unknown
        : CPSInformation.t * add_a * add_a * add_aP *
          (Value.t list) * (CloK.t list) *
          Store.t * StoreK.t * StoreProxy.t * Label.Set.set * Label.Set.set *
          (next_configs * store_exts * storeK_exts * storeP_exts)
          -> (next_configs * store_exts * storeK_exts * storeP_exts * Label.Set.set * Label.Set.set)

end = struct

  structure C = CPS
  structure U = TransitionUtil
  structure PInfo = CPSInformation

  structure LS = Label.Set
  structure AS = Addr.Set

  type ty_addrs = {a_unit : Addr.t, a_int : Addr.t, a_real : Addr.t,
                   a_char : Addr.t, a_string : Addr.t, a_word : Addr.t}
  type sideEffect_vars = LVar.t Label.Map.map
  type util_addrs = {tyAddrs : ty_addrs,
                     sideEffectVars : sideEffect_vars}
                        
  type next_configs = Config.t list
  type store_exts = (Addr.t * Value.t) list
  type storeK_exts = (AddrK.t * ValueK.t) list
  type storeP_exts = (AddrProxy.t * ValueProxy.t) list

  type transitionResult = next_configs *
                          store_exts * storeK_exts * storeP_exts *
                          Value.t list * CloK.t list

  type add_a = Addr.t -> unit
  type add_aP = AddrProxy.t * (int list) -> unit
  type side_effect_table = Addr.t Label.Map.map

  fun checkTypes (tenv, x, d) = let
      val CPSTypes.TyScheme (_, ty) = LVar.typeOf x
  in Value.join (Value.empty (U.instantiateTy (tenv, ty)), d)
     handle _ => raise Fail (String.concat ["bad check type: ", TEnv.toString tenv, " ", LVar.toString x, " ", Value.toString d]);
     ()
  end

  fun cty_toString (CPSTypes.ContTy tys) =
      "[ContTy " ^ (String.concatWithMap " " CPSTypes.toString tys) ^ "]"

  (* A single transition step. *)
  fun trans (pinfo, add_a_primary, add_a_secondary, add_aP, utilAddrs : util_addrs, xi, store, storeK, storeP) = let
      val sideEffectVars = #sideEffectVars utilAddrs
      val tyAddrs = #tyAddrs utilAddrs
      val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
  in
      case e
       of C.LETFUN (bindings, body) => let
           (* allocate the addresses which will be needed *)
           val triples = List.map (fn lam => (#1 lam, U.alloc (#1 lam, tenv, aP), lam)) bindings
           (* update the environments with the new addresses *)
           fun make_bind ((x, a, _), env) = Env.extend (env, x, a)
           val env' = List.foldl make_bind env triples
           (* use the updated environments to create closures *)
           fun make_clo ((_, a, lam), store_exts) =
               (a, U.evalLam pinfo (lam, env', tenv)) :: store_exts
           val store_exts = List.foldl make_clo [] triples
       in ([Config.make (body, env', envK, tenv, aP)], store_exts, [], [], [], []) end
        | C.LETCONT (bindingKs, body) => let
            (* allocate the addresses which will be needed *)
            val triplesK = List.map (fn lamK => (#1 lamK, U.allocK (#1 lamK, tenv, aP), lamK)) bindingKs
            (* update the environments with the new addresses *)
            fun make_bindK ((k, aK, _), envK) = EnvK.extend (envK, k, aK)
            val envK' = List.foldl make_bindK envK triplesK
            (* use the updated environments to create continuation closures *)
            fun make_cloK ((_, aK, lamK), storeK_exts) =
                (aK, (U.evalLamK pinfo (lamK, env, envK', tenv))) :: storeK_exts
            val storeK_exts = List.foldl make_cloK [] triplesK
        in ([Config.make (body, env, envK', tenv, aP)], [], storeK_exts, [], [], []) end
        | C.IF (oper, args, thn, els) => let
            (* we don't do anything fancy here; either branch could be taken *)
            (* Since the arguments are used, we don't need to track them. *)
            (* val () = List.app (add_lvar env) args *)
        in ([Config.make (thn, env, envK, tenv, aP), Config.make (els, env, envK, tenv, aP)], [], [], [], [], []) end
        | C.ATOM (arg, x, e') => let
            val d = U.evalAtom (lab_e, add_a_primary, arg, env, store)
            val a = (* case arg
                     of C.LIT (Literal.Int _, _) => #a_int tyAddrs
                      | C.LIT (Literal.Word _, _) => #a_word tyAddrs
                      | C.LIT (Literal.Real _, _) => #a_real tyAddrs
                      | C.LIT (Literal.Char _, _) => #a_char tyAddrs
                      | C.LIT (Literal.String _, _) => #a_string tyAddrs
                      | C.UNIT => #a_unit tyAddrs
                      | _ => *) U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], [(a, d)], [], [], [], []) end

        | C.PURE (oper, args, x, e') => let
            (* FIXME: we only care about tracking the arguments if the
               operator is an allocation *)
            val d_args =
                case oper
                 of PrimOp.Pure.ArrayAlloc => List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
                  | PrimOp.Pure.Array0 => List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
                  | PrimOp.Pure.Ref => List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
                  | _ => List.map (fn arg => U.evalLVar (arg, env, store)) args
            val (d, store_exts) = U.performPurePrim (sideEffectVars, lab_e, oper, d_args, tenv, aP, [])
            val a = U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], (a, d) :: store_exts, [], [], [], []) end
        | C.ARITH (oper, args, x, e', e_exn) => let
            val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
            val d = U.performArithPrim (oper, d_args)
            val a = U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP), Config.make (e_exn, env, envK, tenv, aP)], [(a, d)], [], [], [], []) end
        | C.GET (oper, args, x, e') => let
            val d_args = List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
            val a = U.alloc (x, tenv, aP)
            val store_exts = U.performGetPrim (fn (a_ref, store_exts) =>
                                                  (add_a_secondary a_ref;
                                                   case Store.find (store, a_ref)
                                                    of SOME d_get => (a, d_get) :: store_exts
                                                     | NONE => store_exts))
                                              [] (* TODO [(a, Value.empty ())] *)
                                              (oper, d_args)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], store_exts, [], [], [], []) end
        | C.SET (oper, args, x, e') => let
            val d_args = List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
            val (d, pass_to_unknown, store_exts) = U.performSetPrim (oper, d_args, [])
            val a = U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], (a, d) :: store_exts, [], [], pass_to_unknown, []) end

        | C.TUPLE (args, x, e') => let
            (* we don't need to track these lvars since the
               addresses in the tuple value will stay the same; that
               is, when the lvars update, this state does not need to.  *)
            val d_tup = Value.add_tv (Value.empty (CPSTypes.TupleTy [] (* TODO *)), TupleValue.make (lab_e, List.map (fn x => Env.lookup (env, x)) args))
            val a = U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], [(a, d_tup)], [], [], [], []) end
        | C.SELECT (offset, arg, x, e') => let
            val d_arg = U.evalLVar_add (add_a_primary, arg, env, store)
            val a = U.alloc (x, tenv, aP)
            val store_exts = Value.select_offset (fn (a_sel, store_exts) => let
                                                      val d_sel = Store.lookup (store, a_sel)
                                                  in checkTypes (tenv, x, d_sel);
                                                     add_a_secondary a_sel;
                                                     (a, d_sel) :: store_exts
                                                  end)
                                                 [] (* TODO [(a, Value.empty ())] *)
                                                 (offset, d_arg)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], store_exts, [], [], [], []) end

        | C.DCAPPLY (dcon, tys, arg, x, e') => let
            (* we don't need to track the lvar since the
               address in the data value will stay the same; that is,
               when the lvars update, this state does not need to. *)
            val d_dv = Value.add_dv (Value.empty (CPSTypes.ConTy ([], let val CPSTypes.DCon record = dcon in #owner record end)), (* TODO *)
                                     DataValue.make (lab_e, dcon, SOME (Env.lookup (env, arg))))
            val a = U.alloc (x, tenv, aP)
            val env' = Env.extend (env, x, a)
        in ([Config.make (e', env', envK, tenv, aP)], [(a, d_dv)], [], [], [], []) end
        | C.SWITCH (arg, pats) => let
            val d_arg = U.evalLVar_add (add_a_primary, arg, env, store)
            (* More precise would be to handle each dv in d_arg and 
               find the pat that it goes to, then make the transition.
               That way we could find dead code / branches. 
               However, I think most of the time all branches are used, 
               so we do the less precise thing here. *)
            (* we could also just do the analysis on the argument
               after computing the state space *)
            fun doCase ((pat, exp'), (next_configs, store_exts)) =
                (case pat
                  of C.VPAT x => let
                      val a = U.alloc (x, tenv, aP)
                      val env' = Env.extend (env, x, a)
                  in (Config.make (exp', env', envK, tenv, aP) :: next_configs, (a, d_arg) :: store_exts) end
                   | C.DCPAT(dcon, _, SOME x) => let
                       val a = U.alloc (x, tenv, aP)
                       val found_any = ref false
                       val store_exts = Value.match_dcon (fn (a_get, store_exts) =>
                                                             (found_any := true;
                                                              add_a_secondary a_get;
                                                              (a, Store.lookup (store, a_get)) :: store_exts))
                                                         ((* (a , Value.empty ()) :: TODO *) store_exts)
                                                         (dcon, d_arg)
                       val env' = Env.extend (env, x, a)
                       val next_configs =
                           if !found_any
                           then Config.make (exp', env', envK, tenv, aP) :: next_configs
                           else next_configs
                   in (next_configs, store_exts)
                   end
                   | _ => (Config.make (exp', env, envK, tenv, aP) :: next_configs, store_exts)
                (* end case *))
            val (next_configs, store_exts) = List.foldl doCase ([], []) pats
        in (next_configs, store_exts, [], [], [], []) end

        | C.APPLY (f, tys, args, argKs) => let
            val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
            val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
            (* evaluate the function value *)
            val d_f = U.evalLVar_add (add_a_primary, f, env, store)
            (* evaluate the user arguments *)
            val d_args = List.map (fn arg => U.evalLVar_add (add_a_secondary, arg, env, store)) args
            (* evaluate the continuation arguments *)
            val dK_argKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
            val proxy = Proxy.make (exp, dK_argKs, aP)
            val popProxies = U.popProxies (add_aP, proxy, storeP)
            fun handle_clo (clo, (next_configs, store_exts, storeK_exts, storeP_exts)) = let
                val (lam as (_, lam_lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
                val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
                (*
                val _ = DebugAnalysisStateSpace.run (fn say => say ["Calling ", Label.toString lam_lab, " from ", Label.toString lab_e, " with ", String.concatWithMap " " Value.toString d_args, "\n"])
                val _ = DebugAnalysisStateSpace.run (fn say => say [TEnv.toString tenv_clo, " ", CPSTypes.toString f_ty, " ", CPSTypes.toString clo_ty, "\n"])
                *)
            in
                case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                 of NONE => (next_configs, store_exts, storeK_exts, storeP_exts)
                  | SOME tenv' => let
                      (*
                      val _ = DebugAnalysisStateSpace.run (fn say => say ["calling: ", Label.toString lam_lab, " under ", TEnv.toString tenv', "\n"])
                      val _ = DebugAnalysisStateSpace.run (fn say => say ["from: ", CPSTypes.toString f_ty, " to: ", CPSTypes.toString clo_ty, "\n"])
                      val _ = DebugAnalysisStateSpace.run (fn say => say [String.concatWithMap " " Value.toString d_args, "\n"])
                      *)
                      val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                      val storeP_exts = (aP', popProxies) :: storeP_exts
                      fun extend (x, d_arg, (env, store_exts)) = let
                          val a = U.alloc (x, tenv, aP')
                      in (Env.extend (env, x, a), (a, d_arg) :: store_exts) end
                      val (env', store_exts) =
                          ListPair.foldl extend (env_clo, store_exts) (xs, d_args)
                      fun extendK (k, (envK, storeK_exts)) = let
                          val aK = U.allocK (k, tenv, aP')
                          val dK = ValueK.from_index (PInfo.k_index pinfo k)
                      in (EnvK.extend (envK, k, aK), (aK, dK) :: storeK_exts) end
                      val (envK', storeK_exts) =
                          List.foldl extendK (EnvK.empty, storeK_exts) ks
                      val next_configs = Config.make (body, env', envK', tenv', aP') :: next_configs
                  in (next_configs, store_exts, storeK_exts, storeP_exts) end
            end
            val (next_configs, store_exts, storeK_exts, storeP_exts) =
                  Value.fold_clos handle_clo ([], [], [], []) d_f
            val pass_to_unknown = Value.fold_unknown (fn acc => acc @ d_args) [] d_f
            val pass_to_unknownK = [] (* Value.fold_unknown (fn acc => acc @ dK_argKs) [] d_f *)

        in (next_configs, store_exts, storeK_exts, storeP_exts, pass_to_unknown, pass_to_unknownK) end
        | C.THROW (k, args) => let
            val k_cty = U.instantiateCTy (tenv, CVar.typeOf k)
            (* evaluate the arguments to the continuation *)
            val d_args = List.map (fn arg => U.evalLVar_add (add_a_primary, arg, env, store)) args
            (* evaluate the continuation to get a set of continuation closures *)
            val dK = U.evalCVar (k, envK, storeK)
            val (cloK_aPs, any_unknown) = U.cloKOf (add_aP, dK, aP, storeP)
            fun handle_cloK_aP ((cloK, aP'), (next_configs, store_exts)) = let
                val (lamK as (_, lamK_lab, xs, body), env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
                val cloK_ty = CPSTypes.ContTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs)
                val cloK_ty = U.instantiateCTy (tenv_cloK, cloK_ty)
                (*
                val _ = DebugAnalysisStateSpace.run (fn say => say ["CallingK ", Label.toString lamK_lab, " from ", Label.toString lab_e, " with ", String.concatWithMap " " Value.toString d_args, "\n"])
                val _ = DebugAnalysisStateSpace.run (fn say => say [TEnv.toString tenv_cloK, " ", cty_toString k_cty, " ", cty_toString cloK_ty, "\n"])
                *)
            in
                case U.unifyCont (tenv_cloK, k_cty, cloK_ty)
                 of NONE => (next_configs, store_exts)
                  | SOME _ => let
                      fun extend (x, d_arg, (env, store_exts)) = let
                          val a = U.alloc (x, tenv, aP')
                      in (Env.extend (env, x, a), (a, d_arg) :: store_exts) end
                      val (env', store_exts) =
                          ListPair.foldl extend (env_cloK, store_exts) (xs, d_args)
                      val next_configs = Config.make (body, env', envK_cloK, tenv_cloK, aP') :: next_configs
                  in (next_configs, store_exts) end
            end
            val (next_configs, store_exts) =
                List.foldl handle_cloK_aP ([], []) cloK_aPs
            val pass_to_unknown = if any_unknown then d_args else []
        in (next_configs, store_exts, [], [], pass_to_unknown, []) end
     (* end case *)
  end

  exception BadUpdate

  (* for atoms, the only update that might occur is if the RHS
     is a lvar that was updated. In that case, the update just flows to the LHS *)
  (* for pure primops, the only update that might occur is if
     the primop is allocating a ref cell. The lvar x should not 
     need to be updated *)
  (* for get primops, the updates are either
     - from the arguments, to x (i.e. a new ref cell flowed to the arg)
       In this case, we need to add the address in the new ref cell(s)
       to the update pool via add_a.
     - from the contents of the arguments to x 
       (i.e. the address within a ref cell has updated 
       since ref/array addresses are disjoint from var addresses, 
       only one of these can happend at once *)
  (* for set primops, we just treat all updates to the arguments
     as the same and so there is only one kind of update. It
     turns out that currently this will always return Value.empty. *)
  (* for select, there are two kinds of updates:
     - updates to the argument (tuple value) to select from.
       In this case, the new address(es) contained in the
       update value we are loading off of needs to be added to
       the update pool via add_a
     - updates to an address within the tuple value to get from.
       In this case, the update value is going to be the selected one. *)
  (* for switches, there are two kinds of updates:
     - updates to the argument (data value) to case on
     - updates to an address within the data value to case on. *)
  (* For function applications, there are two types of updates:
     - the function is being updated
     - an argument is being updated
     The function and arguments can't both update because that wouldn't type check *)
  (* For throws, the only update is to the arguments *)

  (* performs a transition on a single update to an address *)
  fun transUpdate_a_primary (pinfo, add_a_primary, add_a_secondary, add_aP, utilAddrs : util_addrs,
                             xi, store, storeK, storeP, a_update, d_update) = let
      val sideEffectVars = #sideEffectVars utilAddrs
      val tyAddrs = #tyAddrs utilAddrs
      val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      fun is_update_a a = Addr.same (a, a_update)
      fun eval_with_fall_through arg = let
          val a = Env.lookup (env, arg)
      in if is_update_a a
         then d_update
         else Store.lookup (store, a)
      end
  in
      case e
       of C.ATOM (arg, x, e') => let
           val a = U.alloc (x, tenv, aP)
       in ([], [(a, d_update)], [], [], [], []) end
        | C.PURE (oper, args, x, e') => let
            val d_args = List.map eval_with_fall_through args
            val (_, store_exts) = U.performPurePrim (sideEffectVars, lab_e, oper, d_args, tenv, aP, [])
        in ([], store_exts, [], [], [], []) end
        | C.GET (oper, args, x, e') => let
              val d_args = List.map eval_with_fall_through args
              val a = U.alloc (x, tenv, aP)
              val store_exts = U.performGetPrim (fn (a_ref, store_exts) =>
                                                    (add_a_secondary a_ref;
                                                     case Store.find (store, a_ref)
                                                      of SOME d_get => (a, d_get) :: store_exts
                                                       | NONE => store_exts))
                                               []
                                               (oper, d_args)
          in ([], store_exts, [], [], [], []) end
        | C.SET (oper, args, x, e') => let
            val d_args = List.map eval_with_fall_through args
            val (d, pass_to_unknown, store_exts) = U.performSetPrim (oper, d_args, [])
        in ([], store_exts, [], [], pass_to_unknown, []) end
        | C.SELECT (offset, arg, x, e') =>  let
            val a = U.alloc (x, tenv, aP)
            val store_exts = Value.select_offset (fn (a_sel, store_exts) => let
                                                      val d_sel = Store.lookup (store, a_sel)
                                                  in checkTypes (tenv, x, d_sel);
                                                     add_a_secondary a_sel;
                                                     (a, d_sel) :: store_exts
                                                  end)
                                                 []
                                                 (offset, d_update)
        in ([], store_exts, [], [], [], []) end
        | C.SWITCH (arg, pats) => let
            fun doCase ((pat, exp'), (next_configs, store_exts)) =
                (case pat
                  of C.VPAT x => let
                      val a = U.alloc (x, tenv, aP)
                  in (next_configs, (a, d_update) :: store_exts) end
                   | C.DCPAT(dcon, _, SOME x) => let
                       val a = U.alloc (x, tenv, aP)
                       val found_any = ref false
                       (* TODO: add found_any *)
                       val store_exts = Value.match_dcon (fn (a_sel, store_exts) =>
                                                             (found_any := true;
                                                              add_a_secondary a_sel;
                                                              (a, Store.lookup (store, a_sel)) :: store_exts))
                                                         store_exts
                                                         (dcon, d_update)
                       val env' = Env.extend (env, x, a)
                       val next_configs =
                           if !found_any
                           then Config.make (exp', env', envK, tenv, aP) :: next_configs
                           else next_configs
                   in (next_configs, store_exts) end
                   | _ => (next_configs, store_exts))
            val (next_configs, store_exts) = List.foldl doCase ([], []) pats
        in (next_configs, store_exts, [], [], [], []) end
        | C.APPLY (f, tys, args, argKs) => let
            val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
            val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
            val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
            val dKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
            val d_f = d_update
            val proxy = Proxy.make (exp, dKs, aP)
            val popProxies = U.popProxies (add_aP, proxy, storeP)
            fun handle_clo (clo, (next_configs, store_exts, storeK_exts, storeP_exts)) = let
                val (lam as (_, lam_lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
                val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
            in
                case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                 of NONE => (next_configs, store_exts, storeK_exts, storeP_exts)
                  | SOME tenv' => let
                      val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                      val storeP_exts = (aP', popProxies) :: storeP_exts
                      fun extend (x, d_arg, (env, store_exts)) = let
                          val a = U.alloc (x, tenv, aP')
                      in (Env.extend (env, x, a), (a, d_arg) :: store_exts) end
                      val (env', store_exts) =
                          ListPair.foldl extend (env_clo, store_exts) (xs, d_args)
                      fun extendK (k, (envK, storeK_exts)) = let
                          val aK = U.allocK (k, tenv, aP')
                          val dK = ValueK.from_index (PInfo.k_index pinfo k)
                      in (EnvK.extend (envK, k, aK), (aK, dK) :: storeK_exts) end
                      val (envK', storeK_exts) =
                          List.foldl extendK (EnvK.empty, storeK_exts) ks
                      val next_configs = Config.make (body, env', envK', tenv', aP') :: next_configs
                  in (next_configs, store_exts, storeK_exts, storeP_exts) end
            end
            val (next_configs, store_exts, storeK_exts, storeP_exts) =
                Value.fold_clos handle_clo ([], [], [], []) d_f
            val pass_to_unknown = Value.fold_unknown (fn acc => acc @ d_args) [] d_f
            val pass_to_unknownK = [] (* TODO: Value.fold_unknown (fn acc => acc @ argKs) [] d_f *)
        in (next_configs, store_exts, storeK_exts, storeP_exts, pass_to_unknown, pass_to_unknownK) end
        | C.THROW (k, args) => let
            val k_cty = U.instantiateCTy (tenv, CVar.typeOf k)
            fun find_update_indices (arg, (index, indices)) = let
                val a = Env.lookup (env, arg)
            in if is_update_a a
               then (index+1, index::indices)
               else (index+1, indices)
            end
            val (_, update_indices) = List.foldl find_update_indices (0, []) args
            val dK = U.evalCVar (k, envK, storeK)
            val (cloK_aPs, any_unknown) = U.cloKOf (add_aP, dK, aP, storeP)
            fun handle_cloK_aP ((cloK, aP'), store_exts) = let
                val ((_, _, xs, body), env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
                val cloK_ty = CPSTypes.ContTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs)
                val cloK_ty = U.instantiateCTy (tenv_cloK, cloK_ty)
            in
                case U.unifyCont (tenv_cloK, k_cty, cloK_ty)
                 of NONE => store_exts
                  | SOME _ => let
                      fun extend (index, store_exts) = let
                          val x = List.nth (xs, index)
                      in (U.alloc (x, tenv, aP'), d_update) :: store_exts end
                      val store_exts = List.foldl extend store_exts update_indices
                  in store_exts end
            end
            val store_exts =
                List.foldl handle_cloK_aP [] cloK_aPs
            val pass_to_unknown = if any_unknown then [d_update] else []
            in ([], store_exts, [], [], pass_to_unknown, []) end
        | _ => raise BadUpdate
     (* end case *)
  end

  (* performs a transition on a single update to an address *)
  fun transUpdate_a_secondary (pinfo, add_a_primary, add_a_secondary, add_aP, utilAddrs : util_addrs,
                               xi, store, storeK, storeP, a_update, d_update) = let
      val sideEffectVars = #sideEffectVars utilAddrs
      val tyAddrs = #tyAddrs utilAddrs
      val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      fun is_update_a a = Addr.same (a, a_update)
      fun eval_with_fall_through arg = let
          val a = Env.lookup (env, arg)
      in if is_update_a a
         then d_update
         else Store.lookup (store, a)
      end
  in
      case e
       of C.GET (oper, args, x, e') => let
           val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
           val a = U.alloc (x, tenv, aP)
           val store_exts = U.performGetPrim (fn (a_ref, store_exts) =>
                                                 if is_update_a a_ref
                                                 then (a, d_update) :: store_exts
                                                 else store_exts)
                                             [] (oper, d_args)
       in ([], store_exts, [], [], [], []) end
        | C.SET (oper, args, x, e') => let
            val d_args = List.map eval_with_fall_through args
            val (d, pass_to_unknown, store_exts) = U.performSetPrim (oper, d_args, [])
            val a = U.alloc (x, tenv, aP)
        in ([], (a, d) :: store_exts, [], [], pass_to_unknown, []) end
        | C.SELECT (offset, arg, x, e') =>  let
            val d_sel = d_update
            val a = U.alloc (x, tenv, aP)
            val _ = checkTypes (tenv, x, d_sel);
        in ([], [(a, d_sel)], [], [], [], []) end 
        | C.SWITCH (arg, pats) => let
            val d_arg = U.evalLVar (arg, env, store)
            fun doCase ((pat, exp'), store_exts) =
                (case pat
                  of C.VPAT x => store_exts
                   | C.DCPAT(dcon, _, SOME x) => let
                       val a = U.alloc (x, tenv, aP)
                       val store_exts = Value.match_dcon (fn (a_get, store_exts) =>
                                                             if is_update_a a_get then (a, d_update) :: store_exts else store_exts)
                                                         store_exts
                                                         (dcon, d_arg)
                   in store_exts end
                   | _ => store_exts)
            val store_exts = List.foldl doCase [] pats
        in ([], store_exts, [], [], [], []) end
        | C.APPLY (f, tys, args, argKs) => let
            val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
            val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
            fun find_update_indices (arg, (index, indices)) = let
                val a = Env.lookup (env, arg)
            in if is_update_a a
               then (index+1, index::indices)
               else (index+1, indices)
            end
            val (_, update_indices) = List.foldl find_update_indices (0, []) args
            val d_f = U.evalLVar(f, env, store)
            fun handle_clo (clo, store_exts) = let
                val (lam as (_, lam_lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
                val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
            in
                case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                 of NONE => store_exts
                  | SOME tenv' => let
                      val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                      fun extend (index, store_exts) = let
                          val x = List.nth (xs, index)
                      in (U.alloc (x, tenv, aP'), d_update) :: store_exts end
                      val store_exts = List.foldl extend store_exts update_indices
                  in store_exts end
            end
            val store_exts = Value.fold_clos handle_clo [] d_f
            val pass_to_unknown = Value.fold_unknown (fn acc => d_update :: acc) [] d_f
        in ([], store_exts, [], [], pass_to_unknown, []) end
        | _ => raise BadUpdate
     (* end case *)
  end

  (* performs a transition on a single update to a continuation address *)
  fun transUpdate_aP (pinfo, add_a_primary, add_a_secondary, add_aP, utilAddrs : util_addrs,
                      xi, store, storeK, storeP,
                      aP_update, lst_update, dP_update) = let
      val sideEffectVars = #sideEffectVars utilAddrs
      val tyAddrs = #tyAddrs utilAddrs
      val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
  in
      case e
       of C.APPLY (f, tys, args, argKs) => let
           val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
           val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
           val d_f = U.evalLVar(f, env, store)
           val dKs = List.map (fn argK => U.evalCVar (argK, envK, storeK)) argKs
           val popProxies = U.popProxies_indices (add_aP, dP_update, lst_update, storeP)
           fun handle_clo (clo, storeP_exts) = let
               val (lam as (_, lam_lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
               val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
               val clo_ty = U.instantiateTy (tenv_clo, clo_ty)
           in
               case U.unifyAndExtend (tenv_clo, f_ty, clo_ty)
                of NONE => storeP_exts
                 | SOME tenv' => let
                     val aP' = U.allocP (lam_lab, tenv', exp, tenv)
                     val storeP_exts = (aP', popProxies) :: storeP_exts
                 in storeP_exts end
           end
           val storeP_exts = Value.fold_clos handle_clo [] d_f
           val pass_to_unknownK = [] (* TODO: Value.fold_unknown (fn acc => dK_update :: acc) [] d_f *)
           in ([], [], [], storeP_exts, [], pass_to_unknownK) end
       | C.THROW (k, args) => let
           val k_cty = U.instantiateCTy (tenv, CVar.typeOf k)
           (* for throws, the continuation argument is the only update *)
           val d_args = List.map (fn arg => U.evalLVar (arg, env, store)) args
           val dK = U.evalCVar (k, envK, storeK)
           val [index] = lst_update
           val (cloK_aPs, any_unknown) = U.cloKOf_index (add_aP, dP_update, index, storeP)
           fun handle_cloK_aP ((cloK, aP'), (next_configs, store_exts)) = let
               val ((_, lamK_lab, xs, body), env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
                val cloK_ty = CPSTypes.ContTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs)
                val cloK_ty = U.instantiateCTy (tenv_cloK, cloK_ty)
                (*
                val _ = DebugAnalysisStateSpace.run (fn say => say ["CallingK ", Label.toString lamK_lab, " from ", Label.toString lab_e, " with ", String.concatWithMap " " Value.toString d_args, "\n"])
                val _ = DebugAnalysisStateSpace.run (fn say => say [TEnv.toString tenv_cloK, " ", cty_toString k_cty, " ", cty_toString cloK_ty, "\n"])
                *)
            in
                case U.unifyCont (tenv_cloK, k_cty, cloK_ty)
                 of NONE => (next_configs, store_exts)
                  | SOME _ => let
                      fun extend (x, d_arg, (env, store_exts)) = let
                          val a = U.alloc (x, tenv_cloK, aP')
                      in (Env.extend (env, x, a), (a, d_arg) :: store_exts) end
                      val (env', store_exts) =
                          ListPair.foldl extend (env_cloK, store_exts) (xs, d_args)
                      val next_configs = Config.make (body, env', envK_cloK, tenv_cloK, aP') :: next_configs
                  in (next_configs, store_exts) end
           end
           val (next_configs, store_exts) =
               List.foldl handle_cloK_aP ([], []) cloK_aPs
           val pass_to_unknown = if any_unknown then d_args else []
           in (next_configs, store_exts, [], [], pass_to_unknown, []) end
       | _ => raise BadUpdate
  end

  fun passed_to_unknown (pinfo, add_a_primary, add_a_secondary, add_aP,
                         ds, cloKs, store, storeK, storeP,
                         ldata_passed_to_unknown, cdata_passed_to_unknown, trans) = let
      val (next_configs, store_exts, storeK_exts, storeP_exts) = trans
      val tenv = TEnv.empty (* TODO *)
      fun handle_d (d, acc) = let
          fun handle_a (a, (wl, seen, result)) =
              if AS.member (seen, a)
              then (wl, seen, result)
              else ((* FIXME: not sure what to put here: add_a a; *) (a::wl, AS.add (seen, a), result))
          fun f_clo (clo, (wl, seen, result)) = let
              val (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown) = result
              val ((_, lab, xs, ks, body), env_clo, tenv_clo) = Clo.get clo
              val ldata_passed_to_unknown = LS.add (ldata_passed_to_unknown, lab)
              val tenv' = tenv_clo (* TODO: we should have some sort of UNKNOWN type *)
              val aP' = U.allocP (PInfo.lam_lab0 pinfo, tenv', body, tenv)
              fun extend (x, (env, store_exts)) = let
                  val a = U.alloc (x, tenv', aP')
              in (Env.extend (env, x, a), (* (a, Value.add_unknown (Value.empty ())) :: TODO *) store_exts) end
              val (env', store_exts) =
                  List.foldl extend (env_clo, store_exts) xs
              fun extendK (k, (envK, storeK_exts)) = let
                  val aK = U.allocK (k, tenv, aP')
                  val dK = ValueK.from_index (PInfo.k_index pinfo k)
              in (EnvK.extend (envK, k, aK), (aK, dK) :: storeK_exts) end
              val (envK', storeK_exts) =
                  List.foldl extendK (EnvK.empty, storeK_exts) ks
              val dP = ValueProxy.unknown
              val storeP_exts = (aP', dP) :: storeP_exts
              val next_configs = Config.make (body, env', envK', tenv', aP') :: next_configs
              val result = (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown)
              in (wl, seen, result) end
          fun f_dv (dv, acc) = let
              val (_, dcon, ao) = DataValue.get dv
          in case ao
              of SOME a => handle_a (a, acc)
               | NONE => acc
          end
          fun f_tv (tv, acc) = let
              val (_, addrs) = TupleValue.get tv
          in List.foldl handle_a acc addrs end
          val f_ref = handle_a
          fun f_arr ((_, a), acc) = handle_a (a, acc)
          fun f_unknown acc = acc
      in Value.fold f_clo f_dv f_tv f_ref f_arr f_unknown acc d end

      fun wl_algo (wl, seen, result) =
          case wl
           of [] => result
            | a :: wl_rst =>
              wl_algo (handle_d (Store.lookup (store, a), (wl_rst, seen, result)))

      fun handle_cloK (cloK, result) = let
          val (lamK, env_cloK, envK_cloK, tenv_cloK) = CloK.get cloK
          val (_, lamK_lab, xs, body) = lamK
          val (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown) = result
          val cdata_passed_to_unknown = LS.add (cdata_passed_to_unknown, lamK_lab)
          val aP' = U.allocP (PInfo.lam_lab0 pinfo, tenv_cloK, body, tenv)
          fun extend (x, (env, store_exts)) = let
              val a = U.alloc (x, tenv_cloK, aP')
          in (Env.extend (env, x, a), (* (a, Value.add_unknown (Value.empty ())) :: TODO *) store_exts) end
          val (env', store_exts) =
              List.foldl extend (env_cloK, store_exts) xs
          val dP = ValueProxy.unknown
          val storeP_exts = (aP', dP) :: storeP_exts
          val next_configs = Config.make (body, env', envK_cloK, tenv_cloK, aP') :: next_configs
          val result = (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown)
          in result end

      val result = (next_configs, store_exts, storeK_exts, storeP_exts, ldata_passed_to_unknown, cdata_passed_to_unknown)
    (* TODO *)
  (*
      val initial = ([], AS.empty, result)
      val result = wl_algo (List.foldl handle_d initial ds)
      val result = List.foldl handle_cloK result cloKs
  *)
      in result end

end
