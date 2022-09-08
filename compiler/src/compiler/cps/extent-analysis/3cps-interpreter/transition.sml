
(* transition.sml
 *
 * Transitions a concrete state.
 *)

structure ThreeCPSTransition : sig

  datatype transResult = TRANS of ThreeCPSTransitionUtil.state | HALT of ThreeCPSValue.t list

  val initialState : CPSInformation.t -> (LVar.t -> Extent.t) -> CPS.comp_unit -> ThreeCPSTransitionUtil.mutable_state * ThreeCPSTransitionUtil.state

  val transAndObtain : CPSInformation.t -> (LVar.t -> Extent.t) -> ThreeCPSTransitionUtil.mutable_state -> ThreeCPSTransitionUtil.state -> transResult

end = struct

  structure C = CPS
  structure CU = CPSUtil
  structure LS = Label.Set
  structure LVS = LVar.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LVT = LVar.Tbl
  structure TVM = CPSTyVar.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation
  structure U = ThreeCPSTransitionUtil

  structure A = ThreeCPSAddr
  structure VB = ThreeCPSValueBase
  structure V = ThreeCPSValue
  structure VKB = ThreeCPSValueKBase
  structure VK = ThreeCPSValueK

  datatype transResult = TRANS of ThreeCPSTransitionUtil.state | HALT of V.t list

  (* Obtains the initial interpreter state for the program *)
  fun initialState pinfo mark (C.CU(f, lab0, xs, ks, e0)) : U.mutable_state * U.state = let
      val stack_pointer = ref 0
      val heap_pointer = ref 0
      val stackK_pointer = ref 0

      val registers = LVT.mkTable (100, Fail "registers")
      val stack = UnboundedArray.empty()
      val heap = UnboundedArray.empty()
      val stackK = UnboundedArray.empty()

      val count_lvar_alloc = LVar.Tbl.mkTable (10000, Fail "count_lvar_alloc")
      val () = List.app (fn x => LVar.Tbl.insert count_lvar_alloc (x, 0)) (PInfo.lvars pinfo)
      val count_lam_alloc = Label.Tbl.mkTable (10000, Fail "count_lam_alloc")
      val () = List.app (fn lam => Label.Tbl.insert count_lam_alloc (lam, 0)) (PInfo.lams pinfo)
      val expsSeen = ref LS.empty
      val lvarsBound = ref LVS.empty

      val mutable_state : U.mutable_state = {
          stack_pointer = stack_pointer,
          heap_pointer = heap_pointer,
          stackK_pointer = stackK_pointer,
          registers = registers,
          stack = stack,
          heap = heap,
          stackK = stackK,
          count_lvar_alloc=count_lvar_alloc,
          count_lam_alloc=count_lam_alloc,
          expsSeen = expsSeen,
          lvarsBound = lvarsBound
      }

      fun alloc_stack () = let
          val a = !stack_pointer
          val () = (stack_pointer := a+1)
      in a end

      fun alloc_heap () = let
          val a = !heap_pointer
          val () = (heap_pointer := a+1)
      in a end

      fun alloc_stackK () = let
          val aK = !stackK_pointer
          val () = (stackK_pointer := aK+1)
      in aK end

      fun alloc_at_mark M = 
          case M
           of Extent.HEAP => alloc_heap ()
            | Extent.STK => alloc_stack ()
            | Extent.REG => ~1

      fun bind_lvar x =
          (U.incr_lvar_count (mutable_state, x);
           lvarsBound := LVS.add (! lvarsBound, x))

      fun alloc x =
          (bind_lvar x; alloc_at_mark (mark x))

      fun store_at_mark (x, M, a, d) =
          case M
           of Extent.HEAP => UnboundedArray.store (heap, a, d)
            | Extent.STK => UnboundedArray.store (stack, a, d)
            | Extent.REG => LVT.insert registers (x, d)

      fun alloc_and_store (x, d) = let
          val M = mark x
          val a = alloc_at_mark M
          val () = store_at_mark (x, M, a, d)
      in a end

      fun allocK k =
          alloc_stackK ()

      fun allocK_and_store (k, dK) = let
          val aK = allocK k
          val () = UnboundedArray.store (stackK, aK, dK)
      in aK end

      val env = LVM.empty
      val env = List.foldl (fn (x, env) => LVM.insert (env, x, alloc_and_store (x, V.make VB.UNIT))) LVM.empty xs

      val envK = LVM.empty
      val envK = List.foldl (fn (k, envK) => CVM.insert (envK, k, allocK_and_store (k, VK.halt))) CVM.empty ks

      val tenv = TVM.empty

      val state0 = (e0, env, envK, tenv)
      in (mutable_state, state0) end

  fun transAndObtain pinfo mark mutable_state state = let
      val (exp as C.EXP (lab_e,e), env, envK, tenv) = state
      val stack_pointer = #stack_pointer mutable_state
      val heap_pointer = #heap_pointer mutable_state
      val registers = #registers mutable_state
      val stack = #stack mutable_state
      val heap = #heap mutable_state
      val stackK_pointer = #stackK_pointer mutable_state
      val stackK = #stackK mutable_state
      val lvarsBound = #lvarsBound mutable_state
      val expsSeen = #expsSeen mutable_state
      val () = expsSeen := LS.add (!expsSeen, lab_e)

      val current_stack_pointer = !stack_pointer
      val current_stackK_pointer = !stackK_pointer

      fun alloc_stack () = let
          val a = !stack_pointer
          val () = (stack_pointer := a+1)
      in a end

      fun alloc_heap () = let
          val a = !heap_pointer
          val () = (heap_pointer := a + 1)
      in a end

      fun alloc_stackK () = let
          val aK = !stackK_pointer
          val () = (stackK_pointer := aK+1)
      in aK end

      fun alloc_at_mark M = 
          case M
           of Extent.HEAP => alloc_heap ()
            | Extent.STK => alloc_stack ()
            | Extent.REG => ~1

      fun bind_lvar x =
          (U.incr_lvar_count (mutable_state, x);
           lvarsBound := LVS.add (! lvarsBound, x))
           

      fun alloc x =
          (bind_lvar x; alloc_at_mark (mark x))

      fun store_at_mark (x, M, a, d) =
          case M
           of Extent.HEAP => UnboundedArray.store (heap, a, d)
            | Extent.STK => UnboundedArray.store (stack, a, d)
            | Extent.REG => LVT.insert registers (x, d)

      fun store (x, env, d) =
          store_at_mark (x, mark x, LVM.lookup (env, x), d)

      fun alloc_and_store (x, d) = let
          val M = mark x
          val a = alloc_at_mark M
          val () = bind_lvar x
          val () = store_at_mark (x, M, a, d)
      in a end

      fun load (x, env) =
          case mark x
           of Extent.HEAP => UnboundedArray.load (heap, LVM.lookup (env, x))
            | Extent.STK => UnboundedArray.load (stack, LVM.lookup (env, x))
            | Extent.REG => LVT.lookup registers x

      fun get_addr (x, env) = let
          val a = LVM.lookup (env, x)
      in case mark x
          of Extent.HEAP => A.HeapAddr a
           | Extent.STK => A.StackAddr a
           | Extent.REG => A.RegAddr x
      end

      fun alloc_heap_addr () =
          A.HeapAddr (alloc_heap ())
      
      fun load_addr a =
          case a
           of A.HeapAddr index => UnboundedArray.load (heap, index)
            | A.StackAddr index => UnboundedArray.load (stack, index)
            | A.RegAddr x => LVT.lookup registers x

      fun store_addr (a, d) =
          case a
           of A.HeapAddr index => UnboundedArray.store (heap, index, d)
            | A.StackAddr index => UnboundedArray.store (stack, index, d)
            | A.RegAddr x => LVT.insert registers (x, d)

      fun allocK k =
          alloc_stackK ()

      fun allocK_and_store (k, dK) = let
          val aK = allocK k
          val () = UnboundedArray.store (stackK, aK, dK)
      in aK end

      fun storeK (k, envK, dK) =
          UnboundedArray.store (stackK, CVM.lookup (envK, k), dK)

      fun loadK (k, envK) =
          UnboundedArray.load (stackK, CVM.lookup (envK, k))

      fun pop_stack (new_stack_pointer) = let
          fun reset (index) =
              if index < current_stack_pointer
              then (UnboundedArray.delete (stack, index); reset (index + 1))
              else ()
      in reset new_stack_pointer; stack_pointer := new_stack_pointer end

      fun pop_stackK (new_stackK_pointer) = let
          fun reset (index) =
              if index < current_stackK_pointer
              then (UnboundedArray.delete (stackK, index); reset (index + 1))
              else ()
      in reset new_stackK_pointer; stackK_pointer := new_stackK_pointer end

      in
        case e
         of C.LETFUN (bindings, body) => let
             (* allocate the addresses which will be needed *)
             val triples = List.map (fn lam => (#1 lam, alloc (#1 lam), lam)) bindings
             val env' = List.foldl (fn ((x, a, lam), env) => LVM.insert (env, x, a)) env triples
             val triples = List.map (fn (x, a, lam) => (x, a, (VB.CLO (lam, env', tenv)))) triples
             val () = List.app (fn (x, _, d) => store (x, env', d)) triples
             val () = List.app (fn lam => U.incr_lam_count (mutable_state, #2 lam)) bindings
             in TRANS (body, env', envK, tenv) end
          | C.LETCONT (bindings, body) => let
             (* allocate the addresses which will be needed *)
             val triplesK = List.map (fn lamK => (#1 lamK, allocK (#1 lamK), lamK)) bindings
             val envK' = List.foldl (fn ((k, aK, lamK), envK) => CVM.insert (envK, k, aK)) envK triplesK
             val triplesK = List.map (fn (k, aK, lamK) => (k, aK, VK.make (VKB.CLOK (lamK, env, envK', tenv, current_stack_pointer, current_stackK_pointer)))) triplesK
             val () = List.app (fn (k, _, dK) => storeK (k, envK', dK)) triplesK

             in TRANS (body, env, envK', tenv) end
          | C.IF (oper, args, thn, els) =>
             if U.evalTestPrim (oper, List.map (fn arg => load (arg, env)) args, load_addr)
             then TRANS (thn, env, envK, tenv)
             else TRANS (els, env, envK, tenv)
          | C.ATOM (arg, x, e') => let
              val d_arg = U.evalAtom mutable_state (arg, env, load)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_arg))
              in TRANS (e', env', envK, tenv) end
          | C.PURE (oper, args, x, e') => let
              val d_args = List.map (fn arg => load (arg, env)) args
              val d_res = U.evalPurePrim mutable_state (oper, d_args, alloc_heap, store_addr) (* might allocate a ref cell or array in the stack or heap *)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_res))
              in TRANS (e', env', envK, tenv) end
          | C.ARITH (oper, args, x, e', e_exn) => (let
              val d_args = List.map (fn arg => load (arg, env)) args
              val d_res = U.evalArithPrim mutable_state (oper, d_args)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_res))
              in TRANS (e', env', envK, tenv) end
          (* If we see a fail exception, that was due to a failure to handle a primop.
             Otherwise, the primop application had an exception and we should transition
             to the exception expression. *)
                handle Fail x => raise Fail x
                     | _ => TRANS (e_exn, env, envK, tenv))
          | C.GET (oper, args, x, e') => let
              val d_args = List.map (fn arg => load (arg, env)) args
              val d_res = U.evalGetPrim mutable_state (oper, d_args, load_addr)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_res))
              in TRANS (e', env', envK, tenv) end
          | C.SET (oper, args, x, e') => let
              val d_args = List.map (fn arg => load (arg, env)) args
              val d_res = U.evalSetPrim mutable_state (oper, d_args, store_addr) (* need to set things in stack or heap *)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_res))
              in TRANS (e', env', envK, tenv) end

          | C.TUPLE (args, x, e') => let
              val addrs = List.map (fn arg => let val a = alloc_heap_addr () in store_addr (a, load (arg, env)); a end) args
              (* val d_tup = V.make (VB.TUPLE (List.map (fn arg => get_addr (arg, env)) args)) *)
              val d_tup = V.make (VB.TUPLE addrs)
              val env' = LVM.insert (env, x, alloc_and_store (x, d_tup))
              in TRANS (e', env', envK, tenv) end
          | C.SELECT (offset, arg, x, e') => let
              val d_arg = load (arg, env)
              in
                case V.base d_arg
                 of VB.TUPLE addrs => if offset <= (List.length addrs)
                      then let
                        val d_sel = load_addr (List.nth(addrs, offset-1))
                        val env' = LVM.insert (env, x, alloc_and_store (x, d_sel))
                        in TRANS (e', env', envK, tenv) end
                      else raise Fail(concat[
                          "bad value: SELECT not given TUPLE of long enough length: ",
                          Int.toString offset, " ", VB.toString (VB.TUPLE addrs)
                        ])
                  | _ => raise Fail("bad value: SELECT not given TUPLE: " ^ VB.toString (V.base d_arg))
                (* end case *)
              end

          | C.DCAPPLY (dcon, tys, arg, x, e') => let
              val a = let val a = alloc_heap_addr () in store_addr (a, load (arg, env)); a end
              (* val d_dv = V.make (VB.DATA (dcon, SOME (get_addr (arg, env)))) *)
              val d_dv = V.make (VB.DATA (dcon, SOME a))
              val env' = LVM.insert (env, x, alloc_and_store (x, d_dv))
          in TRANS (e', env', envK, tenv) end
          | C.SWITCH (arg, pats) => let
              val d = load (arg, env)
              (* val _ = if (Label.toString lab_e) = (*"L05DE"*) "L05FC" then CheckAnalysisResults.say [CValue.toString d, "switch", "\n"] else () *)
              fun handle_pats pats =
                  (case pats
                    of [] => raise Fail "no pattern"
                     | (pat,body)::rst =>
                       (case (pat, V.base d)
                         of (C.VPAT x, _) => let
                             val env' = LVM.insert (env, x, alloc_and_store (x, d))
                         in TRANS (body, env', envK, tenv) end
                          | (C.DCPAT (dcon', _, xo), VB.DATA (dcon, ao)) =>
                            (case (CPSDataCon.compare(dcon, dcon'), ao, xo)
                              of (EQUAL, SOME a, SOME x) => let
                                  val d_inner = load_addr a
                                  val env' = LVM.insert (env, x, alloc_and_store (x, d_inner))
                              in TRANS (body, env', envK, tenv) end
                               | (EQUAL, NONE, NONE) => TRANS (body, env, envK, tenv)
                               | _ => handle_pats rst)
                          | (C.LPAT (lit, _), base) =>
                            if (VB.compare (U.literalToValueBase lit, base)) = EQUAL
                            then TRANS (body, env, envK, tenv)
                            else handle_pats rst
                          | _ => raise Fail ("bad pattern: got " ^ (V.toString d) ^ " at " ^ (Label.toString lab_e))))
          in handle_pats pats end

          | C.APPLY (f, tys, args, argKs) => let
              val CPSTypes.TyScheme (tvars, f_ty) = LVar.typeOf f
              val f_ty = U.instantiate (tenv, tvars, tys, f_ty)
              val args = List.map (fn arg => load (arg, env)) args
              val argKs = List.map (fn argK => loadK (argK, envK)) argKs
              val d_f = load (f, env)
              (* val () = Verbose.say (["calling: ", Label.toString lab_e, " "] @ (List.map ThreeCPSValue.toString (d_f :: args)) @ ["\n"]) *)
              in
                case V.base d_f
                 of VB.CLO (clo as (lam, env_lam, tenv_lam)) => let
                      val (_, lab_lam, xs, ks, body) = lam
                      val clo_ty = CPSTypes.FunTy (List.map (fn x => U.removeScheme (LVar.typeOf x)) xs, List.map CVar.typeOf ks)
                      val clo_ty = U.instantiateTy (tenv_lam, clo_ty)
                      val tenv' = (case U.unifyAndExtend (tenv_lam, f_ty, clo_ty)
                                    of NONE => (Verbose.say ["call: ", Label.toString lab_e,
                                                             " | lam: ", Label.toString lab_lam,
                                                             " | f_ty: ", CPSTypes.toString f_ty,
                                                             " | clo_ty: ", CPSTypes.toString clo_ty,
                                                             "\n"];
                                                raise Fail "bad type unify")
                                     | SOME tenv' => tenv')
                      val new_stack_pointer = List.foldl (fn (argK, max) => Int.max (VKB.stack_pointer (VK.base argK), max)) 0 argKs
                      val () = pop_stack (new_stack_pointer)
                      val new_stackK_pointer = List.foldl (fn (argK, max) => Int.max (VKB.stackK_pointer (VK.base argK), max)) 0 argKs
                      val () = pop_stackK (new_stackK_pointer)

                      val env' = ListPair.foldl (fn (x, arg, env) => LVM.insert (env, x, alloc_and_store (x, arg))) env_lam (xs, args) 

                      val envK' = ListPair.foldl (fn (k, argK, envK) => CVM.insert (envK, k, allocK_and_store (k, argK))) CVM.empty (ks, argKs)
                 in TRANS (body, env', envK', tenv') end
                  | _ => raise Fail ("bad value: APPLY " ^ (Label.toString lab_e) ^ ": " ^ (VB.toString (V.base d_f)))
                (* end case *)
              end
          | C.THROW (k, args) => let
              val args = List.map (fn arg => load (arg, env)) args
              val cont = loadK (k, envK)
              (* val () = Verbose.say (["throwing: ", Label.toString lab_e, " "] @ (List.map ThreeCPSValue.toString args) @ ["\n"]) *)
              in
                case VK.base cont
                 of VKB.HALT => let
                     in (HALT args) end
                  | (VKB.CLOK (cloK as ((_, lab, xs, body), env_lamK, envK_lamK, tenv_lamK, new_stack_pointer, new_stackK_pointer))) =>
                    if (length args) <> (length xs)
                    then raise Fail "bad program"
                    else let
                        val () = pop_stack (new_stack_pointer)
                        val () = pop_stackK (new_stackK_pointer)
                        val env' = ListPair.foldl (fn (x, arg, env) => LVM.insert (env, x, alloc_and_store (x, arg))) env_lamK (xs, args) 
                    in TRANS (body, env', envK_lamK, tenv_lamK) end
          end
        (* end case *)
      end

end
