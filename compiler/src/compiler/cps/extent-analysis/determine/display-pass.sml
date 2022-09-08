(* display-pass.sml
 *
 * Computes display passing information.
 *)

structure DetermineDisplayPass : DETERMINE_INFO =
  struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure CVS = LVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  structure B = Binding
  structure BS = Binding.Set
  structure U = TransitionUtil

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val aK_map = #aK_map analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      fun add (map, x, l, ls) =
          case ls of
              NONE => map
            | SOME ls =>
              (case LVM.find (map, x)
                of NONE => LVM.insert (map, x, LM.insert (LM.empty, l, ls))
                 | SOME acc =>
                   LVM.insert (map, x,
                               (case LM.find (acc, l)
                                 of NONE => LM.insert (acc, l, ls)
                                  | SOME ls' => LM.insert (acc, l, LS.intersection (ls', ls)))))
      fun get (map, x, l) =
          case LVM.find (map, x)
           of NONE => NONE
            | SOME acc => (case LM.find (acc, l)
                            of NONE => NONE
                             | SOME ls => SOME ls)
      fun addK (mapK, k, l, ls) =
          case ls of
              NONE => mapK
            | SOME ls =>
              (case CVM.find (mapK, k)
                of NONE => CVM.insert (mapK, k, LM.insert (LM.empty, l, ls))
                 | SOME accK =>
                   CVM.insert (mapK, k,
                               (case LM.find (accK, l)
                                 of NONE => LM.insert (accK, l, ls)
                                  | SOME ls' => LM.insert (accK, l, LS.intersection (ls', ls)))))
      fun getK (mapK, k, l) =
          case CVM.find (mapK, k)
           of NONE => NONE
            | SOME accK => (case LM.find (accK, l)
                             of NONE => NONE
                              | SOME ls => SOME ls)

      fun intersection (ls1, ls2) =
          case (ls1, ls2)
           of (NONE, NONE) => NONE
            | (SOME ls1, NONE) => SOME ls1
            | (NONE, SOME ls2) => SOME ls2
            | (SOME ls1, SOME ls2) => SOME (LS.intersection (ls1, ls2))

      fun iterate ((C.EXP (l, e), env, envK, aP), (map, mapK)) = let
          val lam_lab = PInfo.exp_lam pinfo l
          val cn = LS.add (PInfo.cn_ld_lam pinfo lam_lab, lam_lab)
      in
          case e
           of C.LETFUN (bindings, body) => let
               (* variables that bind explicit function values always
               match the environment of the current frame *)
               val map = List.foldl (fn ((x, _), map) => add (map, x, lam_lab, SOME cn)) map bindings
               val map = List.foldl (fn ((_, (lam_lab', _, _, _)), map) =>
                                        LVS.foldl (fn (x, map) =>
                                                           add (map, x, lam_lab', get (map, x, lam_lab)))
                                                       map (PInfo.fv_lam_lv pinfo lam_lab'))
                                    map bindings
           in (map, mapK) end
            | C.LETCONT (bindings, body) => let
                (* cont variables that bind explicit continuation
                values always match the environment of the current
                frame *)
                val mapK = List.foldl (fn ((k, _), mapK) => addK (mapK, k, lam_lab, SOME cn)) mapK bindings
            in (map, mapK) end
            | C.IF (oper, args, thn, els) => (map, mapK)
              (* Shouldn't have to do anything here *)
            | C.ATOM (arg, x, e') =>
              (case arg
                of C.LVAR (y, _) => (add (map, x, lam_lab, get (map, y, lam_lab)), mapK)
                 | _ => (map, mapK))

            (* nothing interesting happens at prim-ops except for refs, which we handle later *)
            | C.PURE (oper, args, x, e') => (map, mapK)
            | C.ARITH (oper, args, x, e', e_exn) => (map, mapK)
            | C.GET (oper, args, x, e') => (map, mapK)
            | C.SET (oper, args, x, e') => (map, mapK)

            | C.TUPLE (args, x, e') => (map, mapK)
            | C.SELECT (offset, arg, x, e') => (map, mapK)

            | C.DCAPPLY (dcon, tys, arg, x, e') => (map, mapK)
            | C.SWITCH (arg, pats) => (map, mapK)

            | C.APPLY (f, tys, args, argKs) => let
                val f_ls = get (map, f, lam_lab)
                fun handle_arg arg = intersection (f_ls, get (map, arg, lam_lab))
                val args_ls = List.map handle_arg args
                fun getCont (map, cont, l) =
                    case cont
                     of C.CLAMBDA lamK => SOME cn
                      | C.CVAR k => getK (mapK, k, l)
                fun handle_argK argK = intersection (f_ls, getCont (map, argK, lam_lab))
                val argKs_ls = List.map handle_argK argKs

                val clos = U.evalLVar(f, env, store)
                fun handle_clo (((lam_lab', xs, ks, body), env_lam), (map, mapK)) = let
                    fun addLV (x, arg_ls, map) = add (map, x, lam_lab', arg_ls)
                    val map = ListPair.foldl addLV map (xs, args_ls)
                    fun addCV (k, argK_ls, mapK) = addK (mapK, k, lam_lab', argK_ls)
                    val mapK = ListPair.foldl addCV mapK (ks, argKs_ls)
                in (map, mapK) end
                val (map, mapK) = Value.fold_clos handle_clo (map, mapK) clos
            in (map, mapK) end
            | C.THROW (k, args) => let
                val k_ls = getK (mapK, k, lam_lab)
                fun handle_arg arg = intersection (k_ls, get (map, arg, lam_lab))
                val args_ls = List.map handle_arg args
                val aK = EnvK.lookup (envK, k)
                fun handle_cloK (((lamK_lab', xs, body), env_lam, envK_lam), map) = let
                    fun addLV (x, arg_ls, map) =
                        add (map, x, PInfo.exp_lam pinfo (CU.labelOfExp body), arg_ls)
                    val map = ListPair.foldl addLV map (xs, args_ls)
                in map end
                val (cloKs, _, _) = AddrK.Map.lookup (aK_map, aK)
                val map = CloK.Set.foldl handle_cloK map cloKs
            in (map, mapK) end
      end

      fun fixpoint (map, mapK) = let
          val (map', mapK') = Config.Set.foldl iterate (map, mapK) configs
      in case (LVM.collate (LM.collate LS.compare) (map, map'),
               CVM.collate (LM.collate LS.compare) (mapK, mapK'))
          of (EQUAL, EQUAL) => (map, mapK)
           | _ => fixpoint (map', mapK')
      end

      (* At this point we can figure out at each call site what we are allowed to passed *)
      (* for every var, for each lambda that uses that var, what frames does that var have in common with the lambda *)

      val displayLVar : (LS.set LM.map) LVM.map = LVM.empty
      val displayCVar : (LS.set LM.map) CVM.map = CVM.empty
      val (displayLVar, displayCVar) = fixpoint (displayLVar, displayCVar)

      fun add_call_site (call_site, acc) = let
          val lam_lab = PInfo.exp_lam pinfo call_site
      in
          case PInfo.exp pinfo call_site
           of C.EXP (_, C.APPLY (f, tys, args, argKs)) =>
              (case get (displayLVar, f, lam_lab)
                of NONE => LM.insert (acc, call_site, LS.empty)
                 | SOME ls => LM.insert (acc, call_site, ls))
            | C.EXP (_, C.THROW (k, args)) =>
              (case getK (displayCVar, k, lam_lab)
                of NONE => LM.insert (acc, call_site, LS.empty)
                 | SOME ls => LM.insert (acc, call_site, ls))
            | _ => raise Fail "bad"
      end
      val displayPass = LM.empty
      val displayPass = List.foldl add_call_site displayPass (PInfo.call_sites pinfo)
      val displayPass = List.foldl add_call_site displayPass (PInfo.callK_sites pinfo)

      val ainfo = AInfo.with_displayPass (ainfo, displayPass)
  in ainfo end

end
