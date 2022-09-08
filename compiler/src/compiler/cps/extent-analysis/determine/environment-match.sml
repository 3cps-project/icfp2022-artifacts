(* environment-match.sml
 *
 * Computes solutions to the environment problem, i.e. when do the values a variable can take on share the same frames as the variable's environment?
 *)

structure DetermineEnvironmentMatch : DETERMINE_INFO =
  struct

  structure C = CPS
  structure CU = CPSUtil
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LVT = LVar.Tbl
  structure CVT = CVar.Tbl
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  (* scrape though program, initialize everything to all and add every var to wl *)
  (* compute the var-use map (maybe precompute this and put in pinfo?) *)
  (* for x in wl: 
       recompute for each use(x)
       if changed, add each recomputed to the wl
   *)
  fun init_and_uses (C.CU lam0, ainfo, pinfo) = let
      val lvarEnvMatch = LVT.mkTable (100, Fail "DetermineEnvironmentMatch.lvarEnvMatch")
      val cvarEnvMatch = CVT.mkTable (100, Fail "DetermineEnvironmentMatch.lvarEnvMatch")
      val lvar_uses = LVT.mkTable (100, Fail "fixme")
      val cvar_uses = CVT.mkTable (100, Fail "fixme")

      val selectToTuple = #selectToTuple (AInfo.tupleInfo ainfo)
      val matchToData = #matchToData (AInfo.dataInfo ainfo)

      fun init_lvar (x, ls) =
          (LVT.insert lvar_uses (x, []);
           LVT.insert lvarEnvMatch (x, ls))

      fun lvar_used (x, exp) =
          LVT.insert lvar_uses (x, exp :: (LVT.lookup lvar_uses x))

      fun init_cvar (k, ls) =
          (CVT.insert cvar_uses (k, []);
           CVT.insert cvarEnvMatch (k, ls))

      fun cvar_used (k, exp) =
          CVT.insert cvar_uses (k, exp :: (CVT.lookup cvar_uses k))

      fun handle_exp (exp as C.EXP (lab_e, e), ls) =
          case e
           of C.LETFUN (bindings, body) =>
              (List.app (fn (f, _, _, _, _) => init_lvar (f, ls)) bindings;
               List.app (fn lam => handle_lam (lam, ls)) bindings;
               handle_exp (body, ls);
               ())
            | C.LETCONT (bindingKs, body) =>
              (List.app (fn (k, _, _, _) => init_cvar (k, ls)) bindingKs;
               List.app (fn lamK => handle_lamK (lamK, ls)) bindingKs;
               handle_exp (body, ls);
               ())
            | C.IF (oper, args, thn, els) =>
              (List.app (fn x => lvar_used (x, exp)) args;
               handle_exp (thn, ls);
               handle_exp (els, ls);
               ())
            | C.ATOM (arg, x, e') =>
              ((case arg of C.LVAR (y, _) => lvar_used (y, exp) | _ => ());
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())
            | C.PURE (oper, args, x, e') =>
              ((* List.app (fn x => lvar_used (x, exp)) args; *)
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())
            | C.ARITH (oper, args, x, e', e_exn) =>
              ((* List.app (fn x => lvar_used (x, exp)) args; *)
               init_lvar (x, ls);
               handle_exp (e', ls);
               handle_exp (e_exn, ls);
               ())
            | C.GET (oper, args, x, e') =>
              (List.app (fn x => lvar_used (x, exp)) args;
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())
            | C.SET (oper, args, x, e') =>
              ((* List.app (fn x => lvar_used (x, exp)) args; *)
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())

            | C.TUPLE(args, x, e') =>
              ((* List.app (fn x => lvar_used (x, exp)) args; *)
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())
            | C.SELECT(offset, arg, x, e') =>
              (lvar_used (arg, exp);
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())

            | C.DCAPPLY(dcon, tys, arg, x, e') =>
              ((* lvar_used (arg, exp); *)
               init_lvar (x, ls);
               handle_exp (e', ls);
               ())
            | C.SWITCH(arg, pats) =>
              (lvar_used (arg, exp);
               List.app (fn (pat, e') =>
                            ((case pat
                               of C.VPAT x => init_lvar (x, ls)
                               | C.DCPAT (_, _, SOME x) => init_lvar (x, ls)
                               | _ => ());
                             handle_exp (e', ls)))
                        pats;
               ())

            | C.APPLY(f, tys, args, argKs) =>
              (List.app (fn x => lvar_used (x, exp)) (f::args);
               List.app (fn k => cvar_used (k, exp)) argKs;
               ())
            | C.THROW (k, args) =>
              (List.app (fn x => lvar_used (x, exp)) args;
               cvar_used (k, exp);
               ())
      and handle_lamK ((_, lamK_lab, xs, body), ls) = let
          val ls = LS.add (ls, lamK_lab)
      in List.app (fn x => init_lvar (x, ls)) xs;
         handle_exp (body, ls);
         ()
      end
      and handle_lam ((_, lam_lab, xs, ks, body), ls) = let
          val ls = LS.add (ls, lam_lab)
      in List.app (fn x => init_lvar (x, ls)) xs;
         List.app (fn k => init_cvar (k, ls)) ks;
         handle_exp (body, ls);
         ()
      end

      fun handle_non_local_exp (exp as C.EXP (lab_e, e), ls) =
          case e
           of C.LETFUN (bindings, body) =>
              (List.app (fn lam => handle_non_local_lam (lam, ls)) bindings;
               handle_non_local_exp (body, ls))
            | C.LETCONT (bindingKs, body) =>
              (List.app (fn lamK => handle_non_local_lamK (lamK, ls)) bindingKs;
               handle_non_local_exp (body, ls))
            | C.IF (oper, args, thn, els) => 
              (handle_non_local_exp (thn, ls);
               handle_non_local_exp (els, ls))
            | C.ATOM (arg, x, e') => handle_non_local_exp (e', ls)
            | C.PURE (oper, args, x, e') => handle_non_local_exp (e', ls)
            | C.ARITH (oper, args, x, e', e_exn) => 
              (handle_non_local_exp (e', ls); 
               handle_non_local_exp (e_exn, ls))
            | C.GET (oper, args, x, e') => handle_non_local_exp (e', ls)
            | C.SET (oper, args, x, e') => handle_non_local_exp (e', ls)
            | C.TUPLE(args, x, e') => handle_non_local_exp (e', ls)
            | C.SELECT(offset, arg, x, e') => let
                val (tuples, _) = LM.lookup (selectToTuple, lab_e)
                fun handle_non_local_tuple lab_tup = let
                    val C.EXP (_, C.TUPLE (args, _, _)) = PInfo.exp pinfo lab_tup
                    val arg = List.nth (args, offset-1)
                in lvar_used (arg, exp) end
            in LS.app handle_non_local_tuple tuples;
               handle_non_local_exp (e', ls) 
            end
            | C.DCAPPLY(dcon, tys, arg, x, e') => handle_non_local_exp (e', ls)
            | C.SWITCH(arg, pats) => let
                val (datas, _) = LM.lookup (matchToData, lab_e)
                fun handle_non_local_data lab_data = 
                    (case PInfo.exp pinfo lab_data
                      of C.EXP (_, C.DCAPPLY (_, _, arg, _, _)) => lvar_used (arg, exp)
                       | _ => ())
            in LS.app handle_non_local_data datas;
               List.app (fn (_, e') => handle_non_local_exp (e', ls)) pats
            end
            | C.APPLY(f, tys, args, argKs) => ()
            | C.THROW (k, args) => ()
      and handle_non_local_lamK ((_, lamK_lab, xs, body), ls) = let
          val ls = LS.add (ls, lamK_lab)
      in handle_non_local_exp (body, ls) end
      and handle_non_local_lam ((_, lam_lab, xs, ks, body), ls) = let
          val ls = LS.add (ls, lam_lab)
      in handle_non_local_exp (body, ls) end

      val () = handle_lam (lam0, LS.empty)
      val () = handle_non_local_lam (lam0, LS.empty)
  in (lvarEnvMatch, cvarEnvMatch,
      lvar_uses, cvar_uses)
  end


  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val exp = PInfo.exp pinfo
      val lam = PInfo.lam pinfo
      val lamK = PInfo.lamK pinfo
      val selectToTuple = #selectToTuple (AInfo.tupleInfo ainfo)
      val matchToData = #matchToData (AInfo.dataInfo ainfo)
      val callToLam = #callToLam (AInfo.funInfo ainfo)
      val callKToLamK = #callKToLamK (AInfo.funKInfo ainfo)
      val cu = #cu analysis_space

      val (lvarEnvMatch, cvarEnvMatch, lvar_uses, cvar_uses) = init_and_uses (cu, ainfo, pinfo)
      val get_lvar = LVT.lookup lvarEnvMatch 
      val get_cvar = CVT.lookup cvarEnvMatch 
      fun update_lvar (x, labels, wl_lv, wl_cv) = let
          val prev = get_lvar x

          val () = if LVar.toString x = "_arg1410614EA" orelse
                      LVar.toString x = "_arg1910314E4"
                   then Verbose.say [LVar.toString x, " ",
                                     String.concatWithMap " " Label.toString
                                                          (LS.listItems prev),
                                     " | ",
                                     String.concatWithMap " " Label.toString
                                                          (LS.listItems labels),
                                     "\n"] 
                   else ()

          val next = LS.intersection (labels, prev)
          val _ = LVT.insert lvarEnvMatch (x, next)
      in if (LS.numItems prev) <> (LS.numItems next)
         then (LVS.add (wl_lv, x), wl_cv)
         else (wl_lv, wl_cv)
      end
      fun update_cvar (k, labels, wl_lv, wl_cv) = let
          val prev = get_cvar k
          val next = LS.intersection (labels, prev)
          val _ = CVT.insert cvarEnvMatch (k, next)
      in if (LS.numItems prev) <> (LS.numItems next)
         then (wl_lv, CVS.add (wl_cv, k)) 
         else (wl_lv, wl_cv)
      end

      fun handle_lvar (x, wl_lv, wl_cv) = let
          val uses = LVT.lookup lvar_uses x
          fun handle_use (C.EXP (lab_e, e), (wl_lv, wl_cv)) = 
              (case e
               of C.LETFUN (bindings, body) => (wl_lv, wl_cv)
                | C.LETCONT (bindings, body) => (wl_lv, wl_cv)
                | C.IF (oper, args, thn, els) => (wl_lv, wl_cv)
                | C.ATOM (arg, x, e') =>
                  (case arg 
                    of C.LVAR (y, _) => update_lvar (x, get_lvar y, wl_lv, wl_cv)
                     | _ => (wl_lv, wl_cv))
                | C.PURE (oper, args, x, e') => (wl_lv, wl_cv)
                | C.ARITH (oper, args, x, e', e_exn) => (wl_lv, wl_cv)
                | C.GET (oper, args, x, e') => update_lvar (x, LS.empty, wl_lv, wl_cv)
                | C.SET (oper, args, x, e') => (wl_lv, wl_cv)
                | C.TUPLE (args, x, e') => (wl_lv, wl_cv)
                | C.SELECT (offset, arg, x, e') => let
                    val curr = get_lvar arg
                    val (tuples, _) = LM.lookup (selectToTuple, lab_e)
                    fun handle_tuple (lab_tup, (wl_lv, wl_cv)) = let
                        val C.EXP (_, C.TUPLE (args, y, _)) = exp lab_tup
                        val arg = List.nth (args, offset-1)
                        (* TODO: need to intersect with curr or get_lvar y here? *)
                    in update_lvar (x, LS.intersection (get_lvar arg, curr), wl_lv, wl_cv) end
                    val (wl_lv, wl_cv) = LS.foldl handle_tuple (wl_lv, wl_cv) tuples
                in (wl_lv, wl_cv) end
                | C.DCAPPLY (dcon, tys, arg, x, e') => (wl_lv, wl_cv)
                | C.SWITCH (arg, pats) => let
                    val curr = get_lvar arg
                    val (datas, _) = LM.lookup (matchToData, lab_e)
                    fun handle_pat ((pat, _), (wl_lv, wl_cv)) = 
                        (case pat
                          of (C.VPAT x) => update_lvar (x, curr, wl_lv, wl_cv)
                           | (C.DCPAT (dcon, _, SOME x)) => let
                               fun handle_data (lab_data, (wl_lv, wl_cv)) = 
                                   (case exp lab_data
                                     of C.EXP (_, C.DCAPPLY (dcon', _, arg, _, _)) => 
                                        (* TODO: need to intersect with curr or get_lvar y here? *)
                                        if CPSDataCon.same (dcon, dcon') 
                                        then update_lvar (x, LS.intersection (get_lvar arg, curr), wl_lv, wl_cv)
                                        else (wl_lv, wl_cv)
                                      | _ => (wl_lv, wl_cv))
                               val (wl_lv, wl_cv) = LS.foldl handle_data (wl_lv, wl_cv) datas
                           in (wl_lv, wl_cv) end
                           | _ => (wl_lv, wl_cv))
                    val (wl_lv, wl_cv) = List.foldl handle_pat (wl_lv, wl_cv) pats
                in (wl_lv, wl_cv) end
                | C.APPLY (f, tys, args, argKs) => let
                    val curr = get_lvar f
                    val (lams, _) = LM.lookup (callToLam, lab_e)
                    val curr_args = List.map (fn arg => LS.intersection (curr, get_lvar arg)) args
                    val curr_argKs = List.map (fn argK => LS.intersection (curr, get_cvar argK)) argKs
                    fun handle_lam (lab_lam, (wl_lv, wl_cv)) = let
                        val (_, _, xs, ks, _) = lam lab_lam
                        fun handle_lvar (x, curr_arg, (wl_lv, wl_cv)) = update_lvar (x, curr_arg, wl_lv, wl_cv)
                        fun handle_cvar (k, curr_argK, (wl_lv, wl_cv)) = update_cvar (k, curr_argK, wl_lv, wl_cv)
                        val (wl_lv, wl_cv) = ListPair.foldl handle_lvar (wl_lv, wl_cv) (xs, curr_args)
                        val (wl_lv, wl_cv) = ListPair.foldl handle_cvar (wl_lv, wl_cv) (ks, curr_argKs)
                    in (wl_lv, wl_cv) end
                    val (wl_lv, wl_cv) = LS.foldl handle_lam (wl_lv, wl_cv) lams
                in (wl_lv, wl_cv) end
                 | C.THROW (k, args) => let
                    val curr = get_cvar k
                    val (lamKs, _) = LM.lookup (callKToLamK, lab_e)
                    val curr_args = List.map (fn arg => LS.intersection (curr, get_lvar arg)) args
                    fun handle_lamK (lab_lamK, (wl_lv, wl_cv)) = let
                        val (_, _, xs, _) = lamK lab_lamK
                        fun handle_lvar (x, curr_arg, (wl_lv, wl_cv)) = update_lvar (x, curr_arg, wl_lv, wl_cv)
                        val (wl_lv, wl_cv) = ListPair.foldl handle_lvar (wl_lv, wl_cv) (xs, curr_args)
                    in (wl_lv, wl_cv) end
                    val (wl_lv, wl_cv) = LS.foldl handle_lamK (wl_lv, wl_cv) lamKs
                in (wl_lv, wl_cv) end)
      in List.foldl handle_use (wl_lv, wl_cv) uses end

      fun handle_cvar (k, wl_lv, wl_cv) = let
          val uses = CVT.lookup cvar_uses k
          fun handle_use (C.EXP (lab_e, e), (wl_lv, wl_cv)) = 
              (case e
               of C.APPLY (f, tys, args, argKs) => let
                    val curr = get_lvar f
                    val (lams, _) = LM.lookup (callToLam, lab_e)
                    fun handle_lam (lab_lam, (wl_lv, wl_cv)) = let
                        val (_, _, xs, ks, _) = lam lab_lam
                        fun handle_cvar (k', (wl_lv, wl_cv)) =
                            if CVar.same (k, k')
                            then update_cvar (k, curr, wl_lv, wl_cv)
                            else (wl_lv, wl_cv)
                        val (wl_lv, wl_cv) = List.foldl handle_cvar (wl_lv, wl_cv) ks
                    in (wl_lv, wl_cv) end
                    val (wl_lv, wl_cv) = LS.foldl handle_lam (wl_lv, wl_cv) lams
                in (wl_lv, wl_cv) end
                | C.THROW (k, args) => let
                    val curr = get_cvar k
                    val (lamKs, _) = LM.lookup (callKToLamK, lab_e)
                    fun handle_lamK (lab_lamK, (wl_lv, wl_cv)) = let
                        val (_, _, xs, _) = lamK lab_lamK
                        fun handle_lvar (x, (wl_lv, wl_cv)) = update_lvar (x, curr, wl_lv, wl_cv)
                        val (wl_lv, wl_cv) = List.foldl handle_lvar (wl_lv, wl_cv) xs
                    in (wl_lv, wl_cv) end
                    val (wl_lv, wl_cv) = LS.foldl handle_lamK (wl_lv, wl_cv) lamKs
               in (wl_lv, wl_cv) end
                | _ => (wl_lv, wl_cv))
      in List.foldl handle_use (wl_lv, wl_cv) uses end

      val () = LVS.app (fn x => (update_lvar (x, LS.empty, LVS.empty, CVS.empty); ())) 
                       (AInfo.unknownLVars ainfo)
      val () = CVS.app (fn x => (update_cvar (x, LS.empty, LVS.empty, CVS.empty); ()))
                       (AInfo.unknownCVars ainfo)

      fun wl_loop (wl_lv, wl_cv) = let
          fun do_cv next (wl_lv, wl_cv) = 
              if CVS.isEmpty wl_cv
              then next (wl_lv, wl_cv)
              else let
                  val k = CVS.minItem wl_cv
                  val wl_cv = CVS.subtract (wl_cv, k)
              in wl_loop (handle_cvar (k, wl_lv, wl_cv)) end
          fun do_lv next (wl_lv, wl_cv) = 
              if LVS.isEmpty wl_lv
              then next (wl_lv, wl_cv)
              else let
                  val x = LVS.minItem wl_lv
                  val wl_lv = LVS.subtract (wl_lv, x)
              in wl_loop (handle_lvar (x, wl_lv, wl_cv)) end
      in do_lv (do_cv (fn x => ())) (wl_lv, wl_cv) end
      val wl_lv = LVS.fromList (PInfo.lvars pinfo)
      val wl_cv = CVS.fromList (PInfo.cvars pinfo)
      val () = wl_loop (wl_lv, wl_cv)
      val () = wl_loop (wl_lv, wl_cv)
      val lvarEnvMatch = LVT.foldi (fn (x, ls, acc) => LVM.insert (acc, x, ls)) LVM.empty lvarEnvMatch
      val cvarEnvMatch = CVT.foldi (fn (k, ls, acc) => CVM.insert (acc, k, ls)) CVM.empty cvarEnvMatch
      val ainfo = AInfo.with_lvarEnvMatch (ainfo, lvarEnvMatch)
      val ainfo = AInfo.with_cvarEnvMatch (ainfo, cvarEnvMatch)
  in ainfo end

end
