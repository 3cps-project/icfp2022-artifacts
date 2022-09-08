(* bound-vars.sml
 *
 * Computes a mapping from return THROWs (THROWs where the cont is an
 * argument to the function) to the set of variables and ldata that
 * are bound in any control path along the function up to that THROW.
 * TODO
 *)

structure Bound : sig

  val bound : CPS.comp_unit -> {b_pop_lv : LVar.Set.set Label.Tbl.hash_table,
                                b_pop_ld : Label.Set.set Label.Tbl.hash_table}

end = struct

  structure C = CPS
  structure LT = Label.Tbl
  structure CVT = CVar.Tbl
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set

  fun bound cu = let
      val b_pop_lv = LT.mkTable(128, Fail "b_pop_lv")
      fun add_b_pop_lv (l, lv) =
          LT.insert b_pop_lv (l, case LT.find b_pop_lv l
                                           of NONE => lv
                                            | SOME lvs => LVS.union (lvs, lv))
      val b_pop_ld = LT.mkTable(128, Fail "b_pop_ld")
      fun add_b_pop_ld (l, ld) =
          LT.insert b_pop_ld (l, case LT.find b_pop_ld l
                                           of NONE => ld
                                            | SOME lds => LS.union (lds, ld))
      (* TODO:DOC k_pop_map maps cvars to pops lexically within the lamK that the cvar is bound to *)
      val k_pop_map = CVT.mkTable(128, Fail "k_pop_map")
      fun add_k_pop_map (k, l) =
          CVT.insert k_pop_map (k, case CVT.find k_pop_map k
                                           of NONE => LS.singleton l
                                            | SOME ls => LS.add (ls, l))
      (* k_k_map maps cvars to cvars used in the lamK that the cvar is used in *)
      val k_k_map = CVT.mkTable(128, Fail "k_k_map")
      fun add_k_k_map (k, k') =
          CVT.insert k_k_map (k, case CVT.find k_k_map k
                                       of NONE => CVS.singleton k'
                                        | SOME ks => CVS.add (ks, k'))
      (* b_k_lv maps cvars to the set of lvars that are bound along any reference to the cvar *)
      val b_k_lv = CVT.mkTable(128, Fail "b_k_lv")
      fun add_b_k_lv (k, lv) =
          CVT.insert b_k_lv (k, case CVT.find b_k_lv k
                                      of NONE => lv
                                       | SOME lvs => LVS.union (lvs, lv))
      (* b_k_ld maps cvars to the set of ldata that are bound along any reference to the cvar *)
      val b_k_ld = CVT.mkTable(128, Fail "b_k_lv")
      fun add_b_k_ld (k, ld) =
          CVT.insert b_k_ld (k, case CVT.find b_k_ld k
                                      of NONE => ld
                                       | SOME lds => LS.union (lds, ld))
      fun bound_exp (exp as C.EXP(l, e))
                    (in_k, bv : LVS.set, bd : LS.set) : unit = (
          case e
           of C.LETFUN(bindings, body) => let
               val (bv, bd) =
                   List.foldl (fn ((f, lam as (lam_lab, _, _, _)), (bv, bd)) =>
                                  (bound_lam lam; (LVS.add(bv, f), LS.add(bd, lam_lab))))
                              (bv, bd) bindings
           in bound_exp body (in_k, bv, bd) end
            | C.LETCONT(bindings, body) => let
                val _ = List.app (fn (k, lamK) => bound_lamK lamK (SOME k, LVS.empty, LS.empty)) bindings
            in bound_exp body (in_k, bv, bd) end
            | C.IF(oper, args, thn, els) => (bound_exp thn (in_k, bv, bd); bound_exp els (in_k, bv, bd))
            | C.ATOM (arg, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)

            | C.PURE (oper, args, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)
            | C.ARITH (oper, args, x, e', e_exn) =>
              (bound_exp e' (in_k, LVS.add (bv, x), bd);
               bound_exp e_exn (in_k, bv, bd))
            | C.GET (oper, args, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)
            | C.SET (oper, args, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)

            | C.TUPLE (args, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)
            | C.SELECT (offset, arg, x, e') => bound_exp e' (in_k, LVS.add (bv, x), bd)

            | C.DCAPPLY (dcon, tys, arg, x, e') =>
              bound_exp e' (in_k, LVS.add (bv, x), bd)
            | C.SWITCH (arg, pats) =>
              List.app (fn (pat, e') => bound_pat (pat, e') (in_k, bv, bd)) pats

            | C.APPLY (f, tys, args, argKs) =>
              (add_b_pop_lv (l, bv);
               add_b_pop_ld (l, bd);
               List.app (fn k =>
                            (add_b_k_lv (k, bv);
                             add_b_k_ld (k, bd);
                             case in_k
                              of SOME in_k =>
                                 (add_k_pop_map (in_k, l);
                                  add_k_k_map (in_k, k))
                               | NONE => ()))
                        argKs)
            | C.THROW (k, args) =>
              (add_b_pop_lv (l, bv);
               add_b_pop_ld (l, bd);
               add_b_k_lv (k, bv);
               add_b_k_ld (k, bd);
               case in_k
                of SOME in_k => (
                    add_k_pop_map (in_k, l);
                    add_k_k_map (in_k, k)
                )
                 | NONE => ()
              )
      (* end case *))
      and bound_cont k (l, in_k, bv, bd) : unit =
          ()
      and bound_lamK (label, xs, body) (in_k, bv, bd) : unit =
          bound_exp body (in_k, LVS.addList(bv, xs), bd)
      and bound_lam (label, xs, ks, body) : unit =
          bound_exp body (NONE, LVS.addList(LVS.empty, xs), LS.empty)
      and bound_pat (pat, exp) (in_k, bv, bd) : unit =
          (case pat
            of C.VPAT x => bound_exp exp (in_k, LVS.add(bv, x), bd)
             | C.LPAT _ => bound_exp exp (in_k, bv, bd)
             | C.DCPAT(_, _, SOME x) => bound_exp exp (in_k, LVS.add(bv, x), bd)
             | C.DCPAT(_, _, NONE) => bound_exp exp (in_k, bv, bd)
          (* end case *))

      (* In the NONE cases, there is a continuation bound that is never called, so we log it *)
      fun lookup_b_k_lv k =
          case CVT.find b_k_lv k
           of SOME lv => lv
            | NONE => (DumpCPSInformation.say [ANSIText.fmt ({fg=SOME ANSIText.red, bg=NONE, bf=true, ul=false}, CVar.toString k), "\n"];
                       LVS.empty)
      fun lookup_b_k_ld k =
          case CVT.find b_k_ld k
           of SOME ld => ld
            | NONE => (DumpCPSInformation.say [ANSIText.fmt ({fg=SOME ANSIText.red, bg=NONE, bf=true, ul=false}, CVar.toString k), "\n"];
                       LS.empty)
      fun propagate wl =
          case wl
           of [] => ()
            | k::wl_rst => let
                val k_lv = lookup_b_k_lv k
                val k_ld = lookup_b_k_ld k
                val _ =
                    LS.app (fn throw => (add_b_pop_lv (throw, k_lv); add_b_pop_ld (throw, k_ld)))
                                  (case CVT.find k_pop_map k of SOME throws => throws | NONE => LS.empty)
                val wl =
                    CVS.foldl (fn (k', wl) => let
                                        val k'_lv = lookup_b_k_lv k'
                                        val k'_ld = lookup_b_k_ld k'
                                    in if not (LVS.isSubset (k_lv, k'_lv) andalso LS.isSubset (k_ld, k'_ld))
                                       then (add_b_k_lv (k', k_lv);
                                             add_b_k_ld (k', k_ld);
                                             if List.exists (fn k'' => CVar.same (k', k'')) wl then wl else k'::wl)
                                      else wl
                                    end)
                                   wl_rst (case CVT.find k_k_map k of SOME k's => k's | NONE => CVS.empty)
            in propagate wl end
      val (C.CU lam0) = cu
  in
      (bound_lam lam0;
       propagate (CVT.foldi (fn (k, _, acc) => k :: acc) [] k_k_map);
       {b_pop_lv=b_pop_lv, b_pop_ld=b_pop_ld})
  end

end
