(* bound-vars.sml
 *
 * Computes a mapping from user lambdas to the set of variables
 * and data labels that are lexically contained in that lambda
 *)

structure Contains : sig

  val contains : CPS.comp_unit -> {
          cn_lam_lv : LVar.Set.set Label.Tbl.hash_table,
          cn_lam_cv : CVar.Set.set Label.Tbl.hash_table,
          cn_lam_ld : Label.Set.set Label.Tbl.hash_table,
          icn_lam_lv : LVar.Set.set Label.Tbl.hash_table,
          icn_lam_cv : CVar.Set.set Label.Tbl.hash_table,
          icn_lam_ld : Label.Set.set Label.Tbl.hash_table,
          icn_lam_cd : Label.Set.set Label.Tbl.hash_table
        }

end = struct

  structure C = CPS
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LT = Label.Tbl

  (* NOTE: this code could be more efficient by threading the accumulator through
   * the tree walk.
   *)
  fun contains (cu as C.CU lam) = let
      val cn_lam_lv = LT.mkTable(128, Fail "compute cn_lam_lv")
      val cn_lam_cv = LT.mkTable(128, Fail "compute cn_lam_cv")
      val cn_lam_ld = LT.mkTable(128, Fail "compute cn_lam_ld")
      val icn_lam_lv = LT.mkTable(128, Fail "compute icn_lam_lv")
      val icn_lam_cv = LT.mkTable(128, Fail "compute icn_lam_cv")
      val icn_lam_ld = LT.mkTable(128, Fail "compute icn_lam_ld")
      val icn_lam_cd = LT.mkTable(128, Fail "compute icn_lam_cd")
      fun initialize_lam lam = (
            LT.insert cn_lam_lv (lam, LVS.empty);
            LT.insert cn_lam_cv (lam, CVS.empty);
            LT.insert cn_lam_ld (lam, LS.empty);
            LT.insert icn_lam_lv (lam, LVS.empty);
            LT.insert icn_lam_cv (lam, CVS.empty);
            LT.insert icn_lam_ld (lam, LS.empty);
            LT.insert icn_lam_cd (lam, LS.empty))

      fun add_lv (x, in_lams) =
          (List.app
            (fn lam => LT.insert cn_lam_lv (lam, LVS.add (LT.lookup cn_lam_lv lam, x)))
              in_lams;
           LT.insert icn_lam_lv (hd in_lams, LVS.add (LT.lookup icn_lam_lv (hd in_lams), x)))
      fun add_cv (k, in_lams) =
          (List.app
            (fn lam => LT.insert cn_lam_cv (lam, CVS.add (LT.lookup cn_lam_cv lam, k)))
              in_lams;
           LT.insert icn_lam_cv (hd in_lams, CVS.add (LT.lookup icn_lam_cv (hd in_lams), k)))
      fun add_cd (cd, in_lams) = (case in_lams
           of [] => ()
            | in_lams =>
              (LT.insert icn_lam_cd (hd in_lams, LS.add (LT.lookup icn_lam_cd (hd in_lams), cd)))
          (* end case *))
      fun add_ld (ld, in_lams) = (case in_lams
           of [] => ()
            | in_lams =>
              (List.app
                (fn lam => LT.insert cn_lam_ld (lam, LS.add (LT.lookup cn_lam_ld lam, ld)))
                  in_lams;
               LT.insert icn_lam_ld (hd in_lams, LS.add (LT.lookup icn_lam_ld (hd in_lams), ld)))
          (* end case *))
      fun containseExp (exp as C.EXP(label, e), in_lams) =
          case e
           of C.LETFUN(bindings, body) => (
                List.app
                  (fn lam => (containsLam (lam, in_lams); add_lv (#1 lam, in_lams)))
                    bindings;
                containseExp (body, in_lams))
            | C.LETCONT (bindings, body) => (
                List.app
                  (fn lamK => (containsLamK (lamK, in_lams); add_cv (#1 lamK, in_lams)))
                    bindings;
                containseExp (body, in_lams))
            | C.IF(oper, args, thn, els) => (containseExp (thn, in_lams); containseExp (els, in_lams))
            | C.ATOM (arg, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))
            | C.PURE (oper, args, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))
            | C.ARITH (oper, args, x, e', e_exn) => (add_lv (x, in_lams); containseExp (e', in_lams); containseExp (e_exn, in_lams))
            | C.GET (oper, args, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))
            | C.SET (oper, args, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))

            | C.TUPLE(xs, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))
            | C.SELECT(offset, arg, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))

            | C.DCAPPLY(dcon, tys, arg, x, e') => (add_lv (x, in_lams); containseExp (e', in_lams))
            | C.SWITCH(x, cases) =>
              List.app (fn (pat, exp) =>
                           (case pat
                             of C.VPAT x => add_lv (x, in_lams)
                              | C.LPAT _ => ()
                              | C.DCPAT (_, _, SOME x) => add_lv (x, in_lams)
                              | C.DCPAT (_, _, NONE) => ();
                            containseExp (exp, in_lams)))
                       cases

            | C.APPLY(f, tys, args, argKs) => ()
            | C.THROW(k, args) => ()
      and containsLamK ((_, lab, uvars, body), in_lams) =
          (add_cd (lab, in_lams);
           List.app (fn x => add_lv (x, in_lams)) uvars;
           containseExp (body, in_lams))
      and containsLam ((_, lab, uvars, cvars, body), in_lams) =
          (initialize_lam lab;
           add_ld (lab, in_lams);
           List.app (fn x => add_lv (x, lab::in_lams)) uvars;
           List.app (fn k => add_cv (k, lab::in_lams)) cvars;
           containseExp (body, lab::in_lams))
  in
      containsLam (lam, []);
      { cn_lam_lv = cn_lam_lv,
        cn_lam_cv = cn_lam_cv,
        cn_lam_ld = cn_lam_ld,
        icn_lam_lv = icn_lam_lv,
        icn_lam_cv = icn_lam_cv,
        icn_lam_ld = icn_lam_ld,
        icn_lam_cd = icn_lam_cd
      }
  end

end
