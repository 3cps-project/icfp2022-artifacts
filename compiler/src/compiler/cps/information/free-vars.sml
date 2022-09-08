 (* free-vars.sml
 *
 * Computes a mapping from expressions to the set of free vars at that expression
 *)

structure FreeVars : sig

(* QUESTION: why do we need different tables for expressions and lambdas?
   BQ ANSWER: I like to treat the labels for different categories as different types.
              Eventually, we could merge these once we've fully settled on the 3CPS IR *)

  val freeVars : CPS.comp_unit -> {fv_exp_lv  : LVar.Set.set Label.Tbl.hash_table,
                                   fv_exp_cv  : CVar.Set.set Label.Tbl.hash_table,
                                   fv_lam_lv : LVar.Set.set Label.Tbl.hash_table,
                                   fv_lam_cv : CVar.Set.set Label.Tbl.hash_table,
                                   fv_lamK_lv : LVar.Set.set Label.Tbl.hash_table,
                                   fv_lamK_cv : CVar.Set.set Label.Tbl.hash_table}

end = struct

  structure C = CPS
  structure LT = Label.Tbl
  structure LVS = LVar.Set
  structure CVS = CVar.Set

  (* NOTE: this code could be more efficient by threading the accumulator through
   * the tree walk.
   * BQ: I tried that, but it was actually slower.
     See commit 4ae8d7d1d93e85cc5be338e19440da28b92d6069

     Update: changing variable generation so that they are indexed 1...n
     means we could use bit vectors instead, which would be better.
     The bit vectors could then be turned into lists of free vars.
   *)
  fun freeVars (cu as C.CU lam0) = let
      val fv_exp_lv = LT.mkTable(128, Fail "fv_exp_lv")
      val fv_exp_cv = LT.mkTable(128, Fail "fv_exp_cv")
      val fv_lam_lv = LT.mkTable(128, Fail "fv_lam_lv")
      val fv_lam_cv = LT.mkTable(128, Fail "fv_lam_cv")
      val fv_lamK_lv = LT.mkTable(128, Fail "fv_lamK_lv")
      val fv_lamK_cv = LT.mkTable(128, Fail "fv_lamK_cv")
      fun lvs_union (fv_lv, fv_lv') = 
          if (LVS.numItems fv_lv) < (LVS.numItems fv_lv')
          then LVS.union (fv_lv', fv_lv)
          else LVS.union (fv_lv, fv_lv')
      fun cvs_union (fv_cv, fv_cv') = 
          if (CVS.numItems fv_cv) < (CVS.numItems fv_cv')
          then CVS.union (fv_cv', fv_cv)
          else CVS.union (fv_cv, fv_cv')
      (* returns the freeVar set of e, and adds the free var sets
         (both user and continuation vars) of e to the correct tbls (via mutation)
       *)
      fun union ((fv_lv, fv_cv), (fv_lv', fv_cv')) =
          (lvs_union (fv_lv, fv_lv'), cvs_union (fv_cv, fv_cv'))
      fun subtract ((fv_lv, fv_cv), (lvs, cvs)) =
          (LVS.subtractList (fv_lv, lvs), CVS.subtractList (fv_cv, cvs))
      fun freeVars_exp (exp as C.EXP(label, e)) = let
          val (fv_lv, fv_cv) = (case e
                 of C.LETFUN(bindings, body) => let
                     val lvs = List.map (fn lam => #1 lam) bindings
                     val fv_body = freeVars_exp body
                     val fv = List.foldl
                                  (fn (lam, fv) => union (fv, freeVars_lam lam))
                                  fv_body bindings
                     val fv = subtract (fv, (lvs, []))
                 in fv end
                  | C.LETCONT(bindings, body) => let
                      val cvs = List.map (fn lamK => #1 lamK) bindings
                      val fv_body = freeVars_exp body
                      val fv = List.foldl
                                   (fn (lamK, fv) => union (fv, freeVars_lamK lamK))
                                   fv_body bindings
                      val fv = subtract (fv, ([], cvs))
                  in fv end
                  | C.IF(oper, args, thn, els) => let
                      val (fv_lv, fv_cv) = union (freeVars_exp thn, freeVars_exp els)
                      in (LVS.addList (fv_lv, args), fv_cv) end
                  | C.ATOM (arg, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                      val fv_lv = LVS.subtract (fv_lv, x)
                      val fv_lv = (case arg
                              of C.LVAR (x, _) => LVS.add(fv_lv, x)
                               | _ => fv_lv
                             (* end case *))
                      in
                        (fv_lv, fv_cv)
                       end

                  | C.PURE (oper, args, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in (LVS.addList (LVS.subtract (fv_lv, x), args), fv_cv) end
                  | C.ARITH (oper, args, x, e', e_exn) => let
                      val (fv_lv, fv_cv) = freeVars_exp e_exn
                      val (fv_lv', fv_cv') = freeVars_exp e'
                  in (LVS.addList (lvs_union (fv_lv, LVS.subtract (fv_lv', x)), args),
                      cvs_union (fv_cv, fv_cv'))
                  end
                  | C.GET (oper, args, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in (LVS.addList (LVS.subtract (fv_lv, x), args), fv_cv) end
                  | C.SET (oper, args, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in (LVS.addList (LVS.subtract (fv_lv, x), args), fv_cv) end

                  | C.TUPLE(args, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in
                      (LVS.addList(LVS.subtract (fv_lv, x), args), fv_cv)
                  end
                  | C.SELECT(offset, arg, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in
                      (LVS.add(LVS.subtract (fv_lv, x), arg), fv_cv)
                  end

                  | C.DCAPPLY(dcon, tys, arg, x, e') => let
                      val (fv_lv, fv_cv) = freeVars_exp e'
                  in
                      (LVS.add (LVS.subtract (fv_lv, x), arg), fv_cv)
                  end
                  | C.SWITCH(arg, cases) =>
                    List.foldl (fn ((pat, e'), fv) => let
                                    val (fv_lv', fv_cv') = freeVars_exp e'
                                    val fv_lv' = case pat
                                                  of (C.VPAT x) => LVS.subtract (fv_lv', x)
                                                   | (C.DCPAT(_, _, SOME x)) => LVS.subtract (fv_lv', x)
                                                   | _ => fv_lv'
                                in union ((fv_lv', fv_cv'), fv) end)
                               (LVS.singleton arg, CVS.empty) cases

                  | C.APPLY(f, tys, args, argKs) =>
                    (LVS.fromList (f :: args), CVS.fromList argKs)
                  | C.THROW(k, args) => (LVS.fromList args, CVS.singleton k)
                (* end case *))
          in
              LT.insert fv_exp_lv (label, fv_lv);
              LT.insert fv_exp_cv (label, fv_cv);
              (fv_lv, fv_cv)
          end (* freeVars_exp *)
      and freeVars_lamK (k, label, uvars, body) = let
          val (fv_lv, fv_cv) = freeVars_exp body
          val fv_lv = LVS.subtractList (fv_lv, uvars)
          in
            LT.insert fv_lamK_lv (label, fv_lv);
            LT.insert fv_lamK_cv (label, fv_cv);
            (fv_lv, CVS.subtract (fv_cv, k))
          end
      and freeVars_lam (f, label, uvars, cvars, body) = let
          val (fv_lv, fv_cv) = freeVars_exp body
          val fv_lv = LVS.subtractList (fv_lv, uvars)
          val fv_cv = CVS.subtractList (fv_cv, cvars)
          in
            LT.insert fv_lam_lv (label, fv_lv);
            LT.insert fv_lam_cv (label, fv_cv);
            (LVS.subtract (fv_lv, f), fv_cv)
          end
      in
        freeVars_lam lam0;
        { fv_exp_lv = fv_exp_lv,
          fv_exp_cv = fv_exp_cv,
          fv_lam_lv = fv_lam_lv,
          fv_lam_cv = fv_lam_cv,
          fv_lamK_lv = fv_lamK_lv,
          fv_lamK_cv = fv_lamK_cv
        }
      end

end (* FreeVars *)
