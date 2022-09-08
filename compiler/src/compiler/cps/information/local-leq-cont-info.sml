(* local-leq-cont-info.sml
 *
 * For each cont var k, gives back the set of cont vars {k', ...} for
 * which k <= k' is possible; i.e. the definition of k is in the scope
 * of k'.
 * Additionally, for each cont lam lamK, gives back the set {lamK', ...}
 * for which lamK <= lamK' is possible; that is, at a call site,
 * it is possible that lamK and lamK' both appear in the proxy
 * (meaning either they are a direct argument or a cont var was bound
 * to them in the innermost user lambda that contains the call site)
 *)

structure LocalLeqContInformation =
struct

  structure C = CPS

  structure CVS = CVar.Set
  structure CVT = CVar.Tbl
  structure LS = Label.Set
  structure LT = Label.Tbl

  fun info (C.CU lam0) = let
      val info_ks = CVT.mkTable (128, Fail "info_ks")
      val info_lamKs = LT.mkTable (128, Fail "info_lamKs")
      fun add_ks (ks, ks_) =
          List.app (fn k => CVT.insert info_ks (k, ks_)) ks
      fun add_lamKs (lamKs, lamKs_) =
          List.app (fn lamK => LT.insert info_lamKs (lamK, lamKs_)) lamKs
      (* ks_ tracks the cont vars that can be called from the current
         expression, and lamKs_ tracks the continuation lambdas that
         could be called locally from the current expression *)
      fun info_exp (exp as C.EXP (l, e), ks_, lamKs_) =
          case e
           of C.LETFUN(bindings, body) => (
                List.app info_lam bindings;
                info_exp (body, ks_, lamKs_))
            | C.LETCONT(bindingKs, body) => let
                val ks = List.foldl (fn ((k, _, _, _), acc) => k :: acc) [] bindingKs
                val lamKs = List.foldl
                      (fn (lamK as (_, lamK_lab, _, _), acc) => lamK_lab :: acc)
                        [] bindingKs
                val ks_' = CVS.addList (ks_, ks)
                val lamKs_' = LS.addList (lamKs_, lamKs)
                in
                  add_ks (ks, ks_');
                  add_lamKs (lamKs, lamKs_');
                  List.app (fn lamK => info_lamK (lamK, ks_', lamKs_')) bindingKs;
                  info_exp (body, ks_', lamKs_')
                end
            | C.IF(oper, args, thn, els) =>
              (info_exp (thn, ks_, lamKs_);
               info_exp (els, ks_, lamKs_))
            | C.ATOM (arg, x, e') =>
              info_exp (e', ks_, lamKs_)

            | C.PURE (oper, args, x, e') =>
              info_exp (e', ks_, lamKs_)
            | C.ARITH (oper, args, x, e', e_exn) =>
              (info_exp (e', ks_, lamKs_);
               info_exp (e_exn, ks_, lamKs_))
            | C.GET (oper, args, x, e') =>
              info_exp (e', ks_, lamKs_)
            | C.SET (oper, args, x, e') =>
              info_exp (e', ks_, lamKs_)

            | C.TUPLE (args, x, e') =>
              info_exp (e', ks_, lamKs_)
            | C.SELECT (offset, arg, x, e') =>
              info_exp (e', ks_, lamKs_)

            | C.DCAPPLY (dcon, tys, arg, x, e') =>
              info_exp (e', ks_, lamKs_)
            | C.SWITCH (arg, pats) =>
              List.app (fn (_, e') => info_exp (e', ks_, lamKs_)) pats

            | C.APPLY (f, tys, args, argKs) => ()
            | C.THROW (k, args) => ()
      (* end case *)
      and info_lamK ((_, _, _, body), ks_, lamKs_) =
            info_exp (body, ks_, lamKs_)
      and info_lam (_, _, _, ks, body) = let
            val ks_ = CVS.fromList ks
            in
              add_ks (ks, ks_);
              info_exp (body, ks_, Label.Set.empty)
            end
  in info_lam lam0;
     {possible_leq_ks = info_ks, leq_lamKs = info_lamKs}
  end

end
