(* proxy-info.sml
 *
 * ... *)

structure ProxyInformation : sig

  val proxy_info : CPS.comp_unit -> {local_k : CVar.Set.set,
                                     k_index : int CVar.Tbl.hash_table}

end = struct

  structure C = CPS
  structure CVS = CVar.Set
  structure CVT = CVar.Tbl

  fun proxy_info (C.CU lam0) = let
      val local_k = ref CVS.empty
      val k_index = CVT.mkTable (128, Fail "compute k_index")

      fun add_indices (ks) = let
          fun add (index, ks) =
              (case ks
                of [] => ()
                 | (k :: ks) => (CVT.insert k_index (k, index);
                                 add (index+1, ks)))
      in add (0, ks) end

      fun info_exp (exp as C.EXP (l, e)) = (case e
            of C.LETFUN(bindings, e_body) =>
               (List.app info_lam bindings;
                info_exp e_body)
             | C.LETCONT(bindingKs, e_body) =>
               (List.app info_lamK bindingKs;
                local_k := CVS.addList (! local_k, List.map #1 bindingKs);
                info_exp e_body)
             | C.IF(oper, args, e_thn, e_els) =>
               (info_exp e_thn;
                info_exp e_els)
             | C.ATOM (arg, x, e') =>
               info_exp e'

             | C.PURE (oper, args, x, e') =>
               info_exp e'
             | C.ARITH (oper, args, x, e', e_exn) =>
               (info_exp e';
                info_exp e_exn)
             | C.GET (oper, args, x, e') =>
               info_exp e'
             | C.SET (oper, args, x, e') =>
               info_exp e'

             | C.TUPLE (args, x, e') =>
               info_exp e'
             | C.SELECT (offset, arg, x, e') =>
               info_exp e'

             | C.DCAPPLY (dcon, tys, arg, x, e') =>
               info_exp e'
             | C.SWITCH (arg, pats) =>
               List.app (fn (_, e') => info_exp e') pats

             | C.APPLY (f, tys, args, argKs) => ()
             | C.THROW (k, args) => ()
          (* end case *))
      and info_lamK (_, label, lvars, e_body) : unit =
          info_exp e_body
      and info_lam (_, label, lvars, cvars, e_body) : unit =
          (add_indices cvars;
           info_exp e_body)
  in info_lam lam0;
     {local_k = ! local_k,
      k_index = k_index}
  end

end
