(* pop.sml
 *
 * Creates a mapping from call and throw labels to the cvars used at those labels which are
 *)

structure Pop : sig

  val pop : CPS.comp_unit -> {pop_cvars : (CVar.t list) Label.Tbl.hash_table,
                              pop_labels : Label.Set.set}

end = struct

  structure C = CPS
  structure LT = Label.Tbl

  (* Could use a property on CVars for this *)

  fun pop (C.CU lam0) = let
      val pop_cvars = Label.Tbl.mkTable (128, Fail "pop_cvars")
      val pop_labels = ref Label.Set.empty
      fun pop_exp (exp as C.EXP (l, e), pop) = let
          fun is_pop k = List.exists (fn k' => CVar.same (k, k')) pop
          in
            case e
             of C.LETFUN(bindings, body) =>
                (List.app pop_lam bindings;
                 pop_exp (body, pop))
              | C.LETCONT(bindings, body) =>
                (List.app (fn lamK => pop_lamK (lamK, pop)) bindings;
                 pop_exp (body, pop))
              | C.IF(oper, args, thn, els) =>
                (pop_exp (thn, pop);
                 pop_exp (els, pop))
              | C.ATOM (arg, x, e') =>
                pop_exp (e', pop)
              | C.PURE (oper, args, x, e') =>
                pop_exp (e', pop)
              | C.ARITH (oper, args, x, e', e_exn) =>
                (pop_exp (e', pop);
                 pop_exp (e_exn, pop))
              | C.GET (oper, args, x, e') =>
                pop_exp (e', pop)
              | C.SET (oper, args, x, e') =>
                pop_exp (e', pop)
              | C.TUPLE (args, x, e') =>
                pop_exp (e', pop)
              | C.SELECT (offset, arg, x, e') =>
                pop_exp (e', pop)
              | C.DCAPPLY (dcon, tys, arg, x, e') =>
                pop_exp (e', pop)
              | C.SWITCH (arg, pats) =>
                List.app (fn (_, e') => pop_exp (e', pop)) pats
              | C.APPLY (f, tys, args, argKs) => let
                  val pops = List.filter is_pop argKs
                  in
                    if (List.length pops) = (List.length argKs)
                      then pop_labels := (Label.Set.add (! pop_labels, l))
                      else ();
                    LT.insert pop_cvars (l, pops)
                  end
              | C.THROW (k, args) =>
                (if is_pop k
                 then pop_labels := (Label.Set.add (! pop_labels, l))
                 else ();
                 LT.insert pop_cvars (l, if is_pop k then [k] else []))
            (* end case *)
          end
      and pop_lamK ((k, label, xs, body), pop) : unit =
          pop_exp (body, pop)
      and pop_lam (f, label, xs, ks, body) : unit =
          pop_exp (body, ks)
      in
        pop_lam lam0;
        {pop_cvars = pop_cvars, pop_labels = ! pop_labels}
      end

end
