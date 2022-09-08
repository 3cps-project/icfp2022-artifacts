(* util.sml
 *
 * Computes a mapping from expression labels to the user lambda label that contains them.
 * Computes a mapping from program labels to various program constructs.
 *)

structure InfoUtil : sig

  val info : CPS.comp_unit -> {
          exps : Label.t list,                          (* comments? *)
          tuples : Label.t list,
          selects : Label.t list,
          datas : Label.t list,
          matches : Label.t list,
          lams : Label.t list,
          call_sites : Label.t list,
          lamKs : Label.t list,
          callK_sites : Label.t list,
          lvars : LVar.t list,
          cvars : CVar.t list,
          ldata : Label.t list,
          cdata : Label.t list,
          exp_lam : Label.t Label.Tbl.hash_table,
          exp : CPS.exp Label.Tbl.hash_table,
          lam : CPS.lambda Label.Tbl.hash_table,
          lamK : CPS.clambda Label.Tbl.hash_table,
          side_effect_labels : Label.t list
        }

end = struct

  structure C = CPS
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LT = Label.Tbl

  fun info (cu as C.CU lam) = let
      val exp_lam = LT.mkTable(128, Fail "exp_lam")
      val exp_tbl = LT.mkTable(128, Fail "exp")
      val lam_tbl = LT.mkTable(128, Fail "lam")
      val lamK_tbl = LT.mkTable(128, Fail "lamK")
      val side_effect_labels = ref []
      val exps = ref []
      val tuples = ref []
      val selects = ref []
      val datas = ref []
      val matches = ref []
      val lams = ref []
      val call_sites = ref []
      val lamKs = ref []
      val callK_sites = ref []
      val lvars = ref []
      val cvars = ref []
      val ldata = ref []
      val cdata = ref []
      fun add_lvar x = (lvars := x :: (! lvars))
      fun add_cvar k = (cvars := k :: (! cvars))
      fun info_exp (exp as C.EXP(l, e)) l0 : unit = (
          exps := l :: (! exps);
          LT.insert exp_lam (l, l0);
          LT.insert exp_tbl (l, exp);
          case e
           of C.LETFUN(bindings, body) => (
                List.app
                  (fn (lam as (f, _, _, _, _)) => (add_lvar f; info_lam (lam, true)))
                    bindings;
                info_exp body l0)
            | C.LETCONT(bindings, body) => (
                List.app
                  (fn (lamK as (k, _, _, _)) => (add_cvar k; info_lamK lamK l0))
                    bindings;
                info_exp body l0)
            | C.IF(oper, args, thn, els) =>
              (info_exp thn l0;
               info_exp els l0)
            | C.ATOM (arg, x, e') =>
              (case arg of C.DCON _ => datas := l :: (! datas) | _ => ();
               add_lvar x;
               info_exp e' l0)

            | C.PURE (oper, args, x, e') =>
              ((case oper
                 of PrimOp.Pure.Ref => side_effect_labels := l :: !side_effect_labels
                  | PrimOp.Pure.Array0 => side_effect_labels := l :: !side_effect_labels
                  | PrimOp.Pure.ArrayAlloc => side_effect_labels := l :: !side_effect_labels
                  | _ => ());
               add_lvar x; info_exp e' l0)
            | C.ARITH (oper, args, x, e', e_exn) =>
              (add_lvar x; info_exp e' l0; info_exp e_exn l0)
            | C.GET (oper, args, x, e') =>
              (add_lvar x; info_exp e' l0)
            | C.SET (oper, args, x, e') =>
              (add_lvar x; info_exp e' l0)

            | C.TUPLE(args, x, e') =>
              (tuples := l :: (! tuples);
               add_lvar x; 
               info_exp e' l0)
            | C.SELECT(offset, arg, x, e') =>
              (selects := l :: (! selects);
               add_lvar x; 
               info_exp e' l0)

            | C.DCAPPLY(dcon, tys, arg, x, e') =>
              (datas := l :: (! datas);
               add_lvar x; 
               info_exp e' l0)
            | C.SWITCH(arg, pats) =>
              (matches := l :: (! matches);
               List.app (fn (pat, e') => info_pat (pat, e') l0) pats)

            | C.APPLY(f, tys, args, argKs) =>
              call_sites := l :: (! call_sites)
            | C.THROW(cont, args) =>
              callK_sites := l :: (! callK_sites)
      (* end case *))
      and info_lamK (lamK as (k, label, xs, body)) l0 : unit =
          (LT.insert lamK_tbl (label, lamK);
           lamKs := label :: (! lamKs);
           cdata := label :: (! cdata);
           List.app add_lvar xs;
           info_exp body l0)
      and info_lam (lam as (f, label, xs, ks, body), is_ld) : unit =
          (LT.insert lam_tbl (label, lam);
           lams := label :: (! lams);
           if is_ld then ldata := label :: (! ldata) else ();
           List.app add_lvar xs;
           List.app add_cvar ks;
           info_exp body label)
      and info_pat (pat, exp) l0 : unit =
          ((case pat
             of C.VPAT x => add_lvar x
              | C.LPAT _ => ()
              | C.DCPAT (_, _, SOME x) => add_lvar x
              | C.DCPAT (_, _, NONE) => ());
           info_exp exp l0)
      val _ = info_lam (lam, false);
  in {exps = ! exps,
      tuples = ! tuples,
      selects = ! selects,
      datas = ! datas,
      matches = ! matches,
      lams = ! lams,
      call_sites = ! call_sites,
      lamKs = ! lamKs,
      callK_sites = ! callK_sites,
      lvars = ! lvars,
      cvars = ! cvars,
      ldata = ! ldata,
      cdata = ! cdata,
      exp_lam = exp_lam,
      exp = exp_tbl,
      lam = lam_tbl,
      lamK = lamK_tbl,
      side_effect_labels = !side_effect_labels}
  end

end
