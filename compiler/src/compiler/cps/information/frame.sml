(* frame.sml
 * Provides information about frame allocation and pop sites,
 * including what they are and
 * the bindings and values that are viable to allocate on each. *)

structure FrameInfo : sig

  val info : CPS.comp_unit -> {
          alloc_locs : Label.t list,
          alloc_loc_choices_lv : LVar.t list Label.Tbl.hash_table,
          alloc_loc_choices_ld : Label.t list Label.Tbl.hash_table,
          local_pop : Label.t list Label.Tbl.hash_table,
          pop_past : Label.t list Label.Tbl.hash_table,
          immediate_alloc_loc_lv : Label.t LVar.Map.map,
          immediate_alloc_loc_ld : Label.t Label.Map.map,
          immediate_lam_lv : Label.t LVar.Map.map,
          immediate_lam_ld : Label.t Label.Map.map
      }

end = struct

  structure C = CPS
  structure LVS = LVar.Set
  structure LS = Label.Set
  structure LT = Label.Tbl
  structure CVM = CVar.Map
  structure LVM = LVar.Map
  structure LM = Label.Map

  fun info (cu as C.CU lam0) = let
      val alloc_locs = ref []
      val alloc_loc_choices_lv = LT.mkTable (128, Fail "compute alloc_loc_choices_lv")
      val alloc_loc_choices_ld = LT.mkTable (128, Fail "compute alloc_loc_choices_ld")
      val local_pop = LT.mkTable (128, Fail "compute local_pop")
      val pop_past = LT.mkTable (128, Fail "compute pop_past")
      val immediate_alloc_loc_lv = ref LVM.empty
      val immediate_alloc_loc_ld = ref LM.empty
      val immediate_lam_lv = ref LVM.empty
      val immediate_lam_ld = ref LM.empty

      fun init_alloc_loc loc =
          (alloc_locs := loc :: (! alloc_locs);
           LT.insert alloc_loc_choices_lv (loc, []);
           LT.insert alloc_loc_choices_ld (loc, []))
      fun add_choices (choices, x) loc =
          LT.insert choices (loc, x :: (LT.lookup choices loc))
      fun add_lv (enclosing_lam, locs) x =
          (List.app (add_choices (alloc_loc_choices_lv, x)) locs;
           immediate_lam_lv := LVM.insert (! immediate_lam_lv, x, enclosing_lam);
           case locs
            of immediate_alloc_loc :: _ => let
                val map = LVM.insert (! immediate_alloc_loc_lv, x, immediate_alloc_loc)
            in immediate_alloc_loc_lv := map end
             | _ => ())
      fun add_ld (enclosing_lam, locs) ld =
          (List.app (add_choices (alloc_loc_choices_ld, ld)) locs;
           case enclosing_lam
            of NONE => ()
             | SOME enclosing_lam => immediate_lam_ld := LM.insert (! immediate_lam_ld, ld, enclosing_lam);
           case locs
            of immediate_alloc_loc :: _ => let
                val map = LM.insert (! immediate_alloc_loc_ld, ld, immediate_alloc_loc)
            in immediate_alloc_loc_ld := map end
             | _ => ())

      (*
      val pop_sites = ref []
      val local_popped = LT.mkTable (128, Fail "compute local_popped")

      fun init_pop_loc site =
          pop_sites := site :: (! pop_sites)
      fun set_local_pop site loc_local_popped =
          LT.insert local_popped loc_local_popped
      *)

      fun label (exp as C.EXP (e_lab, _)) = e_lab

      fun init_k (k, k_map) =
          CVM.insert (k_map, k, LS.empty)
      fun add_k alloc_loc (k, k_map) =
          CVM.insert (k_map, k, LS.add (CVM.lookup (k_map, k), alloc_loc))
      fun find_local_popped (argKs, k_map) = let
          fun local_of_argK k = CVM.lookup (k_map, k)
      in List.foldl (fn (argK, acc) => LS.intersection (local_of_argK argK, acc))
                    (local_of_argK (hd argKs))
                    (tl argKs)
      end


      fun info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) (e as C.EXP(_, e_)) = (case e_
           of C.LETFUN(bindings, e_body) =>
              (List.app (info_binding (enclosing_lam, in_locs, k_map, k_local)) bindings;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.LETCONT (bindingKs, e_body) => let
                fun handleK ((k, _, _, _), k_local) = k :: k_local
                val k_local_new = List.foldl handleK [] bindingKs
                val k_map = List.foldl init_k k_map k_local_new
                val k_local = k_local_new @ k_local
                val k_map' = List.foldl (add_k (label e_body)) k_map k_local
                in List.app (info_bindingK (enclosing_lam, in_locs, local_in_locs, k_map, k_local)) bindingKs;
                   init_alloc_loc (label e_body);
                   info_exp (enclosing_lam, (label e_body) :: in_locs, (label e_body) :: local_in_locs, k_map', k_local) e_body
                end
            | C.IF (oper, args, thn, els) =>
              (info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) thn;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) els)
            | C.ATOM (arg, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.PURE (oper, args, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.ARITH (oper, args, x, e_body, e_exn) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_exn)
            | C.GET (oper, args, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.SET (oper, args, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)

            | C.TUPLE (xs, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.SELECT (offset, arg, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)

            | C.DCAPPLY (dcon, tys, arg, x, e_body) =>
              (add_lv (enclosing_lam, in_locs) x;
               info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
            | C.SWITCH (x, cases) =>
              List.app (info_case (enclosing_lam, in_locs, local_in_locs, k_map, k_local)) cases

            | C.APPLY(f, tys, args, argKs) => let
                val local_popped = find_local_popped (argKs, k_map)
                in
                  LT.insert local_pop (label (e), LS.listItems local_popped);
                  LT.insert pop_past (label (e), local_in_locs)
                end
            | C.THROW(k, args) => let
                val local_popped = CVM.lookup (k_map, k)
                in
                  LT.insert local_pop (label (e), LS.listItems local_popped)
                end
          (* end case *))
      and info_lamK (enclosing_lam, in_locs, local_in_locs, k_map, k_local) (k, lamK_lab, xs, e_body) =
          (List.app (add_lv (enclosing_lam, in_locs)) xs;
           info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) e_body)
      and info_lam (enclosing_lam, in_locs) (_, lam_lab, xs, ks, e_body) = let
          val k_map = List.foldl init_k CVM.empty ks
          val k_map = List.foldl (add_k lam_lab) k_map ks
      in
          add_ld (enclosing_lam, in_locs) lam_lab;
          init_alloc_loc lam_lab;
          List.app (add_lv (lam_lab, lam_lab :: in_locs)) xs;
          info_exp (lam_lab, lam_lab :: in_locs, [lam_lab], k_map, ks) e_body
      end
      and info_binding (enclosing_lam, in_locs, k_map, k_local) (lam as (f, _, _, _, _)) =
          (add_lv (enclosing_lam, in_locs) f;
           info_lam (SOME enclosing_lam, in_locs) lam)
      and info_bindingK (enclosing_lam, in_locs, local_in_locs, k_map, k_local) lamK =
            info_lamK (enclosing_lam, in_locs, local_in_locs, k_map, k_local) lamK
      and info_case (enclosing_lam, in_locs, local_in_locs, k_map, k_local) (pat, exp) = (case pat
            of C.VPAT x => add_lv (enclosing_lam, in_locs) x
             | C.LPAT _ => ()
             | C.DCPAT (_, _, SOME x) => add_lv (enclosing_lam, in_locs) x
             | C.DCPAT (_, _, NONE) => ()
           (* end case *);
           info_exp (enclosing_lam, in_locs, local_in_locs, k_map, k_local) exp)
  in
      info_lam (NONE, []) lam0;
      { alloc_locs = ! alloc_locs,
        alloc_loc_choices_lv = alloc_loc_choices_lv,
        alloc_loc_choices_ld = alloc_loc_choices_ld,
        local_pop = local_pop,
        pop_past = pop_past,
        immediate_alloc_loc_lv = ! immediate_alloc_loc_lv,
        immediate_alloc_loc_ld = ! immediate_alloc_loc_ld,
        immediate_lam_lv = ! immediate_lam_lv,
        immediate_lam_ld = ! immediate_lam_ld }
  end

end


