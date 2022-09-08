(* redundant-selection.sml
 *
 *)

structure CPSRedundantSelection : sig

  val redundant_selection : CPS.comp_unit -> CPS.comp_unit option

  type stats = {elim_select_count : int,
                elim_switch_count : int}
  val stats : unit -> stats

end = struct

  type stats = {elim_select_count : int,
                elim_switch_count : int}
  val st = ref {elim_select_count=0,
                elim_switch_count=0}
  fun stats () = !st
  fun incr_elim_select_count n = let
      val {elim_select_count=elim_select_count,
           elim_switch_count=elim_switch_count} = !st
  in st := {elim_select_count=elim_select_count + n,
            elim_switch_count=elim_switch_count}
  end
  fun incr_elim_switch_count n = let
      val {elim_select_count=elim_select_count,
           elim_switch_count=elim_switch_count} = !st
  in st := {elim_select_count=elim_select_count,
            elim_switch_count=elim_switch_count + n}
  end


  structure C = CPS
  structure LVT = LVar.Tbl
  structure CVT = CVar.Tbl

  datatype data = LIT of Literal.t * C.ty
                | EMPTYDCON of C.dcon * C.ty list
                | DCON of C.dcon * C.ty list * C.lvar

  fun redundant_selection (C.CU lam0) = let
      val has_changed = ref false
      fun changed () = (has_changed := true)
      (* killing things out of the tables may improve running time *)
      val lvarTuple = LVar.Tbl.mkTable (100, Fail "CPSRedundantSelection.lvarTuple")
      fun find_lvar_tuple x = LVT.find lvarTuple x
      fun init_lvar_tuple (x : LVar.t, shape : LVar.t list) = LVT.insert lvarTuple (x, shape)
      fun copy_lvar_tuple (x, y) =
          (case LVT.find lvarTuple y
            of NONE => ()
             | SOME shape => LVT.insert lvarTuple (x, shape))
      fun destroy_lvar_tuple x = ((LVT.remove lvarTuple x; ()) handle _ => ())
      val lvarData = LVar.Tbl.mkTable (100, Fail "CPSRedundantSelection.lvarData")
      fun find_lvar_data x = LVT.find lvarData x
      fun init_lvar_data (x : LVar.t, shape : data) = LVT.insert lvarData (x, shape)
      fun copy_lvar_data (x, y) =
          (case LVT.find lvarData y
            of NONE => ()
             | SOME shape => LVT.insert lvarData (x, shape))
      fun destroy_lvar_data x = ((LVT.remove lvarData x; ()) handle _ => ())
      fun simplify_exp (exp as C.EXP (lab_e, e)) = 
	  case e
	   of C.LETFUN(bindings, body) => let
	       val body = simplify_exp body
               val bindings = List.map simplify_lam bindings
           in C.EXP (lab_e, C.LETFUN (bindings, body)) end
	    | C.LETCONT(bindingKs, body) => let
		val body = simplify_exp body
                val bindingKs = List.map simplify_lamK bindingKs
            in C.EXP (lab_e, C.LETCONT (bindingKs, body)) end
	    | C.IF(oper, args, thn, els) => let
		val thn = simplify_exp thn
		val els = simplify_exp els
	    in C.EXP (lab_e, C.IF (oper, args, thn, els)) end
	    | C.ATOM (arg, x, e') => let
                val _ = case arg
                         of C.LIT lit => init_lvar_data (x, LIT lit)
                          | C.DCON dcon => init_lvar_data (x, EMPTYDCON dcon)
                          | _ => ()
		val e' = simplify_exp e'
                val _ = destroy_lvar_data x
            in C.EXP (lab_e, C.ATOM (arg, x, e')) end
	    | C.PURE (oper, args, x, e') => let
		val e' = simplify_exp e'
            in C.EXP (lab_e, C.PURE (oper, args, x, e')) end
	    | C.ARITH (oper, args, x, e', e_exn) => let
		val e' = simplify_exp e'
		val e_exn = simplify_exp e_exn
            in C.EXP (lab_e, C.ARITH (oper, args, x, e', e_exn)) end
	    | C.GET (oper, args, x, e') => let
		val e' = simplify_exp e'
            in C.EXP (lab_e, C.GET (oper, args, x, e')) end
	    | C.SET (oper, args, x, e') => let
		val e' = simplify_exp e'
            in C.EXP (lab_e, C.SET (oper, args, x, e')) end
	    | C.TUPLE(args, x, e') => let
                val _ = init_lvar_tuple (x, args)
                val e' = simplify_exp e'
                val _ = destroy_lvar_tuple x
            in C.EXP (lab_e, C.TUPLE (args, x, e')) end
	    | C.SELECT(offset, arg, x, e') => 
              (case find_lvar_tuple arg
                of NONE => let
                    val e' = simplify_exp e'
                in C.EXP (lab_e, C.SELECT (offset, arg, x, e')) end
                 | SOME ys => let
                     val y = List.nth (ys, offset-1) handle Subscript => (print ((LVar.toString arg) ^ " " ^
                                                                                 (Int.toString offset) ^ " " ^
                                                                                 (String.concat (List.map LVar.toString ys)));
                                                                          raise Subscript)
                     val _ = copy_lvar_tuple (x, y)
                     val _ = copy_lvar_data (x, y)
                     val e' = simplify_exp e'
                     val _ = destroy_lvar_tuple x
                     val _ = destroy_lvar_data x
                     val () = changed ()
                     val _ = incr_elim_select_count 1
                 in C.EXP (lab_e, C.ATOM (C.LVAR (y, []), x, e')) end)
	    | C.DCAPPLY(dcon, tys, arg, x, e') => let
                val _ = init_lvar_data (x, DCON (dcon, tys, arg))
                val e' = simplify_exp e'
                val _ = destroy_lvar_data x
            in C.EXP (lab_e, C.DCAPPLY (dcon, tys, arg, x, e')) end
	    | C.SWITCH(arg, pats) => 
              (case find_lvar_data arg
                of NONE => let
		    fun simplify_pat (pat, e') = (pat, simplify_exp e')
	            val pats = List.map simplify_pat pats
                in C.EXP (lab_e, C.SWITCH (arg, pats)) end
                 | SOME data => let
                     fun find_pat (_, []) = raise Fail "CPSRedundantSelection.find_pat: no pattern" (* maybe we shouldn't fail here since programs don't need to have all the matches... *)
                       | find_pat (_, (C.VPAT x, e') :: rest_pats) = let
                           val _ = copy_lvar_tuple (x, arg)
                           val _ = copy_lvar_data (x, arg)
                           val e' = simplify_exp e'
                           val _ = destroy_lvar_tuple x
                           val _ = destroy_lvar_data x
                           val () = changed ()
                           val _ = incr_elim_switch_count 1
                       in C.EXP (lab_e, C.ATOM (C.LVAR (arg, []), x, e')) end
                       | find_pat (LIT (lit, ty), (C.LPAT (lit', ty'), e') :: rest_pats) =
                         if Literal.same (lit, lit') andalso CPSTypes.same (ty, ty')
                         then let
                             val e' = simplify_exp e'
                             val () = changed ()
                             val _ = incr_elim_switch_count 1
                         in e' end
                         else find_pat (data, rest_pats)
                       | find_pat (EMPTYDCON (dcon, tys), (C.DCPAT (dcon', tys', NONE), e') :: rest_pats) =
                         if CPSDataCon.same (dcon, dcon') andalso ListPair.all CPSTypes.same (tys, tys')
                         then let
                             val e' = simplify_exp e'
                             val () = changed ()
                             val _ = incr_elim_switch_count 1
                         in e' end
                         else find_pat (data, rest_pats)
                       | find_pat (DCON (dcon, tys, arg), (C.DCPAT (dcon', tys', SOME x), e') :: rest_pats) =
                         if CPSDataCon.same (dcon, dcon') andalso ListPair.all CPSTypes.same (tys, tys')
                         then let
                             val _ = copy_lvar_tuple (x, arg)
                             val _ = copy_lvar_data (x, arg)
                             val e' = simplify_exp e'
                             val _ = destroy_lvar_tuple x
                             val _ = destroy_lvar_data x
                             val () = changed ()
                             val _ = incr_elim_switch_count 1
                         in C.EXP (lab_e, C.ATOM (C.LVAR (arg, []), x, e')) end
                         else find_pat (data, rest_pats)
                       | find_pat (_, _ :: rest_pats) = find_pat (data, rest_pats)
                 in find_pat (data, pats) end)
	    | C.APPLY(f, tys, args, argKs) => 
		C.EXP (lab_e, C.APPLY (f, tys, args, argKs)) 
	    | C.THROW(k, args) => C.EXP (lab_e, C.THROW (k, args)) 
	  (* end case *)
	  and simplify_lamK (lamK as (k, lamK_lab, xs, body)) = let
	      val body = simplify_exp body
	  in (k, lamK_lab, xs, body) end
	  and simplify_lam (lam as (f, lam_lab, xs, ks, body)) = let
	      val body = simplify_exp body
	  in (f, lam_lab, xs, ks, body) end
      val cu = C.CU (simplify_lam lam0)
  in if !has_changed
     then SOME cu
     else NONE
  end

end
