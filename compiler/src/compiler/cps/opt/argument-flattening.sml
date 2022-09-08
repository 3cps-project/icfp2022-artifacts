(* argument-flattening.sml
 *
 * TODO
 *)

(* FIXME: should be called ArgumentFlattening or just Flattening) and not be exported
 * from the CPS library.
 *)
structure CPSArgumentFlattening : sig

    val transform : CPS.comp_unit * {user : CallWebs.t, cont : CallWebs.t} -> CPS.comp_unit

  end = struct

    structure C = CPS
    structure LVS = LVar.Set
    structure LS = Label.Set
    structure LVT = LVar.Tbl
    structure CVT = CVar.Tbl
    structure LT = Label.Tbl

    structure IntTbl = IntHashTable

    (* First, collect a list of forms for each variable, and a list of
       var, offset selects. A form is a representation of the tuple
       structure for that variable. Then, we do the following to a
       fixpoint:
       - Go through each call web; if there is a flattening
	 that can occur, then do it, and add revise the form for the
	 parameters of the lambdas of the call web.
       - Go through each select; if the variable arg can be selected off
	 of, change the form of the defined variable to selecting off of
	 the variable arg's form and remove the select from the list.
       Then, go through the program with an environment mapping
       variables with what they should be replaced with.
       When translating a call / throw, we use the unified form information
       at the call / throw to expand the number of arguments.

** FIXME: a better approach is to build a contraction/shrinking pass that will remove
** unused code.  In this way, argument flattening becomes simpler.

       When translating an expression, we translate the sub-expressions
       and use the free variable sets of those subexpressions to
       determine whether the current expression / definition is needed.
       This will remove old contructed tuples that are not needed anymore.
       Additionally, we remove selects that are no longer needed.
       When translating a lambda, we first translate the body. The issue
       is that there may be references to tuples that appeared in the
       original source, or that have not been created at all. We then
       insert any needed tuple constructions at the beginning of the
       lambda. Finally, we expand the parameters to match the
       specification of the call web.
    *)

    (* count the number of argument flattens *)
    structure ST = Stats

    val cntrs = ST.Group.newWithPri ST.Group.root ("argument flatten", [2, 0])
    local
	val newCntr = ST.Counter.new cntrs
    in
    val cntFlatten = newCntr "flattens"
    end

    (* The results from this module may look strange.
       For example, suppose there was a function f that appears at two call sites:
       (f a1 ... am k1 ... km)
       (f b1 ... bm j1 ... jm)
       and only the first is in the call web of f's lambda,
       due to the second being unreachable code.
       Then only the first call will have argument flattening done,
       and the second will still have m arguments.
     *)

    datatype abstract_form = AAtom | ATuple of abstract_form list
    datatype form = Atom of LVar.t | Tuple of LVar.t * (LVar.t list)

    (* FIXME: I make new variables everywhere, since I don't know what
       to do about properties and such. Likely, we will add type
       information and stuff here, but separate passed can recompute
       properties. *)
    fun newLVar x : LVar.t =
	LVar.newTmp (LVar.prefixOf x, CPSTypes.TyScheme ([], CPSTypes.TupleTy []), Extent.HEAP)
    fun newLVar_index (x, index) : LVar.t =
	LVar.newTmp (LVar.prefixOf x, CPSTypes.TyScheme ([], CPSTypes.TupleTy []), Extent.HEAP)
    fun newCVar k : CVar.t =
	CVar.newTmp (CVar.prefixOf k, CPSTypes.ContTy [], Extent.HEAP)

    (* Compute the form of each variable. *)
    fun computeForms (C.CU lam0) = let
	val form_tbl = LVT.mkTable (100, Fail "computeForms.form_tbl")
	val env = LVT.mkTable (100, Fail "computeForms.env")
	val envK = CVT.mkTable (100, Fail "computeForms.envK")
	val params_tbl = LT.mkTable (100, Fail "computeForms.params_tbl")
	val args_tbl = LT.mkTable (100, Fail "computeForms.args_tbl")
	val selects = ref []
	fun add x = LVT.insert env (x, newLVar x)
	fun addK k = CVT.insert envK (k, newCVar k)
	fun addAtom x =
	    (add x;
	     LVT.insert form_tbl (x, Atom x))
	fun addTuple (x, xs) = let
	    val _ = add x
	    val form = Tuple (x, xs)
	in LVT.insert form_tbl (x, form) end
	fun add_params (lam_lab, xs) =
	    LT.insert params_tbl (lam_lab, xs)
	fun add_args (lab_e, args) =
	    LT.insert args_tbl (lab_e, args)
	fun do_exp (exp as C.EXP (lab_e, e)) =
	    case e
	     of C.LETFUN (bindings, body) => (
		 List.app (fn (f, _, _, _, _) => addAtom f) bindings;
		 List.app (fn lam => do_lam lam) bindings;
		 do_exp body)
	      | C.LETCONT (bindingKs, body) => (
		  List.app (fn lamK => do_lamK lamK) bindingKs;
		  List.app (fn (k, _, _, _) => addK k) bindingKs;
		  do_exp body)
	      | C.IF (oper, args, thn, els) =>
		(do_exp thn;
		 do_exp els)
	      | C.ATOM (arg, x, e') =>
		(addAtom x;
		 do_exp e')

	      | C.PURE (oper, args, x, e') =>
		(addAtom x;
		 do_exp e')
	      | C.ARITH (oper, args, x, e', e_exn) =>
		(addAtom x;
		 do_exp e';
		 do_exp e_exn)
	      | C.GET (oper, args, x, e') =>
		(addAtom x;
		 do_exp e')
	      | C.SET (oper, args, x, e') =>
		(addAtom x;
		 do_exp e')

	      | C.TUPLE(args, x, e') =>
		(addTuple (x, args);
		 do_exp e')
	      | C.SELECT(offset, arg, x, e') =>
		(addAtom x;
		 selects := (x, offset, arg) :: (! selects);
		 do_exp e')

	      | C.DCAPPLY(dcon, tys, arg, x, e') =>
		(addAtom x;
		 do_exp e')
	      | C.SWITCH(arg, pats) =>
		List.app (fn (pat, e') => do_pat (pat, e')) pats

	      | C.APPLY(f, tys, args, argKs) => add_args (lab_e, args)
	      | C.THROW(cont, args) => add_args (lab_e, args)
	(* end case *)
	and do_lamK (lamK as (k, lamK_lab, xs, body)) =
	    (List.app addAtom xs;
	     add_params (lamK_lab, xs);
	     do_exp body)
	and do_lam (lam as (f, lam_lab, xs, ks, body)) =
	    (List.app addAtom xs;
	     List.app addK ks;
	     add_params (lam_lab, xs);
	     do_exp body)
	and do_pat (pat, exp) =
	    ((case pat
	       of C.VPAT x => addAtom x
		| C.LPAT _ => ()
		| C.DCPAT (_, _, SOME x) => addAtom x
		| C.DCPAT (_, _, NONE) => ());
	     do_exp exp)
	val _ = add (#1 lam0)
	val _ = do_lam lam0
    in (env, envK, form_tbl, params_tbl, args_tbl, ! selects) end

    (* Unify two abstract forms *)
    fun unify (aform1, aform2) =
	case (aform1, aform2)
	 of (AAtom, AAtom) => AAtom
	  | (AAtom, _) => AAtom
	  | (_, AAtom) => AAtom
	  | (ATuple aforms1, ATuple aforms2) =>
	    ATuple (ListPair.map (fn (aform1', aform2') => unify (aform1', aform2')) (aforms1, aforms2))
    (* Unify two abstract form lists *)
    fun unify_list (aform_list1, aform_list2) =
	ListPair.map unify (aform_list1, aform_list2)

    (* Obtain the abstract form of a form *)
    fun abstractForm form_tbl form =
	case form
	 of Atom _ => AAtom
	  | Tuple (_, xs) => ATuple (List.map (fn x => abstractForm form_tbl (LVT.lookup form_tbl x)) xs)
    (* Obtain the list of abstract form of a list of form *)
    and abstractForm_list form_tbl form_list =
	List.map (abstractForm form_tbl) form_list

    (* TODO *)
    fun extendParam (env_tbl, form_tbl) (x, aform) =
	((* Verbose.say ["extending ", LVar.toString x, "\n"]; *)
	case (LVT.lookup form_tbl x, aform)
	 of (Atom x, AAtom) => ()
	  | (Tuple _, AAtom) => ()
	  | (Atom x, ATuple aform_list) => let
	      val xs = List.mapi (fn (index, _) => newLVar_index (x, index)) aform_list
	  in
	      ST.Counter.tick cntFlatten;
	      List.appi (fn (index, x) => LVT.insert env_tbl (x, x)) xs;
	      LVT.insert form_tbl (x, Tuple (x, xs));
	      List.app (fn x => LVT.insert form_tbl (x, Atom x)) xs;
	      extendParam_list (env_tbl, form_tbl) (xs, aform_list)
	  end
	  | (Tuple (x, xs), ATuple aform_list) =>
	    extendParam_list (env_tbl, form_tbl) (xs, aform_list))
    (* TODO *)
    and extendParam_list (env_tbl, form_tbl) (xs, aform_list) =
	ListPair.app (extendParam (env_tbl, form_tbl)) (xs, aform_list)

    (* TODO *)
(* FIXME: if you are going to use imperative data structures, then you don't need
 * to have them as iteration arguments.  Make them free variables instead.
 *)
    fun fixpoint (call_webs : CallWebs.web list,
		  call_websK : CallWebs.web list,
		  env_tbl : LVar.t LVT.hash_table,
		  envK_tbl : CVar.t CVT.hash_table,
		  form_tbl : form LVT.hash_table,
		  params_tbl : (LVar.t list) LT.hash_table,
		  args_tbl : (LVar.t list) LT.hash_table,
		  aform_tbl : (abstract_form list) IntTbl.hash_table,
		  aform_tblK : (abstract_form list) IntTbl.hash_table,
		  selects : (LVar.t * int * LVar.t) list,
		  killed_selects_tbl : bool LVT.hash_table) = let
	val changed = ref false
	fun handle_web aform_tbl (index, {calls, lams, unknown_call, unknown_lam}) =
	    if (IntTbl.inDomain aform_tbl index andalso (unknown_call orelse unknown_lam))
	    then ()
	    else if LS.isEmpty calls
	    then let
		(* If the calls are empty, then the lams should not be
		   We still need to insert this web into aform_tbl *)
		val some_lam_lab = LS.minItem lams
		val params = LT.lookup params_tbl some_lam_lab
		val aform_list = List.tabulate (List.length params, fn _ => AAtom)
	    in IntTbl.insert aform_tbl (index, aform_list) end
	    else let
		val aform_lists = LS.foldl (fn (call, acc) => List.map (fn arg : LVar.t => abstractForm form_tbl (LVT.lookup form_tbl arg)) (LT.lookup args_tbl call) :: acc) [] calls
		val aform_list = List.foldl unify_list (hd aform_lists) (tl aform_lists)
		val aform_list_old = IntTbl.lookup aform_tbl index
	    in
		if aform_list = aform_list_old
		then ()
		else let
		    fun handle_lam lam_lab = let
			val params = LT.lookup params_tbl lam_lab
		    in
			extendParam_list (env_tbl, form_tbl) (params, aform_list)
		    end
		in
		    changed := false;
		    IntTbl.insert aform_tbl (index, aform_list); (* update the table *)
		    LS.app handle_lam lams (* propagate the changes to the parameters of lambdas *)
		end
	    end
	val _ = List.appi (handle_web aform_tbl) call_webs
	val _ = List.appi (handle_web aform_tblK) call_websK
	fun handle_select (x, offset, arg) =
	    case LVT.lookup form_tbl arg
	     of Atom _ => true
	      | Tuple (_, xs) => let
		  val x' = List.nth (xs, offset-1)
	      in
		  LVT.insert form_tbl (x, LVT.lookup form_tbl x');
		  LVT.insert env_tbl (x, LVT.lookup env_tbl x');
		  LVT.insert killed_selects_tbl (x, true);
		  changed := true;
		  false
	      end
	val selects = List.filter handle_select selects
    in if ! changed
       then fixpoint (call_webs, call_websK, env_tbl, envK_tbl, form_tbl, params_tbl, args_tbl, aform_tbl, aform_tblK, selects, killed_selects_tbl)
       else selects
    end

    (* FIXME: could use an accumulator, though I'm not sure to what
       degree we want to care about the order of passed arguments. *)

    (* Flatten a form *)
    fun matchAndFlattenForm form_tbl (aform : abstract_form, form : form) =
	case (aform, form)
	 of (AAtom, Atom x) => [x]
	  | (AAtom, Tuple (x, _)) => [x]
	  | (ATuple aforms, Tuple (x, xs)) =>
	    ListPair.foldr (fn (aform, x, acc) => matchAndFlattenForm form_tbl (aform, LVT.lookup form_tbl x) @ acc)
			   [] (aforms, xs)
	  | _ => raise Fail "matchAndFlattenForm"

    (* Flatten a list of forms *)
    fun matchAndFlattenForm_list form_tbl (aform_list, form_list) =
	ListPair.foldr (fn (aform, form, acc) => matchAndFlattenForm form_tbl (aform, form) @ acc)
		       [] (aform_list, form_list)


    (* TODO *)
    fun new_needed_tuples (env, form_tbl, form, e) =
	case form
	 of Atom x => e
	  | Tuple (x, args) => let
	      fun handle_form (x, e) = new_needed_tuples (env, form_tbl, LVT.lookup form_tbl x, e)
	      val e = C.mkTUPLE (List.map env args, env x, e)
	  in List.foldl handle_form e args end

    val KEEP_UNUSED = true

    fun applyForms (C.CU lam0, call_webs, call_websK, (env_tbl, envK_tbl, form_tbl, aform_tbl, aform_tblK, killed_selects_tbl)) = let
	fun web_toString ({lams, calls, ...} : CallWebs.web) =
	    String.concat ["{",
			   "lams: ", String.concatWithMap " " Label.toString (LS.listItems lams), " ",
			   "calls: ", String.concatWithMap " " Label.toString (LS.listItems calls), "}"]
	(*
	val _ = Verbose.say ["user: ", String.concatWithMap " " web_toString call_webs, " ",
			     "cont: ", String.concatWithMap " " web_toString call_websK, "\n"]
	*)
	fun findIndex (msg, select, webs) lab  =
	    case List.foldli (fn (index, web : CallWebs.web, acc) =>
				  if acc <> ~1
				  then acc
				  else if LS.member (select web, lab)
				  then index
				  else acc)
			     ~1 webs
	     of ~1 => (Verbose.say [msg, " ", Label.toString lab, " ", String.concatWithMap " " web_toString webs, "\n"]; raise Fail "die")
	      | index => index
	fun web_lams ({lams, ...} : CallWebs.web) = lams
	fun web_calls ({calls, ...} : CallWebs.web) = calls
	val webIndex_lam = findIndex ("lam", web_lams, call_webs)
	val webIndex_call = findIndex ("call", web_calls, call_webs)
	val webIndex_lamK = findIndex ("lamK", web_lams, call_websK)
	val webIndex_callK = findIndex ("callK", web_calls, call_websK)
	fun env x = case LVT.find env_tbl x of SOME y => y
					     | NONE => (Verbose.say [LVar.toString x, "\n"]; raise Fail "")
	fun envK k = CVT.lookup envK_tbl k
	fun do_exp (exp as C.EXP (lab_e, e)) =
	    case e
	     of C.LETFUN (bindings, body) => let
		 val body = do_exp body
		 fun handle_lam lam = do_lam lam
		 val bindings = List.map handle_lam bindings
	     in C.mkLETFUN (bindings, body) end
	      | C.LETCONT (bindingKs, body) => let
		 val body = do_exp body
		 fun handle_lamK lamK = do_lamK lamK
		 val bindingKs = List.map handle_lamK bindingKs
	     in C.mkLETCONT (bindingKs, body) end
	      | C.IF(oper, args, thn, els) => let
		  val args = List.map env args
		  val thn = do_exp thn
		  val els = do_exp els
	      in C.mkIF (oper, args, thn, els) end
	      | C.ATOM (arg, x, e') => let
		  val e' = do_exp e'
		  val x = env x
	          val arg =
		      case arg
		       of C.LVAR (y, tys) => C.LVAR (env y, tys)
			| _ => arg
	      in C.mkATOM (arg, x, e') end

	      | C.PURE (oper, args, x, e') => let
		  val e' = do_exp e'
		  val x = env x
		  val args = List.map env args
	      in C.mkPURE (oper, args, x, e') end
	      | C.ARITH (oper, args, x, e', e_exn) => let
		  val e' = do_exp e'
		  val e_exn = do_exp e_exn
		  val x = env x
		  val args = List.map env args
	      in C.mkARITH (oper, args, x, e', e_exn) end
	      | C.GET (oper, args, x, e') => let
		  val e' = do_exp e'
		  val x = env x
		  val args = List.map env args
	      in C.mkGET (oper, args, x, e') end
	      | C.SET (oper, args, x, e') => let
		  val e' = do_exp e'
		  val x = env x
		  val args = List.map env args
	      in C.mkSET (oper, args, x, e') end

	      | C.TUPLE(args, x, e') => let
		  val e' = do_exp e'
		  val x = env x
		  val args = List.map env args
	      in C.mkTUPLE (args, x, e') end
	      (* FIXME: need to do stuff here? *)
	      | C.SELECT(offset, arg, x, e') => let
		  val e' = do_exp e'
	      in if LVT.lookup killed_selects_tbl x
		 then e'
		 else let
		     val x = env x
		     val arg = env arg
		 in C.mkSELECT (offset, arg, x, e') end
	      end
	      | C.DCAPPLY(dcon, tys, arg, x, e') => let
		  val e' = do_exp e'
		  val x = env x
		  val arg = env arg
		  val tys = tys (* FIXME *)
	      in C.mkDCAPPLY (dcon, tys, arg, x, e') end
	      | C.SWITCH(arg, pats) => let
		  fun handle_pat (pat, e') = let
		      val e' = do_exp e'
		  in
		      case pat
		       of C.VPAT x => (C.VPAT (env x), e')
			| C.LPAT lit => (C.LPAT lit, e')
			| C.DCPAT (dcon, tys, SOME x) => (C.DCPAT (dcon, tys, SOME (env x)), e')
			| C.DCPAT (dcon, tys, NONE) => (C.DCPAT (dcon, tys, NONE), e')
		  end
		  val pats = List.map handle_pat pats
		  val arg = env arg
	      in C.mkSWITCH (arg, List.rev pats) end

	      | C.APPLY(f, tys, args, argKs) => let
		  val f = env f
		  val tys = tys (* FIXME *)
		  val aform_list = IntTbl.lookup aform_tbl (webIndex_call lab_e)
		  fun handle_arg (arg, aform, acc) = let
		      val form = LVT.lookup form_tbl arg
		  in matchAndFlattenForm form_tbl (aform, form) @ acc end
		  val args = ListPair.foldl handle_arg [] (args, aform_list)
		  val args = List.map env args
		  val argKs = List.map envK argKs
	      in C.mkAPPLY (f, tys, args, argKs) end
	      | C.THROW(k, args) => let
		  val k = envK k
		  val aform_list = IntTbl.lookup aform_tblK (webIndex_callK lab_e)
		  fun handle_arg (arg, aform, acc) = let
		      val form = LVT.lookup form_tbl arg
		  in matchAndFlattenForm form_tbl (aform, form) @ acc end
		  val args = ListPair.foldl handle_arg [] (args, aform_list)
		  val args = List.map env args
	      in C.mkTHROW (k, args) end
	(* end case *)
	and do_lamK (lamK as (k, lamK_lab, xs, body)) = let
	    val body = do_exp body
	    val form_list = List.map (fn x => LVT.lookup form_tbl x) xs
	    fun handle_param (form, e) =
		new_needed_tuples (env, form_tbl, form, e)
	    val body = List.foldl handle_param body form_list
	    val aform_list = IntTbl.lookup aform_tblK (webIndex_lamK lamK_lab)
	    fun handle_x (x, aform, acc) = let
		val form = LVT.lookup form_tbl x
	    in matchAndFlattenForm form_tbl (aform, form) @ acc end
	    val xs' = ListPair.foldl handle_x [] (xs, aform_list)
	    (* assert: the form of each xs should exactly match that of the abstract forms *)
	    val xs = List.map env xs'
	    val k = envK k
	in C.mkCLambda (k, xs, body) end
	and do_lam (lam as (f, lam_lab, xs, ks, body)) = let
	    val body = do_exp body
	    val form_list = List.map (fn x => LVT.lookup form_tbl x) xs
	    fun handle_param (form, e) =
		new_needed_tuples (env, form_tbl, form, e)
	    val body = List.foldl handle_param body form_list
	    val aform_list = IntTbl.lookup aform_tbl (webIndex_lam lam_lab)
	    fun handle_x (x, aform, acc) = let
		val form = LVT.lookup form_tbl x
	    in matchAndFlattenForm form_tbl (aform, form) @ acc end
	    val xs' = ListPair.foldl handle_x [] (xs, aform_list)
	    (* assert: the form of each xs should exactly match that of the abstract forms *)
	    val f = env f
	    val xs = List.map env xs'
	    val ks = List.map envK ks
	in C.mkLambda (f, xs, ks, body) end
    in C.CU (do_lam lam0) end

    fun transform (cu, {user=call_webs, cont=call_websK}) = let
	val call_webs = CallWebs.all call_webs
	val call_websK = CallWebs.all call_websK
	val (env_tbl, envK_tbl, form_tbl, params_tbl, args_tbl, selects) = computeForms cu
	val aform_tbl = IntTbl.mkTable (100, Fail "aform_tbl")
	val aform_tblK = IntTbl.mkTable (100, Fail "aform_tblK")
	fun handle_web aform_tbl (index, web : CallWebs.web) = let
	    val lams = #lams web
	    val calls = #calls web
	in if LS.isEmpty lams
	   then let
	       val some_call_lab = LS.minItem calls
	       val args = LT.lookup args_tbl some_call_lab
	       val aform_list = List.tabulate (List.length args, fn _ => AAtom)
	   in IntTbl.insert aform_tbl (index, aform_list) end
	   else let
	       val some_lam_lab = LS.minItem lams
	       val params = LT.lookup params_tbl some_lam_lab
	       val aform_list = List.tabulate (List.length params, fn _ => AAtom)
	   in IntTbl.insert aform_tbl (index, aform_list) end
	end
	val () = List.appi (handle_web aform_tbl) call_webs
	val () = List.appi (handle_web aform_tblK) call_websK
	val killed_selects_tbl = LVT.mkTable (100, Fail "killed_selects_tbl")
	val _ = List.app (fn (x, _, _) => LVT.insert killed_selects_tbl (x, false)) selects
	val selects = fixpoint (call_webs, call_websK, env_tbl, envK_tbl, form_tbl, params_tbl, args_tbl, aform_tbl, aform_tblK, selects, killed_selects_tbl)
	fun IT_toString lt toString =
	    "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (Int.toString x) ^ " -> " ^ (toString y))
						    (IntTbl.foldi (fn (x, y, acc) => (x, y) :: acc) [] lt)))
	    ^ "]"
	fun LT_toString lt toString =
	    "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (Label.toString x) ^ " -> " ^ (toString y))
						    (LT.foldi (fn (x, y, acc) => (x, y) :: acc) [] lt)))
	    ^ "]"
	fun LVT_toString lt toString =
	    String.concatWith "\n" (List.map (fn (x, y) => (LVar.toString x) ^ " -> " ^ (toString y))
					     (LVT.foldi (fn (x, y, acc) => (x, y) :: acc) [] lt))
	fun aform_toString aform =
	    case aform
	     of AAtom => "Atom"
	      | ATuple aform_list => "(Tuple " ^ (aform_list_toString aform_list) ^ ")"
	and aform_list_toString aform_list =
	    String.concatWithMap " " aform_toString aform_list
	fun form_toString form =
	    case form
	     of Atom x => "Atom " ^ (LVar.toString x)
	      | Tuple (x, xs) => "(Tuple " ^ (LVar.toString x) ^ " " ^ (form_list_toString xs) ^ ")"
	and form_list_toString xs =
	    String.concatWithMap " " (fn x => form_toString (LVT.lookup form_tbl x)) xs
	fun web_toString ({lams, calls, ...} : CallWebs.web) =
	    String.concat ["{",
			   "lams: ", String.concatWithMap " " Label.toString (LS.listItems lams), " ",
			   "calls: ", String.concatWithMap " " Label.toString (LS.listItems calls), "}"]
	val () =
	    if true
	    then ()
	    else let
		fun pair_toString (i, web) = "[" ^ (Int.toString i) ^ " " ^ (web_toString web) ^ "]\n"
		fun make_pair call_webs i = (i, List.nth (call_webs, i))
		fun make_pair call_websK i = (i, List.nth (call_websK, i))
		val call_webs = List.tabulate (List.length call_webs, make_pair call_webs)
		val call_websK = List.tabulate (List.length call_websK, make_pair call_websK)
		(*
	    fun filter_pair (i, web : CallWebs.web) =
		not (#unknown_call web orelse
		     #unknown_lam web orelse
		     LS.isEmpty (#calls web) orelse
		     LS.isEmpty (#lams web))
	    val call_webs = List.filter filter_pair call_webs
	    val call_websK = List.filter filter_pair call_websK
		*)
		val () = Verbose.say [String.concatWithMap " " pair_toString call_webs, "\n"]
		val () = Verbose.say [String.concatWithMap " " pair_toString call_websK, "\n"]
		val () = Verbose.say ["call webs aform\n", IT_toString aform_tbl aform_list_toString, "\n"]
		val () = Verbose.say ["call websK aform\n", IT_toString aform_tblK aform_list_toString, "\n"]
		val () = Verbose.say [LVT_toString killed_selects_tbl (fn bool => if bool then "true" else "false"), "\n"]
		val () = Verbose.say ["forms\n", LVT_toString form_tbl form_toString]
	    in () end
	val cu = applyForms (cu, call_webs, call_websK, (env_tbl, envK_tbl, form_tbl, aform_tbl, aform_tblK, killed_selects_tbl))
    in cu end

  end
