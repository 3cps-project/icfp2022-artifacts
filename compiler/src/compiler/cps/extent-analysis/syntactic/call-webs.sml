(* syntactic-call-webs.sml
 *
 * Computes call webs based on a simple syntactic criteria.
 * Any function var that is passed as an argument to a function, tuple, etc.
 * is treated as if it could be called anywhere; that is, it has unknown_call=true.
 *)

structure DetermineSyntacticCallWebs : sig

  val callWebs : CPS.comp_unit * {add_unknown : bool} -> {user : CallWebs.t, cont : CallWebs.t}

end = struct

  structure C = CPS
  structure LVM = LVar.Map
  structure CVM = CVar.Map

  fun callWebs (cu as C.CU lam0, {add_unknown}) = let
      fun find_fun_lv (fun_lv, x) =
          LVM.find (fun_lv, x)
      fun find_fun_cv (fun_lv, x) =
          CVM.find (fun_lv, x)
      fun add (fun_lv, x, lam_lab) =
          LVM.insert (fun_lv, x, lam_lab)
      fun addK (fun_cv, k, lamK_lab) =
          CVM.insert (fun_cv, k, lamK_lab)
      fun do_exp (exp as C.EXP (lab_e, e), webs as (callWebs, callWebsK), fun_lv, fun_cv) =
          case e
           of C.LETFUN (bindings, body) => let
               fun collect_fun_lv ((f, lam_lab, _, _, _), fun_lv) = add (fun_lv, f, lam_lab)
               val fun_lv = List.foldl collect_fun_lv fun_lv bindings
               fun handle_bind (lam, webs) =
                   do_lam (lam, webs, fun_lv, fun_cv)
               val webs = List.foldl handle_bind webs bindings
               val webs = do_exp (body, webs, fun_lv, fun_cv) 
           in webs end
            | C.LETCONT (bindingKs, body) => let
               fun collect_fun_cv ((k, lamK_lab, _, _), fun_cv) = addK (fun_cv, k, lamK_lab)
               val fun_cv = List.foldl collect_fun_cv fun_cv bindingKs
               fun handle_bindK (lamK, webs) =
                   do_lamK (lamK, webs, fun_lv, fun_cv)
               val webs = List.foldl handle_bindK webs bindingKs
               val webs = do_exp (body, webs, fun_lv, fun_cv) 
           in webs end
            | C.IF (oper, args, thn, els) => let
                val webs = do_exp (thn, webs, fun_lv, fun_cv)
                val webs = do_exp (els, webs, fun_lv, fun_cv)
            in webs end
            | C.ATOM (arg, x, e') => let
                val fun_lv =
                    case arg
                     of C.LVAR (y, _) =>
                        (case find_fun_lv (fun_lv, y)
                          of SOME lam_lab => add (fun_lv, x, lam_lab)
                           | NONE => fun_lv)
                      | _ => fun_lv
            in do_exp (e', webs, fun_lv, fun_cv) end

            | C.PURE (oper, args, x, e') => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end
            | C.ARITH (oper, args, x, e', e_exn) => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end
            | C.GET (oper, args, x, e') => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end
            | C.SET (oper, args, x, e') => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end

            | C.TUPLE(args, x, e') => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end
            | C.SELECT(offset, arg, x, e') =>
              do_exp (e', webs, fun_lv, fun_cv) 

            | C.DCAPPLY(dcon, tys, arg, x, e') => let
                val callWebs =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val webs = (callWebs, callWebsK)
            in do_exp (e', webs, fun_lv, fun_cv) end
            | C.SWITCH(arg, pats) => let
                fun handle_pat ((pat, e'), webs) =
                    do_exp (e', webs, fun_lv, fun_cv)
            in List.foldl handle_pat webs pats end

            | C.APPLY(f, tys, args, argKs) => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                fun handle_argK (argK, callWebsK) =
                    case find_fun_cv (fun_cv, argK)
                     of SOME lamK_lab => if add_unknown then CallWebs.add_unknown_call (callWebsK, {lam=lamK_lab}) else callWebs
                      | NONE => callWebsK
                val callWebsK = List.foldl handle_argK callWebsK argKs
                val callWebs =
                    case find_fun_lv (fun_lv, f)
                     of SOME lam_lab => CallWebs.add (callWebs, {lambda=lam_lab, call=lab_e})
                      | NONE => if add_unknown then CallWebs.add_unknown_lam (callWebs, {call=lab_e}) else callWebs
                val webs = (callWebs, callWebsK)
            in webs end
            | C.THROW (k, args) => let
                fun handle_arg (arg, callWebs) =
                    case find_fun_lv (fun_lv, arg)
                     of SOME lam_lab => if add_unknown then CallWebs.add_unknown_call (callWebs, {lam=lam_lab}) else callWebs
                      | NONE => callWebs
                val callWebs = List.foldl handle_arg callWebs args
                val callWebsK =
                    case find_fun_cv (fun_cv, k)
                     of SOME lamK_lab => CallWebs.add (callWebsK, {lambda=lamK_lab, call=lab_e})
                      | NONE => if add_unknown then CallWebs.add_unknown_lam (callWebsK, {call=lab_e}) else callWebs
                val webs = (callWebs, callWebsK)
            in webs end

      (* end case *)
      and do_lamK (lamK as (k, lamK_lab, xs, body), webs, fun_lv, fun_cv) =
          do_exp (body, webs, fun_lv, fun_cv)
      and do_lam (lam as (f, lam_lab, xs, ks, body), webs, fun_lv, fun_cv) =
          do_exp (body, webs, fun_lv, fun_cv)
      val {lams, call_sites, lamKs, callK_sites, ...} = InfoUtil.info cu
      val callWebs = CallWebs.initial {lams=lams, calls=call_sites}
      val callWebsK = CallWebs.initial {lams=lamKs, calls=callK_sites}
      val (callWebs, callWebsK) = do_lam (lam0, (callWebs, callWebsK), LVM.empty, CVM.empty)
  in {user=callWebs, cont=callWebsK} end

end
