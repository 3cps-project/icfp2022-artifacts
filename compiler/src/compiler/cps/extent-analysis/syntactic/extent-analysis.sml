
structure SyntacticExtentAnalysis : sig

   val analyze : CPS.comp_unit -> unit

end = struct

   structure LVT = LVar.Tbl
   structure C = CPS

   fun analyze (C.CU lam0) = let
       val notInNestedLam = LVT.mkTable (100, Fail "SyntacticExtentAnalysis.notInNestedLam")
       val notInNestedAny = LVT.mkTable (100, Fail "SyntacticExtentAnalysis.notInNestedAny")
       val lvarInnermostLam = LVT.mkTable (100, Fail "SyntacticExtentAnalysis.lvarInnermostLam")
       val lvarInnermost = LVT.mkTable (100, Fail "SyntacticExtentAnalysis.lvarInnermost")
       fun init (innermost_lam, innermost) x =
           (LVT.insert lvarInnermostLam (x, innermost_lam);
            LVT.insert lvarInnermost (x, innermost);
            LVT.insert notInNestedLam (x, ());
            LVT.insert notInNestedAny (x, ());
            ())

       fun remove (lvt, x) =
           case LVT.find lvt x
            of SOME _ => LVT.remove lvt x
             | NONE => ()

       fun destroy x =
           (LVT.remove lvarInnermostLam x;
            LVT.remove lvarInnermost x;
            remove (notInNestedLam, x);
            remove (notInNestedAny, x))

       fun annotate x = let
           val stack = LVT.inDomain notInNestedLam x
           val reg = LVT.inDomain notInNestedAny x
           val extent = if stack andalso reg
                        then Extent.REG
                        else if stack 
                        then Extent.STK
                        else Extent.HEAP
       in LVar.setExtent (x, extent) end

       fun check_stack (x, innermost_lam) =
           case LVT.find lvarInnermostLam x
            of SOME lab => if Label.same (lab, innermost_lam)
                           then ()
                           else (remove (notInNestedLam, x); ())
             | NONE => ()
       fun check_reg (x, innermost) =
           case LVT.find lvarInnermost x
            of SOME lab => if Label.same (lab, innermost)
                           then ()
                           else (remove (notInNestedAny, x); ())
             | NONE => ()
       fun check (innermost_lam, innermost) x =
           (check_stack (x, innermost_lam); 
            check_reg (x, innermost); ())

       fun analyze_exp (C.EXP (_, e), innermost_lam, innermost) =
           case e
	    of C.LETFUN(bindings, body) => 
               ((*List.app (fn (f, _, _, _, _) => init (innermost_lam, innermost) f) bindings;
                List.app (fn lam as (f, lab_lam, _, _, _) =>
                             (LVT.insert lvarInnermostLam (f, lab_lam);
                              LVT.insert lvarInnermost (f, lab_lam);
                              analyze_lam lam))
                         bindings;
                List.app (fn lam as (f, _, _, _, _) =>
                             (LVT.insert lvarInnermostLam (f, innermost_lam);
                              LVT.insert lvarInnermost (f, innermost)))
                         bindings;
                analyze_exp (body, innermost_lam, innermost);
                List.app (fn (f, _, _, _, _) => annotate f) bindings;
                List.app (fn (f, _, _, _, _) => destroy f) bindings; *)
                 (* this should be able to check for recursive functions, 
                    marking them all as heap *)
                 List.app (fn (f, _, _, _, _) => init (innermost_lam, innermost) f) bindings;
                 List.app (fn bind => analyze_lam bind) bindings;
                 analyze_exp (body, innermost_lam, innermost);
                 List.app (fn (f, _, _, _, _) => annotate f) bindings;
                 List.app (fn (f, _, _, _, _) => destroy f) bindings;
                 List.app (fn (f, _, _, _, _) => LVar.setExtent (f, Extent.HEAP)) bindings)
                
	     | C.LETCONT(bindingKs, body) =>
               (List.app (analyze_lamK innermost_lam) bindingKs;
                analyze_exp (body, innermost_lam, innermost))
	    | C.IF(oper, args, thn, els) => 
              (List.app (check (innermost_lam, innermost)) args;
	       analyze_exp (thn, innermost_lam, innermost);
	       analyze_exp (els, innermost_lam, innermost))
	    | C.ATOM (arg, x, e') => let
                val _ = case arg 
                         of C.LVAR (y, ty) => check (innermost_lam, innermost) y
                          | _ => ()
	    in
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x
            end
	    | C.PURE (oper, args, x, e') =>
              (List.app (check (innermost_lam, innermost)) args;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.ARITH (oper, args, x, e', e_exn) => 
              (List.app (check (innermost_lam, innermost)) args;
               analyze_exp (e_exn, innermost_lam, innermost);
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.GET (oper, args, x, e') =>
              (List.app (check (innermost_lam, innermost)) args;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.SET (oper, args, x, e') => 
              (List.app (check (innermost_lam, innermost)) args;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.TUPLE(args, x, e') => 
              (List.app (check (innermost_lam, innermost)) args;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.SELECT(offset, arg, x, e') => 
              (check (innermost_lam, innermost) arg;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.DCAPPLY(dcon, tys, arg, x, e') => 
              (check (innermost_lam, innermost) arg;
               init (innermost_lam, innermost) x;
               analyze_exp (e', innermost_lam, innermost);
               annotate x;
               destroy x)
	    | C.SWITCH(arg, pats) => let
                fun handle_pat (pat, e') =
                    case pat
                     of C.VPAT x => 
                        (init (innermost_lam, innermost) x;
                         analyze_exp (e', innermost_lam, innermost);
                         annotate x;
                         destroy x)
                      | C.DCPAT (dcon', _, SOME x) =>
                        (init (innermost_lam, innermost) x;
                         analyze_exp (e', innermost_lam, innermost);
                         annotate x;
                         destroy x)
                      | C.DCPAT (dcon', _, NONE) => analyze_exp (e', innermost_lam, innermost)
                      | C.LPAT (lit, _) => analyze_exp (e', innermost_lam, innermost)
            in check (innermost_lam, innermost) arg; 
               List.app handle_pat pats 
            end
	    | C.APPLY(f, tys, args, argKs) => 
              List.app (check (innermost_lam, innermost)) (f::args)
	    | C.THROW(k, args) => 
              List.app (check (innermost_lam, innermost)) args
	  (* end case *)
       and analyze_lam (_, lab_lam, xs, _, body) =
           (List.app (init (lab_lam, lab_lam)) xs;
            analyze_exp (body, lab_lam, lab_lam);
            List.app annotate xs;
            List.app destroy xs)
       and analyze_lamK lab_lam (_, lab_lamK, xs, body) = 
           (List.app (init (lab_lam, lab_lamK)) xs;
            analyze_exp (body, lab_lam, lab_lamK);
            List.app annotate xs;
            List.app destroy xs)
   in analyze_lam lam0 end

end
