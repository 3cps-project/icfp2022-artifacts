(* print-cps.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure PrintCPS : sig

    val output : TextIO.outstream * string * CPS.comp_unit -> unit

    val formatLabel : Label.t * ANSIText.t -> unit
    val unformatLabel : Label.t -> unit

  end = struct

    structure C = CPS
    structure P = PrimOp

  (* this is a specialization of the SML/NJ Library's TextIOPP, which allows
   * us to print fixed-width UTF8 character encodings w/o messing up the
   * indentation.
   *)
    structure Token =
      struct
        type style = unit
        datatype token = L | CL
        fun string L = "λ"
          | string CL = "cλ"
        fun style _ = ()
        fun size L = 1
          | size CL = 2
      end

    structure PP = struct
        structure PP = PPStreamFn (
          structure Token = Token
          structure Device = SimpleTextIODev)
        open PP
        fun openOut arg = openStream(SimpleTextIODev.openDev arg)
      end;

    fun includeLabels () = Controls.get Ctl.dumpCPSWithLabels

    (* it is very useful to be able to format labels during debugging *)
    val labelFormat : ANSIText.t Label.Tbl.hash_table = Label.Tbl.mkTable (100, Fail "PrintCPS label format")
    fun formatLabel (l, f : ANSIText.t) = Label.Tbl.insert labelFormat (l, f)
    fun unformatLabel l = (Label.Tbl.remove labelFormat l; ())

    fun lvarToString x = LVar.toString x ^ Extent.suffix(LVar.extentOf x)
    fun labelToString lab = Label.toString lab
    val dconToString = CPSDataCon.toString

    fun output (outS, msg, C.CU fb) = let
          val ppS = PP.openOut {dst = outS, wid = 90}
          val string = PP.string ppS
          fun sp () = PP.space ppS 1
          fun nl () = PP.newline ppS
        (* horizontal list w/o parens *)
          fun nakedHList ppItem items = (
                PP.openHBox ppS;
                  case items
                   of item::items => (
                        ppItem item;
                        List.app (fn item => (string ","; sp(); ppItem item)) items)
                    | [] => ()
                  (* end case *);
                PP.closeBox ppS)
        (* horizontal list in parens *)
          fun hlist ppItem items = (
                PP.openHBox ppS;
                  string "(";
                  nakedHList ppItem items;
                  string ")";
                PP.closeBox ppS)
        (* vertical list *)
          fun vlist ppItem items = (
                PP.openVBox ppS (PP.Abs 1);
                  string "(";
                  case items
                   of item::items => (
                        ppItem item;
                        List.app (fn item => (nl(); ppItem item)) items)
                    | [] => ()
                  (* end case *);
                  string ")";
                PP.closeBox ppS)
          fun ppLVar x = string(lvarToString x)

          fun ppLabel lab = if includeLabels()
                then string (case Label.Tbl.find labelFormat lab
                              of SOME format => ANSIText.fmt (format, labelToString lab)
                               | NONE => labelToString lab)
                else ()

          fun ppLVars [] = string "()"
            | ppLVars [x] = ppLVar x
            | ppLVars xs = (
                string "("; string(String.concatWithMap "," lvarToString xs); string ")")
          fun ppCVar k = string(CVar.toString k ^ Extent.suffix(CVar.extentOf k))
          fun ppBlk exp = let
                fun doLets (exp as C.EXP(exp_lab, term)) = (case term
                       of C.LETFUN(binds, e) => let
                            fun ppBind ((f, lab, xs, ks, e), prefix) = (
                                  nl();
                                  PP.openHVBox ppS (PP.Abs 4);
                                    PP.openHBox ppS;
                                      string prefix; sp();
                                      if includeLabels()
                                        then (
                                            string "["; ppLabel exp_lab;
                                            string "]"; sp())
                                        else ();
                                      ppLVar f; sp(); ppLabel lab; sp();
                                      string "("; nakedHList ppLVar xs;
                                      sp(); string "/"; sp();
                                      nakedHList ppCVar ks; string ")"; sp(); string "="; sp();
                                    PP.closeBox ppS;
                                    ppExp e;
                                  PP.closeBox ppS;
                                  "and")
                            in
                              ignore (List.foldl ppBind "fun" binds);
                              doLets e
                            end
                       | C.LETCONT(binds, e) => let
                            fun ppBind ((k, lab, xs, e), prefix) = (
                                  nl();
                                  PP.openHVBox ppS (PP.Abs 4);
                                    PP.openHBox ppS;
                                      string prefix; sp();
                                      if includeLabels()
                                        then (
                                          string "["; ppLabel exp_lab;
                                          string "]"; sp())
                                        else ();
                                      ppCVar k; sp(); ppLabel lab; sp();
                                      hlist ppLVar xs;
                                      sp(); string "=";
                                    PP.closeBox ppS;
                                    ppExp e;
                                  PP.closeBox ppS;
                                  "and")
                            in
                              ignore (List.foldl ppBind "cont" binds);
                              doLets e
                            end
                        | C.DCAPPLY(dc, tys, x, y, e) => ppBind (
                            exp_lab,
                            y,
                            fn () => (string (dconToString dc); sp(); ppLVar x),
                            e)
                        | C.PURE(f, xs, y, e) => ppPrim (exp_lab, P.Pure.toString f, xs, y, e)
                        | C.ARITH(f, xs, y, e, C.EXP(exn_lab, C.THROW(exh, []))) => ppBind (
                            exp_lab,
                            y,
                            fn () => (
                              string (P.Arith.toString f); sp();
                              string "("; nakedHList ppLVar xs;
                              sp(); string "/"; sp();
                              ppLabel exn_lab; sp ();
                              ppCVar exh; string ")"),
                            e)
                        | C.ARITH _ => raise Fail "bogus ARITH"
                        | C.GET(f, xs, y, e) =>
                            ppPrim (exp_lab, P.Getter.toString f, xs, y, e)
                        | C.SET(f, xs, y, e) =>
                            ppPrim (exp_lab, P.Setter.toString f, xs, y, e)
                        | C.TUPLE(xs, y, e) => ppBind (
                            exp_lab,
                            y,
                            fn () => (string "tuple"; sp(); hlist ppLVar xs),
                            e)
                        | C.SELECT(i, x, y, e) => ppBind (
                            exp_lab,
                            y,
                            fn () => (string ("#"^Int.toString i); sp(); ppLVar x),
                            e)
                        | C.ATOM(atm, y, e) =>
                            ppBind (exp_lab, y, fn () => string(CPSUtil.atomToString atm), e)
                        | _ => (
                            nl();
                            string "in";
                            PP.openVBox ppS (PP.Abs 2);
                              nl(); ppExp exp;
                            PP.closeBox ppS;
                            nl();
                            string "end")
                      (* end case *))
                and ppBind (exp_lab, x, ppRHS, e) = (
                      nl();
                      PP.openHBox ppS;
                        string "let"; sp(); ppLabel exp_lab; sp(); ppLVar x; sp(); string "="; sp();
                        ppRHS ();
                      PP.closeBox ppS;
                      doLets e)
                and ppPrim (exp_lab, rator, xs, y, e) = ppBind (
                      exp_lab,
                      y,
                      fn () => (string rator; sp(); hlist ppLVar xs),
                      e)
                in
                  PP.openVBox ppS (PP.Abs 0);
                    doLets exp;
                  PP.closeBox ppS
                end
          and ppExp (exp as C.EXP(exp_lab, term)) = (case term
                 of C.IF(tst, args, e1, e2) => (
                      PP.openHBox ppS;
                        string "if"; sp(); ppLabel exp_lab; sp(); string (P.Test.toString tst); sp(); ppLVars args;
                      PP.closeBox ppS;
                      sp();
                      PP.openHBox ppS;
                        string "then"; sp();
                        PP.openHOVBox ppS (PP.Abs 2); ppExp e1; PP.closeBox ppS;
                      PP.closeBox ppS;
                      sp();
                      PP.openHBox ppS;
                        string "else"; sp();
                        PP.openHOVBox ppS (PP.Abs 2); ppExp e2; PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.SWITCH(atm, cases) => let
                      fun ppCase (pat, exp) = (
                            nl();
                            PP.openHBox ppS;
                              string "|"; sp(); ppPat pat; sp(); string "=>";
                              PP.openHOVBox ppS (PP.Abs 4); ppExp exp; PP.closeBox ppS;
                            PP.closeBox ppS)
                      and ppPat pat = (case pat
                             of C.VPAT x => ppLVar x
                              | C.LPAT(lit, _) => string(Literal.toString lit)
                              | C.DCPAT(dc, _, NONE) => string (dconToString dc)
                              | C.DCPAT(dc, _, SOME x) => (
                                  PP.openHBox ppS;
                                    string (dconToString dc); sp(); ppLVar x;
                                  PP.closeBox ppS)
                            (* end case *))
                      in
                        PP.openVBox ppS (PP.Abs 0);
                          PP.openHBox ppS;
                            string "switch"; sp(); ppLabel exp_lab; sp(); ppLVar atm; sp(); string "of";
                          PP.closeBox ppS;
                          List.app ppCase cases;
                          nl();
                        PP.closeBox ppS;
                        string "end"
                      end
                  | C.APPLY(f, tys, args, ks) => (
                      PP.openHBox ppS;
                        ppLVar f; sp(); ppLabel exp_lab; sp(); string "(";
                        nakedHList ppLVar args;
                        sp(); string "/"; sp();
                        nakedHList ppCVar ks;
                        string ")";
                      PP.closeBox ppS)
                  | C.PURE _ => ppBlk exp
                  | C.ARITH _ => ppBlk exp
                  | C.GET _ => ppBlk exp
                  | C.SET _ => ppBlk exp
                  | C.THROW(k, xs) => (
                      PP.openHBox ppS;
                        string "throw"; sp(); ppLabel exp_lab; sp(); ppCVar k; sp(); ppLVars xs;
                      PP.closeBox ppS)
                  | _ => ppBlk exp
                (* end case *))
        (* print continuations as arguments to PRIM or APPLY *)
          and ppConts [] = raise Fail "unexpected empty continuation list"
            | ppConts [k] = (nl(); ppCVar k; string ")")
            | ppConts (k::kr) = (nl(); ppCVar k; string ","; ppConts kr)
          val (f, lab, xs, ks, body) = fb
          in
            PP.openVBox ppS (PP.Abs 0);
              string (concat ["===== CPS: ", msg, " ====="]); nl();
              PP.openVBox ppS (PP.Abs 4);
                PP.openHBox ppS;
                  string "fun"; sp(); ppLVar f; sp(); ppLabel lab; sp();
                  string "("; nakedHList ppLVar xs;
                  sp(); string "/"; sp();
                  nakedHList ppCVar ks; string ")"; sp(); string "=";
                PP.closeBox ppS;
                ppExp body;
              PP.closeBox ppS;
              nl();
              string "====="; nl();
            PP.closeBox ppS;
            PP.closeStream ppS
          end

  end
