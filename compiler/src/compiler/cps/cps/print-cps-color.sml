(* print-cps.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure PrintCPS : sig

    val output : TextIO.outstream * string * CPS.comp_unit -> unit

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

    val dconToString = CPSDataCon.toString

  (* Returns a string that gives a random foreground/background pair, deterministic on i *)
    fun color i = let
          val it = i mod 56
          val color = it mod 7
          val bg = it mod 8
          val underline = (i mod 128) > 64
          val bold = (i mod 256) > 128
          val bg = 0
          in {
            fg = SOME(if color >= bg then color+1 else 0),
            bg = SOME bg,
            bf = bold,
            ul = underline
          } end

    fun expToString (C.EXP(l, e)) : string = let
          val e = (case e
                 of C.LETREC _ => "letrec"
                  | C.IF _ => "if"
                  | C.SWITCH _ => "switch"
                  | C.APPLY _ => "apply"
                  | C.DCAPPLY _ => "dcapply"
                  | C.PRIM _ => "prim"
                  | C.THROW _ => "throw"
                  | C.TUPLE _ => "tuple"
                  | C.SELECT _ => "select"
                (* end case *))
          val i = Word.toIntX (Label.hash l)
          in
            concat [
                ANSIText.fmt ({fg=SOME 7, bg=NONE, bf=true, ul=true}, e),
                ANSIText.fmt (color i, concat["<", Label.toString l, ">"])
              ]
          end

    fun output (outS, msg, C.CU fb) = let
          val ppS = PP.openOut {dst = outS, wid = 90}
          val string = PP.string ppS
          fun sp () = PP.space ppS 1
          fun nl () = PP.newline ppS
          fun sexp (prefix, args) = (
                PP.openHBox ppS;
                  string "("; string prefix; sp();
                  PP.openHOVBox ppS (PP.Rel 0);
                    args(); string ")";
                  PP.closeBox ppS;
                PP.closeBox ppS)
          fun sexp' (tok, args) = (
                PP.openHBox ppS;
                  string "("; PP.token ppS tok; sp();
                  PP.openHOVBox ppS (PP.Rel 0);
                    args(); string ")";
                  PP.closeBox ppS;
                PP.closeBox ppS)
        (* horizontal list w/o parens *)
          fun nakedHList ppItem items = (
                PP.openHBox ppS;
                  case items
                   of item::items => (
                        ppItem item;
                        List.app (fn item => (sp(); ppItem item)) items)
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
                PP.openVBox ppS (PP.Rel 1);
                  string "(";
                  case items
                   of item::items => (
                        ppItem item;
                        List.app (fn item => (nl(); ppItem item)) items)
                    | [] => ()
                  (* end case *);
                  string ")";
                PP.closeBox ppS)
          fun ppLVar x = string(LVar.toString x ^ Extent.suffix(LVar.extentOf x))
          fun ppCVar k = string(CVar.toString k ^ Extent.suffix(CVar.extentOf k))
          fun ppAtom atm = string(CPSUtil.atomToString atm)
          fun ppExp (exp as C.EXP(_, term)) = (case term
                 of C.LETREC(binds, e) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "letrec" *); sp();
                          vlist ppBind binds;
                          nl();
                          ppExp e; string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.IF(tst, args, e1, e2) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (*string "if"*); sp(); P.testToString tst; sp(); nakedHList ppAtom args; nl();
                          sp(); ppExp e1;
                          sp(); ppExp e2;
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.SWITCH(atm, cases) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (*string "switch"*); sp(); ppAtom atm; nl();
                          vlist ppCase cases;
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.APPLY(f, tys, xs, ks) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "apply" *);
                          sp(); string (LVar.toString f); sp(); nakedHList ppAtom xs; sp();
                          nakedHList ppCont ks;
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.DCAPPLY(dc, tys, x, k) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "dcapply" *); dconToString dc; sp(); ppLVar x; sp();
                          ppCont k; 
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.PRIM(f, xs, ks) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "prim" *); P.arithToString f; nakedHList ppAtom xs; sp(); nl();
                          nakedHList ppCont ks;
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.THROW(k, xs) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "throw"*); sp(); nakedHList ppAtom xs; sp();
                          ppCont k; 
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.TUPLE(xs, k) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string "tuple" *); sp(); nakedHList ppLVar xs; sp();
                          ppCont k; 
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.SELECT(i, x, k) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string (expToString exp) (* string ("select "^ (Int.toString i)) *); sp(); string (Int.toString i); sp(); ppLVar x; sp();
                          ppCont k; 
                          string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                (* end case *))
          and ppBind (C.FUN lambda) = ppLambda lambda
            | ppBind (C.CONT(k, cont)) = (
                PP.openHBox ppS;
                  string "["; ppCVar k; sp();
                  PP.openHOVBox ppS (PP.Rel 2);
                    ppCont cont; string "]";
                  PP.closeBox ppS;
                PP.closeBox ppS)
          and ppLambda (f, lab, xs, ks, e) = (
                PP.openHBox ppS;
                  string "["; ppLVar f; sp(); nl();
                  sexp' (Token.L, fn () => (
                    PP.openHBox ppS;
                      string (Label.toString lab); sp(); 
                      hlist ppLVar xs; sp(); 
                      hlist ppCVar ks; sp(); 
                    PP.closeBox ppS;
                    sp(); ppExp e));
                  string "]";
                PP.closeBox ppS)
          and ppCont (C.CLAMBDA cl) = ppCLambda cl
            | ppCont (C.CVAR k) = ppCVar k
            | ppCont C.HALT = string "(halt)"
          and ppCLambda (lab, xs, e) =
              sexp' (Token.CL, fn () => (string (Label.toString lab); sp(); hlist ppLVar xs; sp(); ppExp e))
          and ppCase (pat, exp) = (
                PP.openHBox ppS;
                  string "[";
                  case pat
                   of C.VPAT x => ppLVar x
                    | C.LPAT(lit, ty) => string(Literal.toString lit)
                    | C.DCPAT(dc, tys, NONE) => string (dconToString dc)
                    | C.DCPAT(dc, tys, SOME x) => sexp (dconToString dc, fn () => ppLVar x)
                  (* end case *);
                  sp(); nl(); ppExp exp;
                  string "]";
                PP.closeBox ppS)
          in
            PP.openVBox ppS (PP.Abs 0);
              string (concat ["===== CPS: ", msg, " ====="]); nl();
              ppLambda fb;
              nl();
              string "====="; nl();
            PP.closeBox ppS;
            PP.closeStream ppS
          end

  end
