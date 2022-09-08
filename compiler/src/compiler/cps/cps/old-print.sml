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

    fun output (outS, msg, C.CU fb) = let
          val ppS = PP.openOut {dst = outS, wid = 90}
          val string = PP.string ppS
          fun sp () = PP.space ppS 1
          fun nl () = PP.newline ppS
          fun sexp (prefix, args) = (
                PP.openHBox ppS;
                  string "(";
                  PP.openHOVBox ppS (PP.Rel 1);
                    string prefix; sp();
                    args(); string ")";
                  PP.closeBox ppS;
                PP.closeBox ppS)
          fun sexp' (tok, args) = (
                PP.openHBox ppS;
                  string "(";
                  PP.openHOVBox ppS (PP.Rel 1);
                    PP.token ppS tok; sp();
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
          fun ppLabel lab = string(Label.toString lab)
          fun ppCVar k = string(CVar.toString k ^ Extent.suffix(CVar.extentOf k))
          fun ppAtom atm = string(CPSUtil.atomToString atm)
          fun ppExp (C.EXP(_, term)) = (case term
                 of C.LETREC(binds, e) => (
                      PP.openHBox ppS;
                        string "(";
                        PP.openHOVBox ppS (PP.Rel 1);
                          string "letrec"; sp();
                          vlist ppBind binds;
                          nl();
                          ppExp e; string ")";
                        PP.closeBox ppS;
                      PP.closeBox ppS)
                  | C.IF(tst, args, e1, e2) =>
                      sexp ("if", fn () => (
                        sexp (P.Test.toString tst, fn () => (sp(); nakedHList ppAtom args));
                        sp(); ppExp e1;
                        sp(); ppExp e2))
                  | C.SWITCH(atm, cases) =>
                      sexp ("switch", fn () => (
                        ppAtom atm; sp();
                        vlist ppCase cases))
                  | C.APPLY(f, tys, xs, ks) =>
                      sexp (LVar.toString f, fn () => (
                        nakedHList ppAtom xs; sp(); string "/"; sp(); nakedHList ppCont ks))
                  | C.DCAPPLY(dc, tys, x, k) =>
                      sexp (dconToString dc, fn () => (
                        ppLVar x; sp(); string "=>"; sp(); ppCont k))
                  | C.PURE(f, xs, k) =>
                      sexp (P.Pure.toString f, fn () => (
                        nakedHList ppAtom xs; sp(); string "=>"; sp(); ppCont k))
                  | C.ARITH(f, xs, k1, k2) =>
                      sexp (P.Arith.toString f, fn () => (
                        nakedHList ppAtom xs; sp(); string "=>"; sp();
                        ppCont k1; sp(); ppCont k2))
                  | C.GET(f, xs, k) =>
                      sexp (P.Getter.toString f, fn () => (
                        nakedHList ppAtom xs; sp(); string "=>"; sp(); ppCont k))
                  | C.SET(f, xs, k) =>
                      sexp (P.Setter.toString f, fn () => (
                        nakedHList ppAtom xs; sp(); string "=>"; sp(); ppCont k))
                  | C.THROW(k, xs) =>
                      sexp ("throw", fn () => (ppCont k; sp(); nakedHList ppAtom xs))
                  | C.TUPLE(xs, k) =>
                      sexp ("tuple", fn () => (
                        nakedHList ppLVar xs; sp(); string "=>"; sp(); ppCont k))
                  | C.SELECT(i, x, k) =>
                      sexp ("#"^Int.toString i, fn () => (
                        ppLVar x; sp(); string "=>"; sp(); ppCont k))
                (* end case *))
          and ppBind (C.FUN lambda) = ppLambda lambda
            | ppBind (C.CONT(k, cont)) = (
                PP.openHBox ppS;
                  string "["; ppCVar k; sp(); ppCont cont; string "]";
                PP.closeBox ppS)
          and ppLambda (f, lab, xs, ks, e) = (
                PP.openHBox ppS;
                  string "["; ppLVar f; sp(); ppLabel lab; sp();
                  sexp' (Token.L, fn () => (
                    PP.openHBox ppS;
                      hlist ppLVar xs; sp(); hlist ppCVar ks;
                    PP.closeBox ppS;
                    sp(); ppExp e));
                  string "]";
                PP.closeBox ppS)
          and ppCont (C.CLAMBDA cl) = ppCLambda cl
            | ppCont (C.CVAR k) = ppCVar k
            | ppCont C.HALT = string "(halt)"
          and ppCLambda (lab, xs, e) =
                sexp' (Token.CL, fn () => (hlist ppLVar xs; sp(); ppExp e))
          and ppCase (pat, exp) = (
                PP.openHBox ppS;
                  string "[";
                  case pat
                   of C.VPAT x => ppLVar x
                    | C.LPAT(lit, ty) => string(Literal.toString lit)
                    | C.DCPAT(dc, tys, NONE) => string (dconToString dc)
                    | C.DCPAT(dc, tys, SOME x) => sexp (dconToString dc, fn () => ppLVar x)
                  (* end case *);
                  sp(); ppExp exp;
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
