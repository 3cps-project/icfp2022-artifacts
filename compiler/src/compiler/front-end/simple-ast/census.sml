(* census.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Census : sig

  (* abstraction of census information *)
    type t

  (* operations on variable use counts *)
    val useCntOf : t -> SimpleVar.t -> int
    val setUse : t -> SimpleVar.t * int -> unit
    val incUse : t -> SimpleVar.t -> unit
    val decUse : t -> SimpleVar.t -> unit
    val isUsed : t -> SimpleVar.t -> bool

  (* operations on variable application counts *)
    val appCntOf : t -> SimpleVar.t -> int
    val setApp : t -> SimpleVar.t * int -> unit
    val incApp : t -> SimpleVar.t -> unit
    val decApp : t -> SimpleVar.t -> unit

  (* helpers for constructing new terms.  These return the variable that they
   * are called with, while also incrementing the counts for the variable.
   *)
    val use : t -> SimpleVar.t -> SimpleVar.t     (* bumps use count *)
    val apply : t -> SimpleVar.t -> SimpleVar.t   (* bumps both use and app counts *)

  (* `replaceWith info (x, y)` adjusts the counts of `y` to reflect that uses
   * of `x` are going to be replaced by `y`.
   *)
    val replaceWith : t -> SimpleVar.t * SimpleVar.t -> unit

  (* associate the counts of the first variable with the second variable (which is
   * assumed to be fresh).
   *)
    val share : t -> SimpleVar.t * SimpleVar.t -> unit

  (* set the counts of the second variable to the first *)
    val copy : t -> SimpleVar.t * SimpleVar.t -> unit

  (* compute census counts for a compilation unit *)
    val analyze : SimpleAST.comp_unit -> t

  (* check a census for correctness; return true if there are any errors *)
    val check : (string list -> unit) -> SimpleAST.comp_unit * t -> bool

  (* debug support *)
    val varToString : t -> SimpleVar.t -> string

    val dump : (string list -> unit) -> t -> unit

  end = struct

    structure S = SimpleAST
    structure SVar = SimpleVar
    structure VTbl = SVar.Tbl

    datatype cnt = CNT of int ref

    datatype t = Info of {
        useTbl : cnt VTbl.hash_table,
        appTbl : cnt VTbl.hash_table
      }

    local
      fun value NONE = 0
        | value (SOME(CNT r)) = !r
      fun countOf tbl = let
            val find = VTbl.find tbl
            in
              fn x => value (find x)
            end
      fun add tbl n = let
            val find = VTbl.find tbl
            val insert = VTbl.insert tbl
            in
              fn x => (case find x
                   of SOME(CNT r) => r := !r + n
                    | NONE => insert (x, CNT(ref n))
                  (* end case *))
            end
      fun set tbl = let
            val insert = VTbl.insert tbl
            in
              fn (x, n) => insert (x, CNT(ref n))
            end
    in

    fun useCntOf (Info{useTbl, ...}) = countOf useTbl
    fun setUse (Info{useTbl, ...}) = set useTbl
    fun incUse (Info{useTbl, ...}) = add useTbl 1
    fun decUse (Info{useTbl, ...}) = add useTbl ~1
    fun isUsed (Info{useTbl, ...}) = let
          val find = VTbl.find useTbl
          in
            fn x => value(find x) > 0
          end

    fun appCntOf (Info{appTbl, ...}) = countOf appTbl
    fun setApp (Info{appTbl, ...}) = set appTbl
    fun incApp (Info{appTbl, ...}) = add appTbl 1
    fun decApp (Info{appTbl, ...}) = add appTbl ~1

    fun use (Info{useTbl, ...}) = let
          val inc = add useTbl 1
          in
            fn x => (inc x; x)
          end
    fun apply (Info{useTbl, appTbl}) = let
          val incU = add useTbl 1
          val incA = add appTbl 1
          in
            fn x => (incU x; incA x; x)
          end

    fun replaceWith (Info{useTbl, appTbl}) = let
          val findUse = VTbl.find useTbl
          val findApp = VTbl.find appTbl
          val insertApp = VTbl.insert appTbl
          in
            fn (x, y) => (
                case (value(findUse x), findUse y)
                 of (n, SOME(CNT r)) => r := !r + n - 1
                  | (n, NONE) => (* there should be at least one use of `y` *)
                      raise Fail "impossible"
                (* end case *);
                case (findApp x, findApp y)
                 of (NONE, _) => ()
                  | (SOME(CNT rx), SOME(CNT ry)) => ry := !ry + !rx
                  | (SOME(CNT rx), NONE) => insertApp (y, CNT(ref(!rx)))
                (* end case *))
          end

    fun share (Info{useTbl, appTbl}) = let
          fun copyCnt tbl = let
                val find = VTbl.find tbl
                val insert = VTbl.insert tbl
                in
                  fn (x, y) => (case find x of SOME cnt => insert (y, cnt) | _ => ())
                end
          val copyUse = copyCnt useTbl
          val copyApp = copyCnt appTbl
          in
            fn (x, y) => (copyUse(x, y); copyApp(x, y))
          end

    fun copy (Info{useTbl, appTbl}) = let
          fun copyCnt tbl = let
                val find = VTbl.find tbl
                val insert = VTbl.insert tbl
                in
                  fn (x, y) => (case find x
                     of SOME(CNT r) => insert (y, CNT(ref(!r)))
                      | _ => ())
                end
          val copyUse = copyCnt useTbl
          val copyApp = copyCnt appTbl
          in
            fn (x, y) => (copyUse(x, y); copyApp(x, y))
          end

    end (* local *)

    fun analyze (S.CU(lambda as S.FB(cu, _, _, _))) = let
        (* table to track use counts of variables *)
          val useTbl = VTbl.mkTable (128, Fail "useTbl")
        (* table to track application counts of functions *)
          val appTbl = VTbl.mkTable (128, Fail "appTbl")
        (* functions to get counts *)
          fun getCnt tbl = let
                val find = VTbl.find tbl
                val insert = VTbl.insert tbl
                in
                  fn x => (case find x
                         of SOME cnt => cnt
                          | NONE => let val cnt = CNT(ref 0)
                              in
                                insert (x, cnt); cnt
                              end)
                end
          val getUseCnt = getCnt useTbl
          val getAppCnt = getCnt appTbl
        (* increment a counter *)
          fun inc (CNT r) = r := !r + 1
        (* count a non-application use *)
          fun cntUse x = inc(getUseCnt x)
        (* count an application use *)
          fun cntApp f = (cntUse f; inc(getAppCnt f))
        (* analyse a lambda *)
          fun analFB (S.FB(_, _, _, e)) = analExp e
        (* analyse an expression *)
          and analExp (S.E(_, exp)) = (case exp
                 of S.E_Let(x, e1, e2) => (
                      analExp e1; analExp e2)
                  | S.E_LetPoly(x, _, e1, e2) => (
                      analExp e1; analExp e2)
                  | S.E_Fun(fbs, e) => (
                      List.app analFB fbs; analExp e)
                  | S.E_Apply(f, _, arg) => (
                      cntApp f; useAtom arg)
                  | S.E_DConApp(_, _, atm) => useAtom atm
                  | S.E_Prim(_, _, args) => List.app useAtom args
                  | S.E_Tuple args => List.app useAtom args
                  | S.E_Select(_, x, _) => cntUse x
                  | S.E_If(_, args, e1, e2, _) => (
                      List.app useAtom args; analExp e1; analExp e2)
                  | S.E_Case(arg, cases, _) => (
                      useAtom arg;
                      List.app (fn (S.RULE(_, _, e)) => analExp e) cases)
                  | S.E_Handle(e1, _, e2, _) => (
                      analExp e1; analExp e2)
                  | S.E_Raise(_, atm, _) => useAtom atm
                  | S.E_Atom atm => useAtom atm
                (* end case *))
          and useAtom (S.A_Var(x, _)) = cntUse x
            | useAtom _ = ()
          in
            analFB lambda;
          (* we bump the use count of the compilation unit by one,
           * since it is used by the linker
           *)
            cntUse cu;
            Info{useTbl = useTbl, appTbl = appTbl}
          end

    fun check say (compUnit, info) = let
          val anyErrors = ref false
          val Info{useTbl, appTbl} = analyze compUnit
          fun chk msg get (x, CNT(ref n)) = if (get x <> n)
                then (
                  anyErrors := true;
                  say [
                      "** ERROR: ", msg, "(", SVar.toString x, ") = ",
                      Int.toString(get x), "; should be ",
                      Int.toString n, "\n"
                    ])
                else ()
          in
            VTbl.appi (chk "useCnt" (useCntOf info)) useTbl;
            VTbl.appi (chk "appCnt" (appCntOf info)) appTbl;
            !anyErrors
          end

    fun varToString info = let
          val useCnt = useCntOf info
          val appCnt = appCntOf info
          in
            fn x => (case (useCnt x, appCnt x)
                 of (n, 0) => concat[SVar.toString x, "(", Int.toString n, ")"]
                  | (n, m) => concat[
                        SVar.toString x, "(", Int.toString n,
                        "/", Int.toString m, ")"
                      ]
                (* end case *))
          end

    fun dump say (info as Info{useTbl, ...}) = let
          val v2s = varToString info
          fun sayv (x, _, first) = (
                if first then say [v2s x] else say [",", v2s x];
                false)
          in
            say ["Census: "];
            ignore(VTbl.foldi sayv true useTbl);
            say ["\n"]
          end

  end
