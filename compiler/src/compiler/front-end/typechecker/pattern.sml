(* pattern.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Binding and match pattern analysis.  This code is based on the paper
 *
 *      Warnings for Pattern Matching, by Luc Maranget.
 *      JFP 17(3), Cambridge University Press, 2007.
 *
 * TODO: there is a problem with pattern matches that involve unbound constructors.
 * The fix is probably in the type checker; i.e., do not analyse patterns that
 * have type errors.
 *)

structure Pattern : sig

    type pattern_info = {
        useless : int list,             (* list of row indices of redundant (aka useless) patterns *)
        uncovered : AST.pat option      (* if `SOME p`, then `p` describes a value that is not
                                         * covered by the matrix.
                                         *)
      }

  (* check if a binding pattern is irrefutable.  Returns `NONE` if it is;
   * otherwise it returns `SOME p`, where `p` is a counter example.
   *)
    val checkBind : AST.pat * Types.ty -> AST.pat option

  (* analyse a match *)
    val checkMatch : AST.pat list * Types.ty -> pattern_info

  end = struct

    structure A = AST
    structure Ty = Types
    structure CSet = ASTUtil.ConstSet

    type pattern_info = {
        useless : int list,             (* list of row indices of redundant (aka useless) patterns *)
        uncovered : AST.pat option      (* if `SOME p`, then `p` describes a value that is not
                                         * covered by the matrix.
                                         *)
      }

    val debug = Ctl.debugPatChk
    val say = Log.msg

(* NOTE: this function should probably be the the Basis List module *)
    fun findSome f [] = NONE
      | findSome f (x::xr) = (case f x of NONE => findSome f xr | something => something)

  (* a dummy variable for counter examples *)
    fun dummy tyc =
          Var.newTmp (concat["<", TyCon.nameOf tyc, ">"]) Ty.ErrorTy

    fun isTuplePat (A.TuplePat _) = true
      | isTuplePat (A.AsPat(_, p)) = isTuplePat p
      | isTuplePat _ = false

  (* return true if there exists a tuple pattern in the first column of the matrix *)
    fun tuplePatInFirstCol ((p :: _) :: r) = isTuplePat p orelse tuplePatInFirstCol r
      | tuplePatInFirstCol _ = false

  (* drop the first column of a matrix *)
    fun dropFirstCol [] = []
      | dropFirstCol ((_::pr)::psr) = pr :: dropFirstCol psr
      | dropFirstCol _ = raise Fail "unexpected empty row"

  (* specialize the first column of the matrix to a constant value *)
    fun specialize (c : A.const, prows : A.pat list list) = let
        (* compute the argument pattern for `c` *)
          val argPat = (case c
                 of A.DConst(dc, tys) => (case DataCon.argTypeOf'(dc, tys)
                       of SOME ty => [A.WildPat ty]
                        | NONE => []
                      (* end case *))
                  | _ => []
                (* end case *))
          fun match (p :: pr) = let
                fun match' (A.VarPat _ ) = SOME(argPat @ pr)
                  | match' (A.WildPat _) = SOME(argPat @ pr)
                  | match' (A.ConstPat c') = if ASTUtil.sameConst(c, c')
                      then SOME pr
                      else NONE
                  | match' (A.ConPat(dc, tys, q)) =
                      if ASTUtil.sameConst(c, A.DConst(dc, tys))
                        then SOME(q :: pr)
                        else NONE
                  | match' (A.AsPat(_, p)) = match' p
                in
                  match' p
                end
            | match _ = raise Fail "bogus row"
          in
            List.mapPartial match prows
          end

  (* return the "default" matrix, which has one fewer columns *)
    fun default (prows : A.pat list list) = let
          fun proj (A.VarPat _ :: pr) = SOME pr
            | proj (A.WildPat _ :: pr) = SOME pr
            | proj (A.ConstPat _ :: _) = NONE
            | proj (A.ConPat _ :: _) = NONE
            | proj (A.AsPat(_, p) :: r) = proj (p :: r)
            | proj (A.TuplePat _ :: _) = raise Fail "unexpected tuple pattern"
            | proj [] = raise Fail "unexpected empty row"
          in
            List.mapPartial proj prows
          end

  (* specialize the first column of the matrix to a tuple of the given arity *)
    fun tupleSpecialize (prows, tys) = let
          fun prefixWildCards ps =
                List.foldr (fn (ty, ps) => A.WildPat ty :: ps) ps tys
          fun expandFirstCol (A.VarPat _ :: pr) = prefixWildCards pr
            | expandFirstCol (A.WildPat _ :: pr) = prefixWildCards pr
            | expandFirstCol (A.TuplePat qs :: pr) = qs @ pr
            | expandFirstCol (A.AsPat(_, p) :: pr) = expandFirstCol (p :: pr)
            | expandFirstCol _ = raise Fail "bogus tuple pattern"
          in
            List.map expandFirstCol prows
          end

  (* project out the set of top-level constructors/constants from the first
   * column of a pattern matrix.
   *)
    fun projectConsts prows = let
          fun proj (A.VarPat _, cset) = cset
            | proj (A.WildPat _, cset) = cset
            | proj (A.ConstPat c, cset) = CSet.add(cset, c)
            | proj (A.ConPat(dc, tys, _), cset) = CSet.add(cset, A.DConst(dc, tys))
            | proj (A.TuplePat[], cset) = cset (* treat "()" as a constant *)
            | proj (A.TuplePat _, cset) = raise Fail "unexpected tuple pattern"
            | proj (A.AsPat(_, p), cset) = proj (p, cset)
          fun projCon (p1 :: _, cset) = proj (p1, cset)
            | projCon _ = raise Fail "unexpected empty row"
          in
            List.foldl projCon CSet.empty prows
          end

  (* is a constant set complete for its type *)
    fun isComplete (sigma, ty) = (case (TypeUtil.prune ty, CSet.numItems sigma)
           of (Ty.ConTy(_, tyc), 0) => TyCon.same(PrimTy.unitTyc, tyc)
            | (_, 0) => false
            | (Ty.ConTy(_, tyc), n) => (TyCon.spanOf tyc = n)
            | (Ty.ErrorTy, _) => true
            | (ty, _) => raise Fail(concat[
                  "isComplete({",
                  String.concatWithMap "," ASTUtil.constToString (CSet.toList sigma),
                  "}, ", TypeUtil.toString ty, ")"
                ])
          (* end case *))

  (* generate a counter example pattern for `ty` that is not in the constant set `sigma`.
   * We assume that `sigma` is not empty.
   *)
    fun genCounterExample (sigma, Ty.ConTy(_, tyc)) = (case TyCon.consOf tyc
           of [] => if TyCon.same(tyc, PrimTy.intTyc)
                  then let
                    val A.LConst(Literal.Int n, ty) = CSet.maxItem sigma
                    in
                      AST.ConstPat(AST.LConst(Literal.Int(n+1), ty))
                    end
(* TODO: generate a representative string value
                else if Ty.isInstance(tyc, PrimTy.stringTyc)
                  then
*)
                (* otherwise, we just use "<tyc>" to represent the counter example *)
                  else AST.VarPat(dummy tyc)
            | dcs => (
                case List.find (fn dc => not(CSet.member(sigma, A.DConst(dc, [])))) dcs
                 of SOME dc => if DataCon.isNullary dc
                      then AST.ConstPat(AST.DConst(dc, []))
                      else AST.ConPat(dc, [], A.WildPat Ty.ErrorTy)
                  | NONE => raise Fail "impossible"
                (* end case *))
          (* end case *))
      | genCounterExample (_, ty) =
          raise Fail("expected type constructor, but got " ^ TypeUtil.toString ty)

  (* `useful (prows, q, ty)` returns `true` if `q` covers some value that
   * is not covered by `prows`.
   *)
    fun useful (prows : A.pat list list, q : A.pat list) = let
          fun chk ([], []) = true       (* no rows or columns *)
            | chk ([]::_, []) = false   (* rows, but no columns *)
            | chk (prows, q::qr) = let
                fun doVar () = (case ASTUtil.typeOfPat q
                       of Ty.TupleTy tys => if tuplePatInFirstCol prows
                            then let
                            (* replace q with wild cards *)
                              val qs' = List.foldr
                                    (fn (ty, qs) => A.WildPat ty :: qs)
                                      qr tys
                              in
                                chk (tupleSpecialize(prows, tys), qs')
                              end
                            else chk (dropFirstCol prows, qr)
                        | Ty.ErrorTy => true
                        | ty => let
                            val sigma = projectConsts prows
                            in
                              if isComplete (sigma, ASTUtil.typeOfPat q)
                                then let
                                  val qrow = [q::qr]
                                  fun chkC c = let
                                        val [qrow'] = specialize(c, qrow)
                                        in
                                          chk (specialize(c, prows), qrow')
                                        end
                                  in
                                    CSet.exists chkC sigma
                                  end
                                else chk (default prows, qr)
                            end
                      (* end case *))
                in
                  case q
                   of A.VarPat _ => doVar()
                    | A.WildPat _ => doVar()
                    | A.ConstPat c => chk (specialize(c, prows), qr)
                    | A.ConPat(dc, tys, q') =>
                        chk (specialize(A.DConst(dc, tys), prows), q'::qr)
                    | A.TuplePat qs' => chk (
                        tupleSpecialize(prows, List.map ASTUtil.typeOfPat qs'),
                        qs' @ qr)
                    | A.AsPat(_, p) => chk(prows, p::qr)
                  (* end case *)
                end
            | chk _ = raise Fail "arg/pattern arity mismatch"
          in
            chk (prows, q)
          end
(*DEBUG*)handle ex => (
            print(concat["useful (-, [",
                String.concatWithMap ", " ASTUtil.patToString q, "])\n"
              ]);
            raise ex)

  (* exhaustiveness check, which returns `NONE` if the pattern is exhaustive and
   * `SOME pat` if it is not, where `pat` is a pattern that is not covered by
   * the first argument.
   *)
    fun exhaustiveChk (_, Ty.ErrorTy) = NONE
      | exhaustiveChk (pmat : A.pat list, ty) = let
          fun optTuple NONE = NONE
            | optTuple (SOME ps) = SOME[A.TuplePat ps]
          fun chk ([], []) = SOME[]
            | chk ([]::_, []) = NONE
            | chk (prows, ty::tyr) = (
                case TypeUtil.prune ty
                 of Ty.ErrorTy => NONE
                  | ty as Ty.TupleTy tys =>
                      if tuplePatInFirstCol prows
                        then (case chk (tupleSpecialize(prows, tys), tys @ tyr)
                           of NONE => NONE
                            | SOME ps => let
                                val (ps1, ps2) = List.splitAt(ps, List.length tys)
                                in
                                  SOME(A.TuplePat ps1 :: ps2)
                                end
                          (* end case *))
                        else (case chk (dropFirstCol prows, tyr)
                           of NONE => NONE
                            | SOME ps => SOME(A.WildPat ty :: ps)
                          (* end case *))
                  | ty => let
                      val sigma = projectConsts prows
                      in
                        if isComplete(sigma, ty)
                          then let
                          (* sigma covers all of the possible constructors, so we
                           * check each one for a possible counter example
                           *)
                            fun chk' (c as A.DConst(dc, tys)) = (
                                  case DataCon.argTypeOf'(dc, tys)
                                   of SOME ty => (case chk (specialize(c, prows), ty :: tyr)
                                         of NONE => NONE
                                          | SOME(q1::qr) => SOME(A.ConPat(dc, tys, q1)::qr)
                                          | SOME _ => raise Fail "expected counter example"
                                        (* end case *))
                                    | NONE => chk (specialize(c, prows), tyr)
                                  (* end case *))
                              | chk' c = (case chk (specialize(c, prows), tyr)
                                   of NONE => NONE
                                    | SOME qs => SOME(A.ConstPat c :: qs)
                                  (* end case *))
                            in
                              findSome chk' (CSet.listItems sigma)
                            end
                          else (case chk (default prows, tyr)
                             of SOME qs => if CSet.isEmpty sigma
                                  then SOME(A.WildPat ty :: qs)
                                  else SOME(genCounterExample(sigma, ty) :: qs)
                              | NONE => NONE
                            (* end case *))
                      end
                (* end case *))
            | chk _ = raise Fail "arg/pattern arity mismatch"
          in
            case chk (List.map (fn p => [p]) pmat, [TypeUtil.prune ty])
             of NONE => NONE
              | SOME[p] => SOME p
              | _ => raise Fail "expected a single pattern"
            (* end case *)
          end
(*DEBUG*)handle ex => (
print(concat["** exhaustiveChk([", String.concatWithMap " | " ASTUtil.patToString pmat,
"], ", TypeUtil.fmt {long=true} ty, ")\n"]);
raise ex)

    fun checkBind (p, Ty.ErrorTy) = NONE
      | checkBind (p, ty) = exhaustiveChk ([p], ty)
(*DEBUG*)handle ex => (
print(concat["checkBind (", ASTUtil.patToString p, " : ", TypeUtil.toString ty, ")\n"]);
raise ex)

    fun checkMatch ([], _) = raise Fail "unexpected empty case"
      | checkMatch (_, Ty.ErrorTy) = { useless = [], uncovered = NONE }
      | checkMatch (p::pr : A.pat list, ty) = let
        (* `chkForUseless (i, p::r, prefix)` checks if `p` is useful w.r.t. `prefix`.
         * If it is not, then `i` is added to the list of useless pattern indices.
         * Note that we take advantage of the fact the order of patterns in `prefix`
         * does not matter when testing is `p` is useless.
         *)
          fun chkForUseless (_, [], _) = []
            | chkForUseless (i, p::pr, prefix) = if useful(prefix, [p])
                then chkForUseless (i+1, pr, [p]::prefix)
                else i :: chkForUseless (i+1, pr, [p]::prefix)
          in {
            useless = chkForUseless (0, pr, [[p]]),
            uncovered = exhaustiveChk (p::pr, ty)
          } end
(*DEBUG*)handle ex => (
            print(concat[
                "checkMatch ([",
                String.concatWithMap "," ASTUtil.patToString (p::pr),
                "], ", TypeUtil.toString ty, ")\n"
              ]);
            raise ex)

  end
