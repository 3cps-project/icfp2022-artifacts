(* backtrack-mc.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * A simple backtracking-based pattern compilation scheme.  This code is based
 * on the sample from
 *
 *      https://github.com/JohnReppy/compiling-pattern-guards
 *
 * which, in turn, implements the classic backtracking scheme described in
 * Section 3 of
 *
 *      Optimizing Pattern Matching
 *      by Fabrice Le Fessant and Luc Maranget
 *      ICFP 2001
 *
 * We implement two basic optimizations: first, we reorder rows to increase the size
 * of partitions (Section 4.1 from [Le Fessant 2001]) and, second, we exploit the
 * fact that patterns are guaranteed to be exhaustive by the typechecker (Section 4.2
 * from [Le Fessant 2001]).
 *)

structure BacktrackMC : sig

    val transform : AST.var * (AST.pat * AST.exp) list * Types.ty -> AST.exp

  end = struct

    structure A = AST
    structure Ty = Types
    structure DC = DataCon
    structure CSet = ASTUtil.ConstSet

    datatype pat = datatype A.pat

  (* a clause matrix *)
    type row = pat list * A.exp
    type cmat = row list

    val patToString = ASTUtil.patToString
    val tyToString = TypeUtil.toString

  (* temporary varables *)
    val newTmp = Var.newTmp "_t"
    val newKont = Var.newTmp "_k"
    val newItem = Var.newTmp "_item"
    val newArg = Var.newTmp "_arg"

    fun letVal (lhs, lhsScm, rhs, e) = A.LetExp(A.ValDecl(lhs, lhsScm, rhs), e)

  (* make the expression `let fun k xs = e2 in e1[k/exitK] end`, where `k`
   * is marked as a join point.
   *)
    fun letcont (e1 : Var.t option -> A.exp, xs, e2) = let
          val resTy = ASTUtil.typeOfExp e2
          val (arg, argTy, e2') = (case List.map Var.monoTypeOf xs
                 of [] => (newTmp PrimTy.unitTy, PrimTy.unitTy, e2)
                  | [ty] => (List.hd xs, ty, e2)
                  | tys => let
                      val argTy = Ty.TupleTy tys
                      val arg = newArg argTy
                      val e = A.CaseExp(
                            A.VarExp(arg, []),
                            [(TuplePat(List.map VarPat xs), e2)],
                            resTy)
                      in
                        (arg, argTy, e)
                      end
                (* end case *))
          val k = newKont(Ty.FunTy(argTy, resTy))
          in
            Var.markJoin k;
            A.LetExp(A.FunDecl([(k, [arg], e2')]), e1 (SOME k))
          end

    fun bindVar (exp, x, y) = letVal(VarPat x, Var.typeOf x, A.VarExp(y, []), exp)

    fun call (f, [arg], ty) = A.ApplyExp(A.VarExp(f, []), arg, ty)
      | call (f, args, ty) = A.ApplyExp(A.VarExp(f, []), A.TupleExp args, ty)

  (* preprocess the first column of a matrix to move shift the variable
   * bindings of top-level layered patterns into the actions.
   *)
    fun flattenLayers ([], mat) = mat
      | flattenLayers (x::_, mat) = let
          fun doRow (p :: rowPats, act) = let
                fun doPat (AsPat(y, p), act) = doPat(p, bindVar(act, y, x))
                  | doPat (p, act) = (p :: rowPats, act)
                in
                  doPat (p, act)
                end
          in
            List.map doRow mat
          end

  (* classification of a block of rows according to the "Classical Scheme"
   * (Section 3.3) of Le Fessant and Maranget.  Note that we have added a
   * case for where the first column has a tuple type and is not all variables.
   *)
    datatype row_block
      = Vars of cmat                    (* variables in first column *)
      | Tuple of cmat                   (* tuple pattern in first column *)
      | Constr of CSet.set * cmat       (* constants in first column *)

  (* test two rows for compatibility *)
    fun compatible (ps1, _) (ps2, _) = ListPair.allEq ASTUtil.compatiblePats (ps1, ps2)

  (* split a matrix into blocks of rows based on the first column of patterns *)
    fun split (rows : row list) = let
        (* return the first pattern of a row *)
          fun firstPat (AsPat _ :: _, _) = raise Fail "unexpected layered pattern"
            | firstPat (p :: _, _) = p
            | firstPat ([],  _) = raise Fail "firstPat: empty row"
        (* figure out what the next block is going to be and call the
         * appropriate collection function.
         *)
          fun collect (row::rowr, blks) = (case firstPat row
               of VarPat _ => collectVars (rowr, [row], blks)
                | WildPat _ => collectVars (rowr, [row], blks)
                | ConstPat c => collectConsts (c, rowr, [row], blks)
                | ConPat(dc, tys, _) =>
                    collectConsts (A.DConst(dc, tys), rowr, [row], blks)
                | TuplePat _ => Tuple(row::rowr) :: blks
                | AsPat _ => raise Fail "unexpected layered pattern"
              (* end case *))
            | collect _ = raise Fail "expected rows"
        (* collect a prefix of rows that have a variable pattern
         * in the first column.
         *)
          and collectVars ([], rows, blks) = Vars(List.rev rows)::blks
            | collectVars (row::rowr, rows, blks) = (case firstPat row
                 of VarPat _ => collectVars (rowr, row::rows, blks)
                  | WildPat _ => collectVars (rowr, row::rows, blks)
                  | _ => collect (row::rowr, Vars(List.rev rows)::blks)
                (* end case *))
        (* collect a prefix of rows that have a constant or constructor pattern
         * in the first column.  We keep track of the set of constructors
         * so that we can detect if the rows are exhaustive.
         *)
          and collectConsts (c, rowr, rows, blks) = let
                fun addDC (cset, dc, tys) = CSet.add(cset, A.DConst(dc, tys))
              (* collect the rows that start with a constructor into a Constr block *)
                fun collect' ([], rows, cset) = Constr(cset, List.rev rows) :: blks
                  | collect' (row::rowr, rows, cset) = (case firstPat row
                       of ConstPat c =>
                            collect' (rowr, row::rows, CSet.add(cset, c))
                        | ConPat(dc, tys, _) =>
                            collect' (rowr, row::rows, addDC(cset, dc, tys))
                        | _ => let
                          (* check the rest of the rows to see if there are any rows with a
                           * head constructor that can be lifted up to the Constr block
                           * we are building.
                           *)
                            fun collect'' ([], cRows, cset, rRows) = (cRows, cset, rRows)
                              | collect'' (row::rowr, cRows, cset, rRows) = (
                                  case firstPat row
                                   of ConPat(dc, tys, _) =>
                                        if List.exists (compatible row) rRows
                                          then collect'' (rowr, cRows, cset, row::rRows)
                                          else (* row can be lifted into the "C" matrix *)
                                            collect'' (rowr, row::cRows, addDC(cset, dc, tys), rRows)
                                    | _ => collect'' (rowr, cRows, cset, row::rRows)
                                  (* end case *))
                            val (cRows, cset, rRows) = collect'' (row::rowr, rows, cset, [])
                            in
                              collect (rev rRows, Constr(cset, List.rev cRows)::blks)
                            end
                      (* end case *))
                in
                  collect' (rowr, rows, CSet.singleton c)
                end
          in
            List.rev (collect (rows, []))
          end

  (* `comp (occs, mat, exitK, resTy)` generates code for the pattern
   * matrix `mat` matching the variable occurrences `occs`.  This function
   * splits the matrix into blocks (essentially the mixture rule) and then
   * applies the appropriate translation function to each block.  The
   * exitK is an option value; we use `NONE` for the outermost call,
   * since the pattern is guaranteed to be exhaustive.
   *)
    fun comp (xs, mat : cmat, exitK, resTy) = (case flattenLayers(xs, mat)
           of (([], act)::_) => act (* no columns left *)
            | rows => (case (xs, split rows)
                 of (x::xr, blk::blkr) => let
                    (* invoke the appropriate translation function for the block *)
                      fun dispatch (Vars mat) k =
                            variableRule (x, xr, mat, k, resTy)
                        | dispatch (Tuple mat) k =
                            tupleRule (x, xr, mat, k, resTy)
                        | dispatch (Constr(cset, mat)) k =
                            constructorRule (x, xr, cset, mat, k, resTy)
                    (* chain together the blocks using continuation functions
                     * for backtracking
                     *)
                      fun f (blk, []) = dispatch blk exitK
                        | f (blk1, blk2::blks) =
                            letcont (dispatch blk1, [], f (blk2, blks))
                      in
                        f (blk, blkr)
                      end
                  | _ => raise Fail "impossible: bogus matrix"
                (* end case *))
          (* end case *))

    and variableRule (x, xr, mat, exitK, resTy) = let
        (* shift the first-column variable to a let binding in the action *)
          fun doRow ((VarPat y :: rowPats, act), rows) =
                (rowPats, bindVar(act, y, x)) :: rows
            | doRow ((WildPat _ :: rowPats, act), rows) =
                (rowPats, act) :: rows
            | doRow ((p :: _, _), _) = raise Fail(concat[
                  "impossible: non-variable pattern (", patToString p, ")"
                ])
            | doRow (([], _), _) = raise Fail "impossible: empty row"
          in
            comp (xr, List.foldr doRow [] mat, exitK, resTy)
          end

  (* replace the first column with one column per tuple component *)
    and tupleRule (x, xr, mat, exitK, resTy) = let
          val tys = (case Var.monoTypeOf x
                 of Ty.TupleTy tys => tys
                  | ty as Ty.ConTy([], tyc) => if TyCon.same(tyc, TyCon.unitTyc)
                      then []
                      else raise Fail("expected tuple type, but got " ^ tyToString ty)
                  | ty => raise Fail("expected tuple type, but got " ^ tyToString ty)
                (* end case *))
        (* expand the patterns in the first column *)
          fun doRow ((VarPat y :: rowPats, act), rows) = let
                val pats = List.map WildPat tys
                in
                  (pats @ rowPats, bindVar(act, y, x)) :: rows
                end
            | doRow ((WildPat _ :: rowPats, act), rows) = let
                val pats = List.map WildPat tys
                in
                  (pats @ rowPats, act) :: rows
                end
            | doRow ((TuplePat pats :: rowPats, act), rows) =
                (pats @ rowPats, act) :: rows
            | doRow ((p :: _, _), _) = raise Fail(concat[
                  "impossible: non-tuple pattern (", patToString p, ")"
                ])
            | doRow (([], _), _) = raise Fail "impossible: empty row"
        (* expand the argument occurrences *)
          val xs' = List.map (fn ty => newItem ty) tys
          in
            letVal(TuplePat(List.map VarPat xs'), Var.typeOf x, A.VarExp(x, []),
              comp (xs' @ xr, List.foldr doRow [] mat, exitK, resTy))
          end

    and constructorRule (x, xr, cset, mat, exitK, resTy) = let
          val tyc = (case Var.monoTypeOf x
                 of Ty.ConTy(_, tyc) => tyc
                  | ty => raise Fail("expected tycon, but got " ^ tyToString ty)
                (* end case *))
        (* make the switch case for the constructor `dc` *)
          fun mkCase (A.DConst(dc, tys), branches) = let
                fun doRow ((ConstPat(A.DConst(dc', _)) :: pr, act), rows) =
                      if DC.same(dc, dc')
                        then (pr, act) :: rows
                        else rows
                  | doRow ((ConPat(dc', _, pat) :: pr, act), rows) =
                      if DC.same(dc, dc')
                        then (pat :: pr, act) :: rows
                        else rows
                  | doRow ((p :: _, _), _) = raise Fail(concat[
                        "impossible: non-constructor pattern (", patToString p, ")"
                      ])
                  | doRow (([], _), _) = raise Fail "impossible: empty row"
                val rows = List.foldr doRow [] mat
                in
                  case DC.argTypeOf dc
                   of SOME tyScm => let
                        val y = newArg (TypeUtil.applyScheme(tyScm, tys))
                        val act = comp (y :: xr, rows, exitK, resTy)
                        in
                          (ConPat(dc, tys, VarPat y), act) :: branches
                        end
                    | NONE => let
                        val act = comp (xr, rows, exitK, resTy)
                        in
                          (ConstPat(A.DConst(dc, tys)), act) :: branches
                        end
                  (* end case *)
                end
            | mkCase (A.LConst(lit, ty), branches) = let
                fun doRow ((ConstPat(A.LConst(lit', _)) :: pr, act), rows) =
                      if Literal.same(lit, lit')
                        then (pr, act) :: rows
                        else rows
                  | doRow ((p :: _, _), _) = raise Fail(concat[
                        "impossible: non-integer pattern (", patToString p, ")"
                      ])
                  | doRow (([], _), _) = raise Fail "impossible: empty row"
                val act = comp (xr, List.foldr doRow [] mat, exitK, resTy)
                in
                  (ConstPat(A.LConst(lit, ty)), act) :: branches
                end
        (* is the column exhaustive for the datatype? *)
          val default = (case exitK
                 of SOME k => if (TyCon.spanOf tyc = CSet.numItems cset)
                      then []
                      else [(WildPat(Var.monoTypeOf x), call(k, [], resTy))]
                  | NONE => [] (* no outermost escape *)
                (* end case *))
          in
            A.CaseExp(A.VarExp(x, []), CSet.foldr mkCase default cset, resTy)
          end

    fun transform (x, cases, ty) = let
          fun mkRow (pat, exp) = ([pat], exp)
          in
            comp ([x], List.map mkRow cases, NONE, ty)
          end

  end
