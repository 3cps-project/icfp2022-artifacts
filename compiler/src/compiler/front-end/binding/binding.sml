(* binding.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Binding-check pass.
 *)

structure Binding : sig

    val check : Error.err_stream * ParseTree.comp_unit -> BindTree.comp_unit

  end = struct

    structure PT = ParseTree
    structure BT = BindTree
    structure Env = BindingEnv
    structure ASet = AtomSet
    structure TVSet = BT.TyVar.Set

    fun unbound errS (span, kind, id) =
          Error.errorAt(errS, span, ["unbound ", kind, " `", Atom.toString id, "`"])

    fun unbound' errS (span, kind, ([], id)) = unbound errS (span, kind, id)
      | unbound' errS (span, kind, (path, id)) =
          Error.errorAt(errS, span, [
              "unbound ", kind, " `",
              String.concatWithMap "." Atom.toString (path @ [id]), "`"
            ])

  (* empty "signature" for error case *)
    val emptySign = BT.Sign{strs=[], tycs=[], cons=[], vals=[]}

  (* check a list of bound identifiers for duplicates, returning a list of name-variable
   * pairs.
   *)
    fun checkForDuplicates errS (ids, kind, cxt) = let
          fun chk ((span, x, x'), (xs, bnds)) =
                if ASet.member(xs, x)
                  then (
                     Error.errorAt (errS, span, [
                        "duplicate ", kind, " `", Atom.toString x, "` ", cxt
                      ]);
                    (xs, bnds))
                  else (ASet.add(xs, x), (x, x')::bnds)
          val (_, bnds) = List.foldl chk (ASet.empty, []) ids
          in
            List.rev bnds
          end

    fun check (errS, {span, tree}) = let
          val unbound = unbound errS
          val unbound' = unbound' errS
          fun chkForDups arg = checkForDuplicates errS arg
          fun spanToLoc span = Error.location(errS, span)
        (* check the path of a qualified identifier *)
          fun chkPath (span, env, strId, rest) = (case Env.findStruct(env, strId)
                 of SOME(strId', modEnv) => let
                      fun chk (modEnv, [], path) = SOME(List.rev path, modEnv)
                        | chk (modEnv, strId::rest, path) = (case Env.findStruct'(modEnv, strId)
                             of SOME(strId', modEnv) => chk (modEnv, rest, strId'::path)
                              | NONE => (
                                  unbound(span, "structure", strId);
                                  NONE)
                            (* end case *))
                      in
                        chk (modEnv, rest, [strId'])
                      end
                  | NONE => (
                      unbound (span, "structure", strId);
                      NONE)
                (* end case *))
        (* check a qualified ID *)
          fun chkQId (span, env, ([], id)) = SOME(NONE, id)
            | chkQId (span, env, (strId::rest, id)) = (case chkPath(span, env, strId, rest)
                 of NONE => NONE
                  | someStr => SOME(someStr, id)
                (* end case *))
        (* check a list of bound type variables *)
          fun checkTyVars (span, env, tvs, cxt) = let
                fun mkTV (tv, tvBinds) =
                      (span, tv, BT.TyVar.new(tv, spanToLoc span)) :: tvBinds
                val btvs = List.foldr mkTV [] tvs
                val btvs' = chkForDups (btvs, "type variable", cxt)
                val env' = Env.tyvsFromList (env, btvs')
                in
                  (List.map #2 btvs', env')
                end
        (* top-level declarations *)
          fun chkDecl (_, env, PT.MarkDecl{span, tree}) = let
                val (dcl', env') = chkDecl (span, env, tree)
                in
                  (BT.MarkDecl{span=span, tree=dcl'}, env')
                end
            | chkDecl (span, env, PT.StructDecl(lhsId, strExp)) = let
                val lhsId' = BT.StrId.new(lhsId, spanToLoc span)
                fun insert senv = Env.insertStruct(env, lhsId, lhsId', senv)
                fun chkStrExp (_, PT.MarkStrExp{span, tree}) = let
                      val (sign, strExp', env') = chkStrExp (span, tree)
                      in
                        (sign, BT.MarkStrExp{span=span, tree=strExp'}, env')
                      end
                  | chkStrExp (span, PT.IdStrExp qid) = (case chkQId(span, env, qid)
                       of SOME(SOME(path', strEnv), id) => (
                            case Env.findStruct'(strEnv, id)
                             of SOME(id', senv) =>
                                  (Env.signOf senv, BT.IdStrExp(path', id'), insert senv)
                              | NONE => (
                                  unbound' (span, "structure", qid);
                                  (emptySign, BT.ErrorStrExp, env))
                            (* end case *))
                        | SOME(NONE, id) => (case Env.findStruct(env, id)
                             of SOME(id', senv) =>
                                  (Env.signOf senv, BT.IdStrExp([], id'), insert senv)
                              | NONE => (
                                  unbound (span, "structure", id);
                                  (emptySign, BT.ErrorStrExp, env))
                            (* end case *))
                        | NONE => (emptySign, BT.ErrorStrExp, env)
                      (* end case *))
                  | chkStrExp (span, PT.DefStrExp dcls) = let
                      val env = Env.structBegin env
                      val (dcls', env') = chkDecls (span, env, dcls)
                      val (strEnv, env') = Env.structEnd (env', lhsId, lhsId')
                      in
                        (Env.signOf strEnv, BT.DefStrExp dcls', env')
                      end
                val (sign, strExp', env') = chkStrExp (span, strExp)
                in
                  (BT.StructDecl(lhsId', sign, strExp'), env')
                end
            | chkDecl (span, env, PT.LocalDecl(dcls1, dcls2)) = let
                val env = Env.localBegin env
                val (dcls1', env) = chkDecls (span, env, dcls1)
                val env = Env.localIn env
                val (dcls2', env) = chkDecls (span, env, dcls2)
                val env = Env.localEnd env
                in
                  (BT.LocalDecl(dcls1', dcls2'), env)
                end
            | chkDecl (span, env, PT.TyDecl(tvs, id, ty)) = let
                val (tvs', env'') = checkTyVars (span, env, tvs, "in type declaration")
                val ty' = chkTy (span, env'', ty)
                val (id', env') = Env.bindTy(env, id, spanToLoc span)
                in
                  (BT.TyDecl(tvs', id', ty'), env')
                end
            | chkDecl (span, env, PT.DataDecl dts) = let
              (* first pass, bind type names *)
                val (env', tycs') = let
                      fun projFn {span, tree=(_, id, _)} =
                            (span, id, BT.TycId.new(id, spanToLoc span))
                      val bts = List.map projFn dts
                      val bts' = chkForDups (bts, "type identifier", "in datatype declaration")
                      in
                        (Env.tycsFromList (env, bts'), List.map #2 bts')
                      end
              (* second pass, process constructors *)
                fun chk (tyc', {span, tree=(tvs, _, cons)}, (dts, bcs)) = let
                      val (tvs', env'') = checkTyVars (span, env', tvs, "in datatype declaration")
                      val (cons', bcs') = List.foldr
                            (fn (conDcl, (cons', bcs')) => let
                                  val (bc, conDcl') = chkConDecl (span, env'', conDcl)
                                  in
                                    (conDcl' :: cons', bc :: bcs')
                                  end)
                              ([], bcs)
                                cons
                      val dt = {span=span, tree=(tvs', tyc', cons')}
                      in
                        (dt::dts, bcs')
                      end
                val (dts', bcs) = ListPair.foldr chk ([], []) (tycs', dts)
                val bcs' = chkForDups (bcs, "constructor", "in datatype declaration")
                in
                  (BT.DataDecl dts', Env.consFromList(env', bcs'))
                end
            | chkDecl (span, env, PT.ExnDecl conDcl) = let
                val ((_, id, id'), conDcl') = chkConDecl (span, env, conDcl)
                in
                  (BT.ExnDecl conDcl', Env.insertConId(env, id, id'))
                end
            | chkDecl (span, env, PT.ValueDecl vdcl) = let
                val (vdcl', env') = chkValDecl (span, env, vdcl)
                in
                  (BT.ValueDecl vdcl', env')
                end
        (* check a list of top-level declarations *)
          and chkDecls (span, env, dcls) = let
                fun chk (dcl, (env, dcls')) = let
                      val (dcl', env') = chkDecl (span, env, dcl)
                      in
                        (env', dcl'::dcls')
                      end
                val (env', dcls') = List.foldl chk (env, []) dcls
                in
                  (List.rev dcls', env')
                end
        (* data-constructor (including exception) definitions *)
          and chkConDecl (_, env, PT.MarkConDecl{span, tree}) = let
                val (bc, conDcl') = chkConDecl (span, env, tree)
                in
                  (bc, BT.MarkConDecl{span = span, tree = conDcl'})
                end
            | chkConDecl (span, env, PT.ConDecl(id, optTy)) = let
                val id' = BT.ConId.new(id, spanToLoc span)
                val optTy' = Option.map (fn ty => chkTy(span, env, ty)) optTy
                in
                  ((span, id, id'), BT.ConDecl(id', optTy'))
                end
        (* value declarations *)
          and chkValDecl (span, env, vd) = let
              (* free type variables are implicitly bound at the innermost enclosing
               * value declaration (Section 4.6; Definition of Standard ML).
               *)
                val _ = Env.pushTyVarScope env
                fun chk (_, PT.MarkVDecl{span, tree}) = let
                      val (vdcl', env') = chk (span, tree)
                      in
                        (BT.MarkVDecl{span=span, tree=vdcl'}, env')
                      end
                  | chk (span, PT.ValVDecl(p, e)) = let
                    (* check `val p = e` *)
                      val (p', bvs) = chkPat (span, env, p)
                      val e' = chkExp (span, env, e)
                      val bvs' = chkForDups (bvs, "variable", "in pattern")
                      val env' = Env.varsFromList (env, bvs')
                      in
                        (BT.ValVDecl(Env.popTyVarScope env, p', e'), env')
                      end
                  | chk (span, PT.FunVDecl fbs) = let (* check `fun fb and ... and fb` *)
                    (* first step is to check that all clauses have the same number
                     * of arguments and the same function name.  We also strip down
                     * the representation.
                     *)
                      val fbs' = let
                            fun chkFn _ (PT.MarkFunct{span, tree}) = chkFn span tree
                              | chkFn span (PT.Funct clauses) = let
                                (* get the name and arity of the function from the first clause *)
                                  val (fname, arity) = let
                                        val (f, params, _, _) = #tree(hd clauses)
                                        in
                                          (f, List.length params)
                                        end
                                (* check that the clauses all have the same name and arity *)
                                  fun chk {span, tree=(f, params, optTy, e)} = let
                                        val n = List.length params
                                        val params = if (n < arity)
                                                then (
                                                  Error.errorAt (errS, span, [
                                                    ]);
                                                (* add missing patterns *)
                                                  params @
                                                    List.tabulate(arity-n, fn _ => PT.WildPat))
                                              else if (n > arity)
                                                then (
                                                  Error.errorAt (errS, span, [
                                                    ]);
                                                (* trim excess patterns *)
                                                  List.take(params, arity))
                                                else params
                                        in
                                          if Atom.same(f, fname)
                                            then ()
                                            else Error.errorAt (errS, span, [
                                                "clauses do not all have same function name; \
                                                \expected '", Atom.toString fname,
                                                "', but found '", Atom.toString f
                                              ]);
                                          {span=span, tree=(params, optTy, e)}
                                        end
                                  in
                                    {span = span, tree = (fname, List.map chk clauses)}
                                  end
                            in
                              List.map (chkFn span) fbs
                            end
                    (* first, extend the environment with the function names *)
                      val (env', fs') = let
                            fun projFn {span, tree=(f, _)} =
                                  (span, f, BT.VarId.new(f, spanToLoc span))
                            val bfs = List.map projFn fbs'
                            val bfs' = chkForDups (bfs, "function", "in function declaration")
                            in
                              (Env.varsFromList (env, bfs'), List.map #2 bfs')
                            end
                    (* second, process each function binding *)
                      fun chkFB (f', {span, tree=(_, clauses)}) = let
                            fun chkClause {span, tree=(ps, optTy, e)} = let
                                (* process the parameter patterns and gather the parameter variables *)
                                  val (ps', bvs) = let
                                        fun chk (p, (ps', bvs)) = let
                                              val (p', bvs2) = chkPat (span, env', p)
                                              in
                                                (p'::ps', bvs2@bvs)
                                              end
                                        in
                                          List.foldr chk ([], []) ps
                                        end
                                  val bvs' = chkForDups (bvs, "variable", "function parameters")
                                  val env' = Env.varsFromList (env', bvs')
                                  val optTy' = Option.map (fn ty => chkTy (span, env, ty)) optTy
                                  val e' = chkExp (span, env', e)
                                  in
                                    {span = span, tree = (ps', optTy', e')}
                                  end
                            in
                              BT.Funct{span = span, tree = (f', List.map chkClause clauses)}
                            end
                      val fbs'' = ListPair.mapEq (fn (f', fb) => chkFB(f', fb)) (fs', fbs')
                      in
                        (BT.FunVDecl(Env.popTyVarScope env, fbs''), env')
                      end
                in
                  chk (span, vd)
                end
        (* types *)
          and chkTy (_, env, PT.MarkTy{span, tree}) =
                BT.MarkTy{span=span, tree=chkTy (span, env, tree)}
            | chkTy (span, env, PT.NamedTy(tys, qid)) = let
                val tys' = List.map (fn ty => chkTy(span, env, ty)) tys
                in
                  case chkQId (span, env, qid)
                   of SOME(SOME(path', strEnv), id) => (case Env.findTyId' (strEnv, id)
                         of SOME id' => BT.NamedTy(tys', (path', id'))
                          | NONE => (
                              unbound' (span, "type constructor", qid);
                              BT.ErrorTy)
                        (* end case *))
                    | SOME(NONE, id) => (case Env.findTyId (env, id)
                         of SOME id' => BT.NamedTy(tys', ([], id'))
                          | NONE => (
                              unbound (span, "type constructor", id);
                              BT.ErrorTy)
                        (* end case *))
                    | NONE => BT.ErrorTy
                  (* end case *)
                end
            | chkTy (span, env, PT.VarTy tv) = (case Env.findTyVar(env, tv)
                 of SOME tv' => BT.VarTy tv'
                  | NONE => BT.VarTy(Env.bindTyVar(env, tv, spanToLoc span))
                (* end case *))
            | chkTy (span, env, PT.TupleTy tys) =
                BT.TupleTy(List.map (fn ty => chkTy(span, env, ty)) tys)
            | chkTy (span, env, PT.FunTy(ty1, ty2)) =
                BT.FunTy(chkTy(span, env, ty1), chkTy(span, env, ty2))
        (* expressions *)
          and chkExp (span, env, exp) = (case exp
                 of PT.MarkExp{span, tree} => BT.MarkExp{span=span, tree=chkExp(span, env, tree)}
                  | PT.LetExp(vds, e) => let
                      val (vds', env') = List.foldl
                            (fn (vd, (vds', env)) => let
                                val (vd', env') = chkValDecl (span, env, vd)
                                in
                                  (vd' :: vds', env')
                                end)
                              ([], env) vds
                      in
                        BT.LetExp(List.rev vds', chkExp(span, env', e))
                      end
                  | PT.IfExp(e1, e2, e3) =>
                      BT.IfExp(chkExp(span, env, e1), chkExp(span, env, e2), chkExp(span, env, e3))
                  | PT.FnExp cases =>
                      BT.FnExp(chkCases (span, env, cases))
                  | PT.CaseExp(e, cases) =>
                      BT.CaseExp(chkExp(span, env, e), chkCases (span, env, cases))
                  | PT.HandleExp(e, cases) =>
                      BT.HandleExp(chkExp(span, env, e), chkCases (span, env, cases))
                  | PT.RaiseExp e => BT.RaiseExp(chkExp(span, env,e))
                  | PT.AndAlsoExp(e1, e2) =>
                      BT.AndAlsoExp(chkExp(span, env,e1), chkExp(span, env, e2))
                  | PT.OrElseExp(e1, e2) =>
                      BT.OrElseExp(chkExp(span, env,e1), chkExp(span, env, e2))
                  | PT.BinaryExp(e1, id, e2) => let
                      val arg' = BT.TupleExp[chkExp(span, env, e1), chkExp(span, env, e2)]
                      in
                        case Env.findValId(env, id)
                         of SOME(BT.Con dc') => BT.ApplyExp(BT.ConExp([], dc'), arg')
                          | SOME(BT.Var x') => BT.ApplyExp(BT.VarExp([], x'), arg')
                          | NONE => raise Fail "impossible"
                        (* end case *)
                      end
                  | PT.ApplyExp(e1, e2) =>
                      BT.ApplyExp(chkExp(span, env,e1), chkExp(span, env, e2))
                  | PT.TupleExp es => BT.TupleExp(chkExps (span, env, es))
                  | PT.ListExp es => BT.ListExp(chkExps (span, env, es))
                  | PT.SeqExp es => BT.SeqExp(chkExps (span, env, es))
                  | PT.IdExp qid => let
                      fun mk (path', BT.Con dc') = BT.ConExp(path', dc')
                        | mk (path', BT.Var x') = BT.VarExp(path', x')
                      in
                        case chkQId(span, env, qid)
                         of SOME(SOME(path', strEnv), id) => (case Env.findValId'(strEnv, id)
                               of SOME id' => mk (path', id')
                                | NONE => (
                                    unbound' (span, "value identifier", qid);
                                    BT.ErrorExp)
                              (* end case *))
                          | SOME(NONE, id) => (case Env.findValId(env, id)
                               of SOME id' => mk ([], id')
                                | NONE => (
                                    unbound (span, "value identifier", id);
                                    BT.ErrorExp)
                            (* end case *))
                          | NONE => BT.ErrorExp
                        (* end case *)
                      end
                  | PT.ConstExp lit => BT.ConstExp lit
                  | PT.ConstraintExp(e, ty) =>
                      BT.ConstraintExp(chkExp(span, env, e), chkTy(span, env, ty))
                (* end case *))
          and chkExps (span, env, es) = List.map (fn e => chkExp(span, env, e)) es
        (* pattern matching rules *)
          and chkCases (span, env, cases) = let
                fun chk _ (PT.MarkMatch{span, tree}) =
                      BT.MarkMatch{span=span, tree=chk span tree}
                  | chk span (PT.CaseMatch(p, e)) = let
                      val (p', bvs) = chkPat (span, env, p)
                      val bvs' = chkForDups (bvs, "variable", "in pattern")
                      val env' = Env.varsFromList (env, bvs')
                      val e' = chkExp (span, env', e)
                      in
                        BT.CaseMatch(p', e')
                      end
                in
                  List.map (chk span) cases
                end
        (* check a pattern; this returns the new pattern and a list of the (atom, id)
         * pairs for the binding occurrences in the pattern (in left-to-right order
         * of occurrence).
         *)
          and chkPat (span, env, pat) = let
                fun chk (span, pat, bvs) = (case pat
                       of PT.MarkPat{span, tree} => let
                            val (p', bvs') = chk (span, tree, bvs)
                            in
                              (BT.MarkPat{span=span, tree=p'}, bvs')
                            end
                        | PT.ConPat(qid, p) => let
                            val (p', bvs') = chk (span, p, bvs)
                            in
                              case chkQId (span, env, qid)
                               of SOME(SOME(path', strEnv), id) => (case Env.findConId'(strEnv, id)
                                     of SOME id' => (BT.ConAppPat((path', id'), p'), bvs')
                                      | NONE => (
                                          unbound' (span, "constructor", qid);
                                          (BT.ErrorPat, bvs'))
                                    (* end case *))
                                | SOME(NONE, id) => (case Env.findConId(env, id)
                                     of SOME id' => (BT.ConAppPat(([], id'), p'), bvs')
                                      | NONE => (
                                          unbound (span, "constructor", id);
                                          (BT.ErrorPat, bvs'))
                                    (* end case *))
                                | NONE => (BT.ErrorPat, bvs')
                              (* end case *)
                            end
                        | PT.ConsPat(p1, p2) => let
                            val (p2', bvs') = chk (span, p2, bvs)
                            val (p1', bvs') = chk (span, p1, bvs')
                            in
                              (BT.ConsPat(p1', p2'), bvs')
                            end
                        | PT.TuplePat ps => let
                            val (ps', bvs') = chkPats (span, ps, bvs)
                            in
                              (BT.TuplePat ps', bvs')
                            end
                        | PT.ListPat ps => let
                            val (ps', bvs') = chkPats (span, ps, bvs)
                            in
                              (BT.ListPat ps', bvs')
                            end
                        | PT.WildPat => (BT.WildPat, bvs)
                        | PT.IdPat qid => (case chkQId (span, env, qid)
                             of SOME(SOME(path', strEnv), id) => (case Env.findConId'(strEnv, id)
                                   of SOME id' => (BT.ConPat(path', id'), bvs)
                                    | NONE => (
                                        unbound' (span, "constructor", qid);
                                        (BT.ErrorPat, bvs))
                                  (* end case *))
                              | SOME(NONE, id) => (case Env.findConId(env, id)
                                   of SOME id' => (BT.ConPat([], id'), bvs)
                                    | NONE => let (* binding occurrence of variable *)
                                        val id' = BT.VarId.new(id, spanToLoc span)
                                        in
                                          (BT.VarPat id', (span, id, id')::bvs)
                                        end
                                  (* end case *))
                              | NONE => (BT.ErrorPat, bvs)
                            (* end case *))
                        | PT.AsPat(p1, p2) => let
                            val (p1', bvs) = chk (span, p1, bvs)
                            val (p2', bvs) = chk (span, p2, bvs)
                            in
                              (BT.AsPat(p1', p2'), bvs)
                            end
                        | PT.ConstPat lit => (BT.ConstPat lit, bvs)
                        | PT.ConstraintPat(p, ty) => let
                            val (p', bvs') = chk (span, p, bvs)
                            val ty' = chkTy (span, env, ty)
                            in
                              (BT.ConstraintPat(p', ty'), bvs')
                            end
                      (* end case *))
                and chkPats (span, ps, bvs) = let
                      fun chkOne (p, (ps', bvs')) = let
                            val (p', bvs') = chk (span, p, bvs')
                            in
                              (p' :: ps', bvs')
                            end
                      in
                        List.foldr chkOne ([], bvs) ps
                      end
                in
                  chk (span, pat, [])
                end
        (* get the initial binding environment *)
          val env0 = Env.new()
        (* process the compilation unit *)
          val (dcls', env') = let
                fun chk (dcl, (dcls', env)) = let
                      val (dcl', env') = chkDecl(span, env, dcl)
                      in
                        (dcl' :: dcls', env')
                      end
                val (dcls', env') = List.foldl chk ([], env0) tree
                in
                  (List.rev dcls', env')
                end
          in
            {span = span, tree = dcls'}
          end (* check *)

  end
