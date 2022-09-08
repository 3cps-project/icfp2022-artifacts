(* contract-types.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Eliminate unecessary polymorphism.
 *
 * TODO: This optimization could be made more effective by doing partial
 * specialization (instead of all or nothing).
 *)

structure ContractTypes : sig

    val transform : Census.t * SimpleAST.comp_unit -> SimpleAST.comp_unit

  end = struct

    structure S = SimpleAST
    structure Ty = SimpleTypes
    structure TyVar = SimpleTyVar
    structure TVMap = TyVar.Map
    structure TVSet = TyVar.Set
    structure Var = SimpleVar
    structure VMap = SimpleVar.Map
    structure VTbl = SimpleVar.Tbl
    structure TyU = SimpleTypeUtil
    structure ST = Stats

  (* debug messages *)
    fun say msg = Log.msg("[S-CTY] " :: msg)
    fun ctlSay msg = if Controls.get Ctl.debugSimpleOpt
          then say msg
          else ()
    val v2s = Var.toString
    fun tvs2s tvs = concat["<", String.concatWithMap "," TyVar.toString tvs, ">"]
    fun tys2s tys = concat["<", String.concatWithMap "," TyU.toString tys, ">"]

  (* counters for optimizations *)
    val cntrs = ST.Group.newWithPri SimpleOptStats.group ("contract-types", [3])
    local
      val newCntr = ST.Counter.new cntrs
    in
    val cntPolyVar      = newCntr "poly-var"    (* # of polymorphic variables *)
    val cntPolyFun      = newCntr "poly-fun"    (* # of polymorphic functions *)
    val cntMonoVar      = newCntr "mono-var"    (* # of specialized variables *)
    val cntMonoFun      = newCntr "mono-fun"    (* # of specialized functions *)
    val cntRenameVar    = newCntr "rename"      (* # of variables with new types *)
    end (* local *)

  (***** Analysis *****)

  (* property for monomorphc instantiation of variables *)
    type ty_args = (TyVar.t * Ty.ty) list
    local
      val {setFn : Var.t * ty_args -> unit, peekFn, ...} =
            Var.newProp (fn _ => raise Fail "ty_args")
    in
    fun recordTyArgs (x, tys) = let
          val tyScm as Ty.TyScheme(tvs, _) = Var.typeOf x
          in
            ctlSay ["type args: ", v2s x, tys2s tys, "\n"];
            setFn (x, ListPair.zip (tvs, tys))
          end
    val findTyArgs = peekFn
    end (* local *)

    datatype ty_info
      = POLY of TVSet.set       (* polymorphic binding with the set of available
                                 * bound type variables at the variables binding.
                                 *)
      | INST of Ty.ty list      (* proposed instantiation of polymorphic binding *)

    val addTVs = TVSet.addList

  (* check if a type is well formed w.r.t. a set of bound type variables;
   * i.e., any type variable in the type is in the set.
   *)
    fun isWellFormed btvs = let
          fun chk (Ty.VarTy tv) = TVSet.member(btvs, tv)
            | chk (Ty.ConTy(tys, _)) = List.all chk tys
            | chk (Ty.FunTy(ty1, ty2)) = chk ty1 andalso chk ty2
            | chk (Ty.TupleTy tys) = List.all chk tys
          in
            chk
          end

  (* the analysis pass computes a mapping from polymorphic variables
   * to type arguments that can be used to specialize the variables.
   *)
    fun analysis copyInfo exp = let
          val tyInfo = VTbl.mkTable (32, Fail "tyInfo")
          val insertVar = VTbl.insert tyInfo
          val removeVar = VTbl.remove tyInfo
          val findVar = VTbl.find tyInfo
          fun anal (btvs, S.E(_, e)) = (case e
                 of S.E_Let(x, e1, e2) => (anal(btvs, e1); anal(btvs, e2))
                  | S.E_LetPoly(x, tvs, e1, e2) => (
                      ST.Counter.tick cntPolyVar;
                    (* insert candidate for specialization into table *)
                      insertVar (x, POLY btvs);
                    (* analyse the variable's scope *)
                      anal (btvs, e2);
                    (* check for specialization *)
                      case findVar x
                       of SOME(INST tys) => (
                            ST.Counter.tick cntMonoVar;
                            ctlSay [
                                "`letpoly ", v2s x, tvs2s tvs,
                                " = ...` can be specialized to ", tys2s tys, "\n"
                              ];
                            recordTyArgs (x, tys))
                        | _ => () (* no specialization *)
                      (* end case *);
                      anal (addTVs(btvs, tvs), e1))
                  | S.E_Fun(fbs, e) => let
                      fun analFB (S.FB(f, _, _, body)) = (case Var.typeOf f
                             of Ty.TyScheme([], _) => anal (btvs, body)
                              | Ty.TyScheme(tvs, _) => (
                                  ST.Counter.tick cntPolyFun;
                                  insertVar (f, POLY btvs);
                                  anal (addTVs(btvs, tvs), body))
                            (* end case *))
                      fun chkFB (S.FB(f, _, _, _)) = (case findVar f
                             of SOME(INST tys) => (
                                  ctlSay [
                                      "function ", v2s f, " can be specialized to ",
                                      tys2s tys, "\n"
                                    ];
                                  ST.Counter.tick cntMonoFun;
                                  recordTyArgs (f, tys))
                              | _ => ()
                            (* end case *))
                      in
                        List.app analFB fbs;
                        anal (btvs, e);
                        List.app chkFB fbs
                      end
                  | S.E_Apply(_, [], atm) => analAtom atm
                  | S.E_Apply(f, tys, atm) => (analPolyVar (f, tys); analAtom atm)
                  | S.E_DConApp(_, _, atm) => analAtom atm
                  | S.E_Prim(_, _, atms) => List.app analAtom atms
                  | S.E_Tuple atms => List.app analAtom atms
                  | S.E_Select(_, x, []) => ()
                  | S.E_Select(_, x, tys) => analPolyVar (x, tys)
                  | S.E_If(_, atms, e1, e2, _) => (
                      List.app analAtom atms;
                      anal (btvs, e1);
                      anal (btvs, e2))
                  | S.E_Case(atm, cases, _) => (
                      analAtom atm;
                      List.app (fn (S.RULE(_, _, e)) => anal (btvs, e)) cases)
                  | S.E_Handle(e1, _, e2, _) => (
                      anal (btvs, e1);
                      anal (btvs, e2))
                  | S.E_Raise _ => ()
                  | S.E_Atom atm => analAtom atm
                (* end case *))
          and analAtom (S.A_Var(x, [])) = ()
            | analAtom (S.A_Var(x, tys)) = analPolyVar (x, tys)
            | analAtom _ = ()
          and analPolyVar (x, tys) = (case findVar x
                 of SOME(POLY btvs) => let
                    (* if this is a recursive instance of `x`, then the `tys` should
                     * just be the type parameters of `x` wrapped in `VarTy`;
                     * otherwise we check that `tys` are well formed w.r.t. `btvs`.
                     *)
                      val Ty.TyScheme(tvs, _) = Var.typeOf x
                      fun isTyParam (tv, Ty.VarTy tv') = TyVar.same(tv, tv')
                        | isTyParam _ = false
                      in
                        if ListPair.all isTyParam (tvs, tys)
                          then () (* recursive instance, so we do nothing *)
                        else if List.all (isWellFormed btvs) tys
                          then insertVar (x, INST tys)
                          else ignore(removeVar x)
                      end
                  | SOME(INST tys') => (* check that `tys` and `tys'` are the same *)
                      if ListPair.allEq TyU.same (tys, tys')
                        then ()
                        else ignore(removeVar x) (* inconsistent instantiations *)
                  | NONE => ()
                (* end case *))
          in
            anal (TVSet.empty, exp);
            (ST.Counter.value cntMonoVar + ST.Counter.value cntMonoFun) > 0
          end

  (***** Transformation *****)

  (* property for monomorphc instantiation of variables *)
    local
      val {setFn : Var.t * Var.t -> unit, peekFn, ...} =
            Var.newProp (fn _ => raise Fail "mono_var")
    in
    fun monoVar copyInfo (x, tyBinds) = let
          val tvMap = List.foldl TVMap.insert' TVMap.empty tyBinds
          val tyScm as Ty.TyScheme(_, ty) = Var.typeOf x
          val x' = Var.new(Var.nameOf x, TyU.applySubst tvMap ty)
          in
            ctlSay [
                "type specialize: ", v2s x, " : ", TyU.schemeToString tyScm,
                " ==> ", v2s x', " : ", TyU.toString(Var.monoTypeOf x'), "\n"
              ];
            copyInfo (x, x');
            setFn (x, x');
            x'
          end
    val findMono = peekFn
    end (* local *)

    datatype env = E of {
        tvMap : TyU.tv_env,     (* instantiation map for type variables *)
        vMap : Var.t VMap.map   (* renaming environment for variables *)
      }

    val emptyEnv = E{tvMap = TVMap.empty, vMap = VMap.empty}

  (* rename a variable, if necessary *)
    fun rnVar (E{vMap, ...}, x) = (case VMap.find(vMap, x)
           of SOME x' => x'
            | NONE => x
          (* end case *))

    fun rnTy (E{tvMap, ...}) = TyU.applySubst tvMap
    fun rnTys (_, []) = []
      | rnTys (env, tys) = List.map (rnTy env) tys

  (* freshen a variable if its type changes *)
    fun fresh copyInfo (env as E{tvMap, vMap}, x) = let
          val tyScm as Ty.TyScheme(tvs, ty) = Var.typeOf x
          in
            if TyU.domainOccursInTy (tvMap, ty)
              then let (* need to rename `x` with a specialized version *)
                val tyScm' = Ty.TyScheme(tvs, TyU.applySubst tvMap ty)
                val x' = Var.newPoly(Var.nameOf x, tyScm')
                val vMap' = VMap.insert (vMap, x, x')
                in
                  ST.Counter.tick cntRenameVar;
                  copyInfo (x, x');
                  ctlSay [
                      "replace ", Var.toString x, " : ", TyU.schemeToString tyScm,
                      " with ", Var.toString x', " : ",  TyU.schemeToString tyScm',
                      "\n"
                    ];
                  (x', E{tvMap = tvMap, vMap = vMap'})
                end
              else (x, env)
          end

    fun insertVar (E{tvMap, vMap}, x, x') =
          E{tvMap = tvMap, vMap = VMap.insert(vMap, x, x')}

    fun addTyBinds (E{tvMap, vMap}, tyBinds) = E{
            tvMap = List.foldl TVMap.insert' tvMap tyBinds,
            vMap = vMap
          }

    fun specializeTyBinds (E{tvMap, ...}, tyBinds) =
          List.map (fn (tv, ty) => (tv, TyU.applySubst tvMap ty)) tyBinds

    fun transform (info, compUnit as S.CU(S.FB(mainF, mainLab, mainParam, mainBody))) = let
          val copyInfo = Census.copy info
          val monoVar = monoVar copyInfo
        (* freshen a variable if its type changes *)
          val fresh = fresh copyInfo
        (* freshen a pattern *)
          fun freshPat (env, S.P_DConApp(dc, tys, x)) = let
                val (x, env) = fresh (env, x)
                in
                  (S.P_DConApp(dc, rnTys(env, tys), x), env)
                end
            | freshPat (env, S.P_Var x) = let
                val (x, env) = fresh (env, x)
                in
                  (S.P_Var x, env)
                end
            | freshPat (env, S.P_DCon(dc, tys)) =
                (S.P_DCon(dc, rnTys(env, tys)), env)
            | freshPat (env, p) = (p, env)
          fun xform (env, S.E(lab, e)) = S.E(lab, xformRep(env, e))
          and xformRep (env, e) = (case e
                 of S.E_Let(x, e1, e2) => let
                      val (x, env) = fresh (env, x)
                      in
                        S.E_Let(x, xform(env, e1), xform(env, e2))
                      end
                  | S.E_LetPoly(x, tvs, e1, e2) => (case findTyArgs x
                       of SOME tyBinds => let
                          (* specialize the type bindings *)
                            val tyBinds = specializeTyBinds (env, tyBinds)
                          (* get the monomorphic version of x *)
                            val x' = monoVar (x, tyBinds)
                            val env1 = addTyBinds (env, tyBinds)
                            val env2 = insertVar (env, x, x')
                            in
                              S.E_Let(x', xform(env1, e1), xform(env2, e2))
                            end
                        | NONE => let
                            val (x, env) = fresh (env, x)
                            in
                              S.E_LetPoly(x, tvs, xform(env, e1), xform(env, e2))
                            end
                      (* end case *))
                  | S.E_Fun(fbs, e) => let
                      fun xformFB (S.FB(f, lab, x, e), (fbs, recEnv)) = (
                            case findTyArgs f
                             of SOME tyBinds => let
                                (* specialize the type bindings *)
                                  val tyBinds = specializeTyBinds (env, tyBinds)
                                (* get the monomorphic version of x *)
                                  val f' = monoVar (f, tyBinds)
                                  val env' = addTyBinds (env, tyBinds)
                                  val (x, env') = fresh (env', x)
                                  in
                                    (S.FB(f', lab, x, xform(env', e))::fbs, recEnv)
                                  end
                              | NONE => let
                                  val (f, recEnv) = fresh (recEnv, f)
                                  val (x, env) = fresh (recEnv, x)
                                  in
                                    (S.FB(f, lab, x, xform(env, e))::fbs, recEnv)
                                  end
                            (* end case *))
                      val (fbs, env) = List.foldr xformFB ([], env) fbs
                      in
                        S.E_Fun(fbs, xform(env, e))
                      end
                  | S.E_Apply(f, tys, atm) => let
                      val (f, tys) = xformVar (env, f, tys)
                      in
                        S.E_Apply(f, tys, xformAtm env atm)
                      end
                  | S.E_DConApp(dc, tys, atm) =>
                      S.E_DConApp(dc, rnTys(env, tys), xformAtm env atm)
                  | S.E_Prim(p, tys, atms) =>
                      S.E_Prim(p, rnTys(env, tys), List.map (xformAtm env) atms)
                  | S.E_Tuple atms => S.E_Tuple(List.map (xformAtm env) atms)
                  | S.E_Select(i, x, tys) => let
                      val (x, tys) = xformVar (env, x, tys)
                      in
                        S.E_Select(i, x, tys)
                      end
                  | S.E_If(p, atms, e1, e2, ty) =>
                      S.E_If(p, List.map (xformAtm env) atms,
                        xform(env, e1), xform(env, e2),
                        rnTy env ty)
                  | S.E_Case(atm, rules, ty) => let
                      fun xformRule (S.RULE(lab, pat, e)) = let
                            val (pat, env) = freshPat (env, pat)
                            in
                              S.RULE(lab, pat, xform(env, e))
                            end
                      in
                        S.E_Case(
                          xformAtm env atm,
                          List.map xformRule rules,
                          rnTy env ty)
                      end
                  | S.E_Handle(e1, x, e2, ty) =>
                      S.E_Handle(xform(env, e1), x, xform(env, e2), rnTy env ty)
                  | S.E_Raise(loc, atm, ty) =>
                      S.E_Raise(loc, xformAtm env atm, rnTy env ty)
                  | S.E_Atom atm => S.E_Atom(xformAtm env atm)
                (* end case *))
          and xformAtm env (S.A_Var(x, tys)) = S.A_Var(xformVar (env, x, tys))
            | xformAtm env (S.A_DCon(dc, tys)) = S.A_DCon(dc, rnTys(env, tys))
            | xformAtm _ atm = atm
          and xformVar (env, x, tys) = (case findMono x
                 of SOME x' => (x', [])
                  | NONE => (rnVar(env, x), rnTys(env, tys))
                (* end case *))
          in
            if analysis (Census.copy info) mainBody
              then (
                ctlSay ["***** Contract Types ******\n"];
                S.CU(S.FB(mainF, mainLab, mainParam, xform (emptyEnv, mainBody))))
              else compUnit
          end

  end
