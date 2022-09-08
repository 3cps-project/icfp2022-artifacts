(* equality.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure Equality : sig

    datatype eq_test
      = PrimTest of PrimOp.test         (* equality/inequality on primitive types *)
      | EqFun of SimpleVar.t            (* synthesized equality  *)

  (* `eqTest (eq, ty)` get the equality/inequality test for the type `ty`.  The flag
   * `eq` is `true` for equality tests and `false` for inequality tests.  For primitive
   * types, the returned test will be as specifed by the `eq` flag, but synthesized
   * tests (i.e., `EqFun f`) are always equality tests.
   *)
    val eqTest : bool * SimpleTypes.ty -> eq_test

    val getEqTests : unit -> SimpleAST.lambda list

  end = struct

    structure STy = SimpleTypes
    structure S = SimpleAST
    structure SV = SimpleVar
    structure TyUtil = SimpleTypeUtil
    structure STyCon = SimpleTyCon
    structure SPrim = SimplePrim
    structure Tgt = Target

  (* hash table keyed by types *)
    structure Tbl = HashTableFn (
      struct
        type hash_key = STy.ty
        val hashVal = SimpleTypeUtil.alphaHash
        val sameKey = SimpleTypeUtil.alphaSame
      end)

    datatype eq_test
      = PrimTest of PrimOp.test         (* equality on primtive types *)
      | EqFun of SV.t                   (* synthesized equality  *)

    local
      fun iEq sz = PrimTest(PrimOp.ICmp(PrimOp.Test.IEq, sz))
      fun iNEq sz = PrimTest(PrimOp.ICmp(PrimOp.Test.INEq, sz))
    in
    val primEqMap = [
            (SPrim.arrayTyc,    PrimTest PrimOp.PtrEq,  PrimTest PrimOp.PtrNEq),
            (SPrim.charTyc,     iEq Tgt.charBits,       iNEq Tgt.charBits),
            (SPrim.intTyc,      iEq Tgt.intBits,        iNEq Tgt.intBits),
            (SPrim.stringTyc,   PrimTest PrimOp.SEq,    PrimTest PrimOp.SNEq),
            (SPrim.refTyc,      PrimTest PrimOp.PtrEq,  PrimTest PrimOp.PtrNEq),
            (SPrim.wordTyc,     iEq Tgt.intBits,        iNEq Tgt.intBits)
          ]
    end

    val boolTy = STy.ConTy([], SPrim.boolTyc)

  (* generate temporaty variables *)
    val eqTst = SV.newTmp "_eqTst"
    val fst = SV.newTmp "_fst"
    val snd = SV.newTmp "_snd"
    val pairArg = SV.newTmp "_pair"

    fun mkLet (name, ty, rhs, k) = let
          val x = SV.newTmp name ty
          in
            S.mkLet(x, rhs, k(S.A_Var(x, [])))
          end

  (* Boolean constant expressions.
   * Note that these need to be functions so that we generate
   * fresh labels for each occurrence.
   *)
    fun trueExp () = S.mkAtom(S.A_DCon(SPrim.boolTrue, []))
    fun falseExp () = S.mkAtom(S.A_DCon(SPrim.boolFalse, []))

  (* Boolean constant patterns *)
    val truePat = S.P_DCon(SPrim.boolTrue, [])
    val falsePat = S.P_DCon(SPrim.boolFalse, [])

  (* keep track of equality functions *)
    val eqFuns : S.lambda list ref = ref []
    val eqTbl : eq_test Tbl.hash_table = Tbl.mkTable(32, Fail "eqTbl")

  (* `eqTest (eq, ty)` get the equality/inequality test for the type `ty`.  The flag
   * `eq` is `true` for equality tests and `false` for inequality tests.
   *)
    fun eqTest (eq, ty) = (case ty
           of STy.ConTy(tyArgs, tyc as STy.Tyc{def=STy.AbsTyc, ...}) => (
                case List.find (fn (tyc', _, _) => STyCon.same(tyc, tyc')) primEqMap
                 of SOME(_, eqTst, neqTst) => if eq then eqTst else neqTst
                  | NONE => raise Fail(concat[
                        "equality not supported for '", TyUtil.toString ty, "'"
                      ])
                (* end case *))
(* FIXME: should synthesize an equality test for datatypes *)
            | STy.ConTy(tyArgs, tyc as STy.Tyc{def=STy.DataTyc _, ...}) => if eq
                then PrimTest PrimOp.PolyEq
                else PrimTest PrimOp.PolyNEq
            | STy.VarTy _ => if eq
                then PrimTest PrimOp.PolyEq
                else PrimTest PrimOp.PolyNEq
            | ty => (case Tbl.find eqTbl ty
                 of SOME eqTst => eqTst
                  | NONE => synthesizeEqTest ty
                (* end case *))
          (* end case *))

    and synthesizeEqTest ty = let
          val eqTst = eqTst (STy.FunTy(STy.TupleTy[ty, ty], boolTy))
        (* add name of equality test to hash table in case it is a recursive type *)
          val _ = Tbl.insert eqTbl (ty, EqFun eqTst)
          val pair = pairArg (STy.TupleTy[ty, ty])
          val fst = fst ty
          val snd = snd ty
          val body = (case ty
                 of STy.TupleTy tys => let
                      fun tstTys (i, [ty]) =
                            mkLet("_a", ty, S.mkSelect(i, fst, []), fn a =>
                            mkLet("_b", ty, S.mkSelect(i, snd, []), fn b => (
                              case eqTest (true, ty)
                               of PrimTest tst =>
                                    S.mkIf(tst, [a, b], trueExp(), falseExp(), boolTy)
                                | EqFun f =>
                                    mkLet("_pair", STy.TupleTy[ty, ty], S.mkTuple[a, b],
                                      fn pair => S.mkApply(f, [], pair))
                              (* end case *))))
                        | tstTys (i, ty::tys) =
                            mkLet("_a", ty, S.mkSelect(i, fst, []), fn a =>
                            mkLet("_b", ty, S.mkSelect(i, snd, []), fn b => (
                              case eqTest (true, ty)
                               of PrimTest tst =>
                                    S.mkIf(tst, [a, b], tstTys(i+1, tys), falseExp(), boolTy)
                                | EqFun f => mkLet("_pair", STy.TupleTy[ty, ty], S.mkTuple[a, b], fn pair =>
                                    mkLet("_res", boolTy, S.mkApply(f, [], pair), fn res =>
                                      S.mkCase(res, [
                                          S.mkRULE(truePat, tstTys(i+1, tys)),
(* TODO: it may be better to use a rule `_ => res` for the false case? *)
                                          S.mkRULE(falsePat, falseExp())
                                        ],
                                        boolTy)))
                              (* end case *))))
                      in
                        tstTys (1, tys)
                      end
                  | _ => raise Fail(concat["equality not supported for '", TyUtil.toString ty, "'"])
                (* end case *))
          val body = S.mkLet(fst, S.mkSelect(1, pair, []),
                S.mkLet(snd, S.mkSelect(2, pair, []),
                  body))
          in
            eqFuns := S.mkFB(eqTst, pair, body) :: !eqFuns;
            EqFun eqTst
          end

    fun getEqTests () = let
          val fns = List.rev (!eqFuns)
          in
            eqFuns := [];
            Tbl.clear eqTbl;
            fns
          end

  end
