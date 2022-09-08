(* convert-ty.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Convert AST types to CPS types.
 *)

structure ConvertTy : sig

    type tv_env = CPSTyVar.t SimpleTyVar.Map.map

    val envFromTyParams : SimpleTypes.tyvar list -> tv_env * CPSTyVar.t list

    val cvtTy : tv_env -> SimpleTypes.ty -> CPSTypes.t

    val tycOf : SimpleTypes.tycon -> CPSTypes.tycon

    val dconOf : tv_env * SimpleTypes.dcon -> CPSTypes.dcon

  end = struct

    structure Ty = SimpleTypes
    structure TyCon = SimpleTyCon
    structure TyVar = SimpleTyVar
    structure TVMap = TyVar.Map
    structure DataCon = SimpleDataCon
    structure CTy = CPSTypes
    structure PTy = CPSPrimTy

    type tv_env = CPSTyVar.t TyVar.Map.map

  (* a property that maps AST type constructors to their CPS equivalents *)
    val {setFn=setTycOf : Ty.tycon * CTy.tycon -> unit, peekFn=peekTycOf, ...} =
          TyCon.newProp(fn tyc => raise Fail "getTycOf")

  (* a property that maps AST data constructors to their CPS equivalents *)
    val {setFn=setDConOf : Ty.dcon * CTy.dcon -> unit, peekFn=peekDConOf, ...} =
          DataCon.newProp(fn tyc => raise Fail "getDCOf")

    fun envFromTyParams params = let
          fun cvtParam (tv, (env, tvs')) = let
                val tv' = CPSTyVar.new()
                in
                  (TVMap.insert(env, tv, tv'), tv'::tvs')
                end
          in
            List.foldr cvtParam (TVMap.empty, []) params
          end

  (* convert builtin abstract type costructors *)
    local
      val primTycMap = [
              (SimplePrim.arrayTyc, PTy.arrayTyc),
              (SimplePrim.unitTyc, PTy.unitTyc),
              (SimplePrim.charTyc, PTy.charTyc),
              (SimplePrim.exnTyc, PTy.exnTyc),
              (SimplePrim.intTyc, PTy.intTyc),
              (SimplePrim.realTyc, PTy.realTyc),
              (SimplePrim.stringTyc, PTy.stringTyc),
              (SimplePrim.refTyc, PTy.refTyc)
            ]
    in
    fun cvtPrimTyc tyc = (
          case List.find (fn (tyc', _) => TyCon.same(tyc, tyc')) primTycMap
           of SOME(_, cpsTyc) => cpsTyc
            | NONE => raise Fail(concat[
                  "unknown abstract tycon '", TyCon.toString tyc, "'"
                ])
          (* end case *))
    end (* local *)

    fun cvtTy env ty = let
          fun cvt ty = (case ty
                 of Ty.VarTy tv => (case TVMap.find(env, tv)
                       of SOME tv' => CTy.VarTy tv'
                        | NONE => raise Fail("unbound type variable " ^ TyVar.toString tv)
                      (* end case *))
                  | Ty.ConTy(tyArgs, tyc) => CTy.ConTy(List.map cvt tyArgs, tycOf tyc)
                  | Ty.FunTy(domTy, rngTy) =>
                      CTy.FunTy([cvt domTy], [CTy.ContTy[cvt rngTy], PTy.exhCTy])
                  | Ty.TupleTy tys => CTy.TupleTy(List.map cvt tys)
                (* end case *))
          in
            cvt ty
(*DEBUG*)handle ex => (
print(concat["cvtTy - (", SimpleTypeUtil.toString ty, ")\n"]);
raise ex)
          end

    and tycOf tyc = (case peekTycOf tyc
           of SOME tyc' => tyc'
            | NONE => (case tyc
                 of Ty.Tyc{def=Ty.AbsTyc, ...} => let
                      val tyc' = cvtPrimTyc tyc
                      in
                        setTycOf (tyc, tyc');
                        tyc'
                      end
                  | Ty.Tyc{name, def=Ty.DataTyc{cons, ...}, params, ...} => let
                      val (env, params') = envFromTyParams params
                      val cvtArgTy = Option.map (cvtTy env)
                      fun doCons (Ty.DCon{name, argTy, ...}) = (name, cvtArgTy argTy)
                      val {dt=tyc', setCons} = CPSTyCon.newDataTyc(name, params')
                    (* need to set the AST->CPS mapping before converting the constructor
                     * argument types to avoid infinite loops!
                     *)
                      val _ = setTycOf (tyc, tyc')
                    (* set the constructors for the CPS type *)
                      val cons' = setCons (List.map doCons (!cons))
                      in
                      (* establish the mapping from AST data constructors to CPS constructors *)
                        ListPair.map setDConOf (!cons, cons');
                        tyc'
                      end
                (* end case *))
          (* end case *))

  (* convert builtin exceptions *)
    local
      val exnMap = [
              (SimplePrim.exnBind, CPSExn.exnBind),
              (SimplePrim.exnDiv, CPSExn.exnDiv),
              (SimplePrim.exnDomain, CPSExn.exnDomain),
              (SimplePrim.exnFail, CPSExn.exnFail),
              (SimplePrim.exnMatch, CPSExn.exnMatch),
              (SimplePrim.exnOverflow, CPSExn.exnOverflow),
              (SimplePrim.exnSize, CPSExn.exnSize),
              (SimplePrim.exnSubscript, CPSExn.exnSubscript)
            ]
    in
    fun findPrimExn dc = List.find (fn (dc', _) => DataCon.same(dc, dc')) exnMap
    end (* local *)

    fun dconOf (tvEnv, dc as Ty.DCon{name=dcName, owner, ...}) = (case peekDConOf dc
           of SOME dc' => dc'
            | NONE => if TyCon.same(owner, SimplePrim.exnTyc)
                then let
                  val dc' = (case findPrimExn dc  (* exception constructor *)
                         of SOME(_, cpsExn) => cpsExn
                          | NONE => (case DataCon.argTypeOf dc
                               of SOME(Ty.TyScheme(_, ty)) =>
                                    CPSExn.new(dcName, SOME(cvtTy tvEnv ty))
                                | NONE => CPSExn.new(dcName, NONE)
                              (* end case *))
                        (* end case *))
                  in
                    setDConOf(dc, dc'); dc'
                  end
                else let
                (* need to convert the owner first *)
                  val tyc' = tycOf owner
                  in
                    case peekDConOf dc
                     of SOME dc' => dc'
                      | NONE => raise Fail("unknown dcon " ^ DataCon.toString dc)
                    (* end case *)
                  end
          (* end case *))

  end
