(* simplify-ty.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Support for converting from AST types to Simple AST types.
 *)

structure SimplifyTy : sig

    type tv_env = SimpleTyVar.t TyVar.Map.map

  (* convert a type constructor *)
    val cvtTyc : Types.tycon -> SimpleTypes.tycon

  (* convert an AST type to a Simple AST type *)
    val cvtTy : tv_env * Types.ty -> SimpleTypes.ty

  (* convert an AST type to a Simple AST type *)
    val cvtTys : tv_env * Types.ty list -> SimpleTypes.ty list

  (* convert an AST type scheme to a Simple AST scheme and return the scheme
   * and the environment augmented with the bound type variables.
   *)
    val cvtTyScheme : tv_env * Types.ty_scheme -> SimpleTypes.ty_scheme * tv_env

    val cvtDCon : Types.dcon -> SimpleTypes.dcon

  end = struct

    structure Ty = Types
    structure STy = SimpleTypes
    structure SDCon = SimpleDataCon
    structure TVMap = TyVar.Map

    type tv_env = SimpleTyVar.t TVMap.map

    fun cvtTyParams (tvMap, params) = let
          fun cvtParam (tv, (tvs', tvMap)) = let
                val tv' = SimpleTyVar.new()
                in
                  (tv'::tvs', TVMap.insert(tvMap, tv, tv'))
                end
          in
            List.foldr cvtParam ([], tvMap) params
          end

    fun envFromTyParams params = cvtTyParams (TVMap.empty, params)

    fun insert (tvMap, tv, tv') = TVMap.insert(tvMap, tv, tv')
    fun lookup (tvMap, tv) = (case TVMap.find(tvMap, tv)
           of SOME tv' => tv'
            | NONE => raise Fail("unknown type variable " ^ TyVar.toString tv)
          (* end case *))

  (* a property that maps AST type constructors to their Simple AST equivalents *)
    val {setFn=setTycOf : Ty.tycon * STy.tycon -> unit, peekFn=peekTycOf, ...} =
          TyCon.newProp(fn tyc => raise Fail "getTycOf")

  (* we need to establish the exception tycon mapping so that the primitive
   * exceptions get the right tycon.
   *)
    val _ = setTycOf (PrimTy.exnTyc, SimpleExn.tyc)

  (* a property that maps AST data constructors to their Simple AST equivalents *)
    val {setFn=setDConOf : Ty.dcon * STy.dcon -> unit, peekFn=peekDConOf, ...} =
          DataCon.newProp(fn tyc => raise Fail "getDCOf")

  (* function to sort AST data constructors into canonical order; we order
   * nullary constructors before constructor-functions and then by
   * lexical order.
   *)
    val sortDCons = let
          fun gt (dc1, dc2) = (case (DataCon.isNullary dc1, DataCon.isNullary dc2)
                 of (true, false) => true
                  | (false, true) => false
                  | _ => (case DataCon.lexCompare(dc1, dc2)
                       of GREATER => true
                        | _ => false
                      (* end case *))
                (* end case *))
          in
            ListMergeSort.sort gt
          end

    fun cvtTy (env, ty) = let
          fun cvt ty = (case (TypeUtil.prune ty)
                 of Ty.VarTy tv => STy.VarTy(lookup(env, tv))
                  | Ty.ConTy(tys, tyc) => STy.ConTy(List.map cvt tys, cvtTyc tyc)
                  | Ty.FunTy(ty1, ty2) => STy.FunTy(cvt ty1, cvt ty2)
                  | Ty.TupleTy tys => STy.TupleTy(List.map cvt tys)
                  | _ => raise Fail(concat["cvtTy (-, ", TypeUtil.toString ty, ")"])
                (* end case *))
          in
            cvt ty
          end

    and cvtTyc tyc = (case peekTycOf tyc
           of SOME tyc' => tyc'
            | NONE => (case tyc
                 of Ty.Tyc{name, params, def=Ty.AbsTyc _, ...} => let
                      val (params', _) = envFromTyParams params
                      val tyc' = SimpleTyCon.newAbsTyc (name, params')
                      in
                        setTycOf (tyc, tyc');
                        tyc'
                      end
                  | Ty.Tyc{name, def=Ty.DataTyc{cons, ...}, params, ...} => let
                      val (params', env) = envFromTyParams params
                      val cvtArgTy = Option.map (fn ty => cvtTy(env, ty))
                      val tyc' = SimpleTyCon.newDataTyc(name, params')
                      val newCons = SDCon.new tyc'
                      fun doCons (dc as Ty.DCon{name, argTy, ...}) = let
                            val dc' = newCons (name, cvtArgTy argTy)
                            in
                              setDConOf (dc, dc');
                              dc'
                            end
                    (* need to set the AST->Simple mapping before converting the constructor
                     * argument types to avoid infinite loops!
                     *)
                      val _ = setTycOf (tyc, tyc')
                    (* put the AST constructors into canonical order *)
                      val sortedCons = sortDCons (!cons)
                    (* set the constructors for the Simple AST type *)
                      val cons' = List.map doCons sortedCons
                      in
                        tyc'
                      end
                (* end case *))
          (* end case *))

    fun cvtTys (env, tys) = List.map (fn ty => cvtTy(env, ty)) tys

    fun cvtTyScheme (env, Ty.TyScheme([], ty)) =
          (STy.TyScheme([], cvtTy(env, ty)), env)
      | cvtTyScheme (env, Ty.TyScheme(tvs, ty)) = let
          val (tvs', env') = cvtTyParams (env, tvs)
          in
            (STy.TyScheme(tvs', cvtTy(env', ty)), env')
          end

    fun cvtDCon (dc as Ty.DCon{name=dcName, owner, ...}) = (case peekDConOf dc
           of SOME dc' => dc'
            | NONE => if TyCon.same(owner, PrimTy.exnTyc)
                then let
                  val dc' = (case DataCon.argTypeOf dc
                         of SOME(Ty.TyScheme([], ty)) =>
                              SimpleExn.new(dcName, SOME(cvtTy (TVMap.empty, ty)))
                          | NONE => SimpleExn.new(dcName, NONE)
                        (* end case *))
                  in
                    setDConOf(dc, dc'); dc'
                  end
                else let
                (* need to convert the owner first *)
                  val tyc' = cvtTyc owner
                  in
                    case peekDConOf dc
                     of SOME dc' => dc'
                      | NONE => raise Fail("unknown dcon " ^ DataCon.toString dc)
                    (* end case *)
                  end
          (* end case *))

  end
