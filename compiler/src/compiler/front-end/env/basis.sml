(* basis.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * This is a placeholder for importing the basis environment.
 *)

structure Basis : sig

    val env0 : {
            tcMap : EnvRep.ty_def BindTree.TycId.Map.map,
            cMap : Types.dcon BindTree.ConId.Map.map,
            vMap : EnvRep.val_bind BindTree.VarId.Map.map
          }

  (* is a type in a type class? Note that this function raises `Fail` for the
   * `Eq` class.  Use the
   * for those abstract types that support equality and false otherwise.
   *)
    val isClass : Types.ty * Types.ty_class -> bool

  end = struct

    structure BB = BasisBinds
    structure BT = BindTree
    structure TycMap = BT.TycId.Map
    structure ConMap = BT.ConId.Map
    structure VarMap = BT.VarId.Map
    structure Ty = Types

    datatype ty_def = datatype EnvRep.ty_def
    datatype val_bind = datatype EnvRep.val_bind

  (* overloaded operators *)
    local
      structure P = PrimVar
      val --> = Ty.FunTy
      fun ** (t1, t2) = Ty.TupleTy[t1, t2]
      infix 9 **
      infixr 8 -->
      fun forall cls mkTy = let
            val tv = TyVar.newOfClass ("'a", false, cls)
            in
              Ty.TyScheme([tv], mkTy(Types.VarTy tv))
            end
      fun binTS () = forall Ty.Num (fn tv => tv ** tv --> tv)
      fun unTS () = forall Ty.Num (fn tv => tv --> tv)
      fun cmpTS () = forall Ty.Order (fn tv => tv ** tv --> PrimTy.boolTy)
    in
    val ovld_add =      Overload(binTS(), [P.int_add, P.word_add, P.real_add])
    val ovld_sub =      Overload(binTS(), [P.int_sub, P.word_sub, P.real_sub])
    val ovld_mul =      Overload(binTS(), [P.int_mul, P.word_mul, P.real_mul])
    val ovld_neg =      Overload(unTS(), [P.int_neg, P.word_neg, P.real_neg])
    val ovld_lt =       Overload(cmpTS(), [P.char_lt, P.int_lt, P.word_lt, P.real_lt, P.string_lt])
    val ovld_lte =      Overload(cmpTS(), [P.char_lte, P.int_lte, P.word_lte, P.real_lte, P.string_lte])
    val ovld_gte =      Overload(cmpTS(), [P.char_gte, P.int_gte, P.word_gte, P.real_gte, P.string_gte])
    val ovld_gt =       Overload(cmpTS(), [P.char_gt, P.int_gt, P.word_gt, P.real_gt, P.string_gt])
    end (* local *)

    fun mapFromList insert empty xs =
          List.foldl (fn ((x, x'), m) => insert(m, x, x')) empty xs

  (* the basis environment *)
    val env0 = let
        (* the predefined type environment *)
          val tcMap = mapFromList TycMap.insert TycMap.empty [
                  (BB.array_ty,         TyCon PrimTy.arrayTyc),
                  (BB.bool_ty,          TyCon PrimTy.boolTyc),
                  (BB.char_ty,          TyCon PrimTy.charTyc),
                  (BB.exn_ty,           TyCon PrimTy.exnTyc),
                  (BB.int_ty,           TyCon PrimTy.intTyc),
                  (BB.list_ty,          TyCon PrimTy.listTyc),
                  (BB.option_ty,        TyCon PrimTy.optionTyc),
                  (BB.real_ty,          TyCon PrimTy.realTyc),
                  (BB.string_ty,        TyCon PrimTy.stringTyc),
                  (BB.ref_ty,           TyCon PrimTy.refTyc),
                  (BB.unit_ty,          TyCon PrimTy.unitTyc),
                  (BB.word_ty,          TyCon PrimTy.wordTyc)
                ]
        (* the predefined constructor environment *)
          val cMap = mapFromList ConMap.insert ConMap.empty [
                (* predefine data constructors *)
                  (BB.boolTrue,         PrimTy.boolTrue),
                  (BB.boolFalse,        PrimTy.boolFalse),
                  (BB.listNil,          PrimTy.listNil),
                  (BB.listCons,         PrimTy.listCons),
                  (BB.optionNONE,       PrimTy.optionNONE),
                  (BB.optionSOME,       PrimTy.optionSOME),
                (* predefined exception constructors *)
                  (BB.exnBind,          PrimExn.exnBind),
                  (BB.exnChr,           PrimExn.exnChr),
                  (BB.exnDiv,           PrimExn.exnDiv),
                  (BB.exnDomain,        PrimExn.exnDomain),
                  (BB.exnFail,          PrimExn.exnFail),
                  (BB.exnMatch,         PrimExn.exnMatch),
                  (BB.exnOverflow,      PrimExn.exnOverflow),
                  (BB.exnSize,          PrimExn.exnSize),
                  (BB.exnSubscript,     PrimExn.exnSubscript)
                ]
        (* the predefined variable environment *)
          val vMap = mapFromList VarMap.insert VarMap.empty [
                (* operators *)
                  (BB.eq_op,            Var PrimVar.poly_eq),
                  (BB.neq_op,           Var PrimVar.poly_neq),
                  (BB.lte_op,           ovld_lte),
                  (BB.lt_op,            ovld_lt),
                  (BB.gte_op,           ovld_gte),
                  (BB.gt_op,            ovld_gt),
                  (BB.hat_op,           Var PrimVar.string_append),
                  (BB.plus_op,          ovld_add),
                  (BB.minus_op,         ovld_sub),
                  (BB.times_op,         ovld_mul),
                  (BB.div_op,           Var PrimVar.int_div),
                  (BB.mod_op,           Var PrimVar.int_mod),
                  (BB.fdiv_op,          Var PrimVar.real_div),
                  (BB.assign_op,        Var PrimVar.ref_assign),
                  (BB.neg_op,           ovld_neg),
                (* reference operations *)
                  (BB.deref_op,         Var PrimVar.ref_deref),
                  (BB.ref_fn,           Var PrimVar.ref_ref),
                (* array operations *)
                  (BB.array0_fn,        Var PrimVar.array0),
                  (BB.array_alloc_fn,   Var PrimVar.array_alloc),
                  (BB.array_length_fn,  Var PrimVar.array_length),
                  (BB.array_sub_fn,     Var PrimVar.array_sub),
                  (BB.array_update_fn,  Var PrimVar.array_update),
                (* character operations *)
                  (BB.ord_fn,           Var PrimVar.char_ord),
                (* string operations *)
                  (BB.size_fn,          Var PrimVar.string_size),
                  (BB.sub_fn,           Var PrimVar.string_sub),
                  (BB.str_fn,           Var PrimVar.string_str),
                  (BB.implode_fn,       Var PrimVar.string_implode),
                (* word operations *)
                  (BB.word_andb_fn,     Var PrimVar.word_andb_fn),
                  (BB.word_fromInt_fn,  Var PrimVar.word_fromInt_fn),
                  (BB.word_lshift_fn,   Var PrimVar.word_lshift_fn),
                  (BB.word_orb_fn,      Var PrimVar.word_orb_fn),
                  (BB.word_notb_fn,     Var PrimVar.word_notb_fn),
                  (BB.word_rshift_fn,   Var PrimVar.word_rshift_fn),
                  (BB.word_rshiftl_fn,  Var PrimVar.word_rshiftl_fn),
                  (BB.word_toInt_fn,    Var PrimVar.word_toInt_fn),
                  (BB.word_toIntX_fn,   Var PrimVar.word_toIntX_fn),
                  (BB.word_xorb_fn,     Var PrimVar.word_xorb_fn),
                (* conversions *)
                  (BB.real_fn,          Var PrimVar.cvt_real),
                  (BB.floor_fn,         Var PrimVar.cvt_floor),
                (* predefined I/O operations *)
                  (BB.print_fn,         Var PrimVar.io_print),
                (* predefined Math functions *)
                  (BB.acos_fn,          Var PrimVar.math_acos),
                  (BB.asin_fn,          Var PrimVar.math_asin),
                  (BB.atan_fn,          Var PrimVar.math_atan),
                  (BB.atan2_fn,         Var PrimVar.math_atan2),
                  (BB.cos_fn,           Var PrimVar.math_cos),
                  (BB.exp_fn,           Var PrimVar.math_exp),
                  (BB.ln_fn,            Var PrimVar.math_ln),
                  (BB.pow_fn,           Var PrimVar.math_pow),
                  (BB.sin_fn,           Var PrimVar.math_sin),
                  (BB.sqrt_fn,          Var PrimVar.math_sqrt),
                  (BB.tan_fn,           Var PrimVar.math_tan)
                ]
          in
            { tcMap = tcMap, cMap = cMap, vMap = vMap }
          end

    local
      val intCls = [PrimTy.intTyc]
      val wordCls = [PrimTy.wordTyc]
      val realCls = [PrimTy.realTyc]
      val numCls = intCls @ wordCls @ realCls
      val orderCls = PrimTy.charTyc :: PrimTy.stringTyc :: numCls
      fun inList tyc tycs = List.exists (fn tyc' => TyCon.same (tyc, tyc')) tycs
    in
    fun isClass (_, Ty.Any) = true
      | isClass (Ty.ErrorTy, _) = true
      | isClass (Ty.ConTy(_, tyc), Ty.Int) = inList tyc intCls
      | isClass (Ty.ConTy(_, tyc), Ty.Word) = inList tyc wordCls
      | isClass (Ty.ConTy(_, tyc), Ty.Real) = inList tyc realCls
      | isClass (Ty.ConTy(_, tyc), Ty.Num) = inList tyc numCls
      | isClass (Ty.ConTy(_, tyc), Ty.Order) = inList tyc orderCls
      | isClass _ = false
    end

  end
