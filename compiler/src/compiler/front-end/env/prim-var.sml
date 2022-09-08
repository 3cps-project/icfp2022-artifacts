(* prim-var.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Predefined variables for the builtin operators
 *)

structure PrimVar : sig

  (* array operations *)
    val array0          : Var.t
    val array_alloc     : Var.t
    val array_length    : Var.t
    val array_sub       : Var.t
    val array_update    : Var.t

  (* character operations *)
    val char_lt         : Var.t
    val char_lte        : Var.t
    val char_gte        : Var.t
    val char_gt         : Var.t
    val char_ord        : Var.t

  (* integer operations *)
    val int_add         : Var.t
    val int_sub         : Var.t
    val int_mul         : Var.t
    val int_div         : Var.t
    val int_mod         : Var.t
    val int_neg         : Var.t
    val int_lt          : Var.t
    val int_lte         : Var.t
    val int_gte         : Var.t
    val int_gt          : Var.t

  (* word operations *)
    val word_add	: Var.t
    val word_sub	: Var.t
    val word_mul	: Var.t
    val word_div	: Var.t
    val word_mod	: Var.t
    val word_neg	: Var.t
    val word_lt		: Var.t
    val word_lte	: Var.t
    val word_gte	: Var.t
    val word_gt		: Var.t
    val word_andb_fn	: Var.t
    val word_fromInt_fn	: Var.t
    val word_lshift_fn	: Var.t
    val word_orb_fn	: Var.t
    val word_notb_fn	: Var.t
    val word_rshift_fn	: Var.t
    val word_rshiftl_fn	: Var.t
    val word_toInt_fn	: Var.t
    val word_toIntX_fn	: Var.t
    val word_xorb_fn	: Var.t

  (* real operations *)
    val real_add        : Var.t
    val real_sub        : Var.t
    val real_mul        : Var.t
    val real_div        : Var.t
    val real_neg        : Var.t
    val real_lt         : Var.t
    val real_lte        : Var.t
    val real_gte        : Var.t
    val real_gt         : Var.t

  (* string operations *)
    val string_lt       : Var.t
    val string_lte      : Var.t
    val string_gte      : Var.t
    val string_gt       : Var.t
    val string_size     : Var.t
    val string_sub      : Var.t
    val string_str      : Var.t
    val string_implode  : Var.t
    val string_append   : Var.t

  (* ref operations *)
    val ref_ref         : Var.t
    val ref_assign      : Var.t
    val ref_deref       : Var.t

  (* polymorphic equality *)
    val poly_eq : Var.t
    val poly_neq        : Var.t

  (* conversions *)
    val cvt_floor       : Var.t
    val cvt_real        : Var.t

  (* I/O functions *)
    val io_print        : Var.t

  (* Math functions *)
    val math_acos       : Var.t
    val math_asin       : Var.t
    val math_atan       : Var.t
    val math_atan2      : Var.t
    val math_cos        : Var.t
    val math_exp        : Var.t
    val math_ln         : Var.t
    val math_pow        : Var.t
    val math_sin        : Var.t
    val math_sqrt       : Var.t
    val math_tan        : Var.t

  end = struct

    structure BB = BasisBinds
    structure Ty = Types

    val --> = Ty.FunTy
    fun ** (t1, t2) = Ty.TupleTy[t1, t2]
    infix 9 **
    infixr 8 -->

  (* basis types *)
    val unitTy = PrimTy.unitTy
    val arrayTy = PrimTy.arrayTy
    val charTy = PrimTy.charTy
    val boolTy = PrimTy.boolTy
    val intTy = PrimTy.intTy
    val realTy = PrimTy.realTy
    val refTy = PrimTy.refTy
    val stringTy = PrimTy.stringTy
    val wordTy = PrimTy.wordTy
    val listTy = PrimTy.listTy

    fun forall mkTy = let
          val tv = TyVar.new' "'a"
          in
            Ty.TyScheme([tv], mkTy(Ty.VarTy tv))
          end
    fun monoVar (name, ty) = Var.new(name, ty)
    fun polyVar (name, mkTy) = Var.newPoly(name, forall mkTy)
    fun binOp (name, ty) = monoVar(name, ty ** ty --> ty)
    fun unOp (name, ty) = monoVar(name, ty --> ty)
    fun cmpOp (name, ty) = monoVar(name, ty ** ty --> boolTy)
    fun eqOp name = let
          val tv = TyVar.newOfClass ("'a", true, Ty.Any)
          val ty = Ty.VarTy tv
          in
            Var.newPoly(name, Ty.TyScheme([tv], ty ** ty --> boolTy))
          end
    fun cvtOp (name, ty1, ty2) = monoVar(name, ty1 --> ty2)

  (* array operations *)
    val array0 = polyVar (BB.array0_fn, fn tv => unitTy --> arrayTy tv)
    val array_alloc = polyVar (BB.array_alloc_fn, fn tv => intTy ** tv --> arrayTy tv)
    val array_length = polyVar (BB.array_length_fn, fn tv => arrayTy tv --> intTy)
    val array_sub = polyVar (BB.array_sub_fn, fn tv => arrayTy tv ** intTy --> tv)
    val array_update = polyVar (BB.array_update_fn, fn tv =>
          Ty.TupleTy[arrayTy tv, intTy,  tv] --> unitTy)

  (* character operations *)
    val char_lt         = cmpOp (BB.lt_op, charTy)
    val char_lte        = cmpOp (BB.lte_op, charTy)
    val char_gte        = cmpOp (BB.gte_op, charTy)
    val char_gt         = cmpOp (BB.gt_op, charTy)
    val char_ord        = cvtOp (BB.ord_fn, charTy, intTy)

  (* integer operations *)
    val int_add         = binOp (BB.plus_op, intTy)
    val int_sub         = binOp (BB.minus_op, intTy)
    val int_mul         = binOp (BB.times_op, intTy)
    val int_div         = binOp (BB.div_op, intTy)
    val int_mod         = binOp (BB.mod_op, intTy)
    val int_neg         = unOp (BB.neg_op, intTy)
    val int_lt          = cmpOp (BB.lt_op, intTy)
    val int_lte         = cmpOp (BB.lte_op, intTy)
    val int_gte         = cmpOp (BB.gte_op, intTy)
    val int_gt          = cmpOp (BB.gt_op, intTy)

  (* word operations *)
    val word_add        = binOp (BB.plus_op, wordTy)
    val word_sub        = binOp (BB.minus_op, wordTy)
    val word_mul        = binOp (BB.times_op, wordTy)
    val word_div        = binOp (BB.div_op, wordTy)
    val word_mod        = binOp (BB.mod_op, wordTy)
    val word_neg        = unOp (BB.neg_op, wordTy)
    val word_lt         = cmpOp (BB.lt_op, wordTy)
    val word_lte        = cmpOp (BB.lte_op, wordTy)
    val word_gte        = cmpOp (BB.gte_op, wordTy)
    val word_gt         = cmpOp (BB.gt_op, wordTy)
    val word_andb_fn	= binOp (BB.word_andb_fn, wordTy)
    val word_fromInt_fn	= cvtOp (BB.word_fromInt_fn, intTy, wordTy)
    val word_lshift_fn	= binOp (BB.word_andb_fn, wordTy)
    val word_orb_fn	= binOp (BB.word_andb_fn, wordTy)
    val word_notb_fn	= unOp (BB.word_notb_fn, wordTy)
    val word_rshift_fn	= binOp (BB.word_andb_fn, wordTy)
    val word_rshiftl_fn	= binOp (BB.word_andb_fn, wordTy)
    val word_toInt_fn	= cvtOp (BB.word_toInt_fn, wordTy, intTy)
    val word_toIntX_fn	= cvtOp (BB.word_toIntX_fn, wordTy, intTy)
    val word_xorb_fn	= binOp (BB.word_andb_fn, wordTy)

  (* real operations *)
    val real_add        = binOp (BB.plus_op, realTy)
    val real_sub        = binOp (BB.minus_op, realTy)
    val real_mul        = binOp (BB.times_op, realTy)
    val real_div        = binOp (BB.fdiv_op, realTy)
    val real_neg        = unOp (BB.neg_op, realTy)
    val real_lt         = cmpOp (BB.lt_op, realTy)
    val real_lte        = cmpOp (BB.lte_op, realTy)
    val real_gte        = cmpOp (BB.gte_op, realTy)
    val real_gt         = cmpOp (BB.gt_op, realTy)

  (* string operations *)
    val string_lt       = cmpOp (BB.lt_op, stringTy)
    val string_lte      = cmpOp (BB.lte_op, stringTy)
    val string_gte      = cmpOp (BB.gte_op, stringTy)
    val string_gt       = cmpOp (BB.gt_op, stringTy)
    val string_size     = monoVar (BB.size_fn, stringTy --> intTy)
    val string_sub      = monoVar (BB.sub_fn, stringTy ** intTy --> charTy)
    val string_append   = binOp (BB.hat_op, stringTy)
    val string_str      = monoVar (BB.str_fn, charTy --> stringTy)
    val string_implode  = monoVar (BB.implode_fn, listTy charTy --> stringTy)

  (* ref operations *)
    val ref_ref         = polyVar(BB.ref_fn, fn tv => tv --> refTy tv)
    val ref_assign      = polyVar(BB.assign_op, fn tv => refTy tv ** tv --> unitTy)
    val ref_deref       = polyVar(BB.deref_op, fn tv => refTy tv --> tv)

  (* polymorphic equality *)
    val poly_eq         = eqOp BB.eq_op
    val poly_neq        = eqOp BB.neq_op

  (* conversions *)
    val cvt_floor       = cvtOp (BB.floor_fn, realTy, intTy)
    val cvt_real        = cvtOp (BB.real_fn, intTy, realTy)

  (* I/O *)
    val io_print        = monoVar(BB.print_fn, stringTy --> unitTy)

  (* Math functions *)
    val math_acos       = monoVar(BB.acos_fn, realTy --> realTy)
    val math_asin       = monoVar(BB.asin_fn, realTy --> realTy)
    val math_atan       = monoVar(BB.atan_fn, realTy --> realTy)
    val math_atan2      = monoVar(BB.atan2_fn, realTy ** realTy --> realTy)
    val math_cos        = monoVar(BB.cos_fn, realTy --> realTy)
    val math_exp        = monoVar(BB.exp_fn, realTy --> realTy)
    val math_ln         = monoVar(BB.ln_fn, realTy --> realTy)
    val math_pow        = monoVar(BB.pow_fn, realTy ** realTy --> realTy)
    val math_sin        = monoVar(BB.sin_fn, realTy --> realTy)
    val math_sqrt       = monoVar(BB.sqrt_fn, realTy --> realTy)
    val math_tan        = monoVar(BB.tan_fn, realTy --> realTy)

  end
