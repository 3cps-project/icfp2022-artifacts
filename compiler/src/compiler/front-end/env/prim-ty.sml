(* prim-ty.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Builtin types.
 *)

structure PrimTy : sig

    val unitTyc : Types.tycon
    val unitTy  : Types.ty

  (* Booleans *)
    val boolTyc   : Types.tycon
    val boolTy    : Types.ty
    val boolTrue  : Types.dcon
    val boolFalse : Types.dcon

  (* Lists *)
    val listTyc  : Types.tycon
    val listTy   : Types.ty -> Types.ty
    val listNil  : Types.dcon
    val listCons : Types.dcon

  (* Options *)
    val optionTyc       : Types.tycon
    val optionTy        : Types.ty -> Types.ty
    val optionNONE      : Types.dcon
    val optionSOME      : Types.dcon

  (* exceptions *)
    val exnTyc : Types.tycon
    val exnTy  : Types.ty

  (* builtin abstract types *)
    val arrayTyc  : Types.tycon
    val arrayTy   : Types.ty -> Types.ty
    val charTyc   : Types.tycon
    val charTy    : Types.ty
    val intTyc    : Types.tycon
    val intTy     : Types.ty
    val realTyc   : Types.tycon
    val realTy    : Types.ty
    val refTyc    : Types.tycon
    val refTy     : Types.ty -> Types.ty
    val stringTyc : Types.tycon
    val stringTy  : Types.ty
    val wordTyc   : Types.tycon
    val wordTy    : Types.ty

  end = struct

    structure BB = BasisBinds

    val boolTyc = TyCon.newDataTyc (BB.bool_ty, [])
    val boolTrue = DataCon.new boolTyc (BB.boolTrue, NONE)
    val boolFalse = DataCon.new boolTyc (BB.boolFalse, NONE)

    local
      val tv = TyVar.new' "'a"
      val tv' = AST.VarTy tv
    in
    val listTyc = TyCon.newDataTyc (BB.list_ty, [tv])
    val listNil = DataCon.new listTyc (BB.listNil, NONE)
    val listCons =
          DataCon.new listTyc
            (BB.listCons, SOME(AST.TupleTy[tv', AST.ConTy([tv'], listTyc)]))
    end (* local *)

  (* Options *)
    local
      val tv = TyVar.new' "'a"
      val tv' = AST.VarTy tv
    in
    val optionTyc = TyCon.newDataTyc (BB.option_ty, [tv])
    val optionNONE = DataCon.new optionTyc (BB.optionNONE, NONE)
    val optionSOME = DataCon.new optionTyc (BB.optionSOME, SOME tv')
    end (* local *)

  (* the `unit` type is defined earlier to avoid circularity *)
    val unitTyc = TyCon.unitTyc

    local
      fun newTyc (id, span, eq) = TyCon.newAbsTyc{
              id = id, arity = 0, span = span, eq = eq, mut = false
            }
    in
    val charTyc = newTyc (BB.char_ty, 255, true)
    val intTyc = newTyc (BB.int_ty, ~1, true)
    val realTyc = newTyc (BB.real_ty, ~1, false)
    val stringTyc = newTyc (BB.string_ty, ~1, false)
    val wordTyc = newTyc (BB.word_ty, ~1, true)
    end

  (* arrays and references are mutable *)
    val arrayTyc = TyCon.newAbsTyc {
            id = BB.array_ty, arity = 1, span = 0,
            eq = true, mut = true
          }
    val refTyc = TyCon.newAbsTyc {
            id = BB.ref_ty, arity = 1, span = 0,
            eq = true, mut = true
          }

    val exnTyc = Exn.tyc

  (* predefined types *)
    fun arrayTy ty = AST.ConTy([ty], arrayTyc)
    val boolTy = AST.ConTy([], boolTyc)
    val charTy = AST.ConTy([], charTyc)
    val intTy = AST.ConTy([], intTyc)
    val realTy = AST.ConTy([], realTyc)
    val stringTy = AST.ConTy([], stringTyc)
    val unitTy = AST.ConTy([], unitTyc)
    val wordTy = AST.ConTy([], wordTyc)
    fun listTy ty = AST.ConTy([ty], listTyc)
    fun optionTy ty = AST.ConTy([ty], optionTyc)
    val exnTy = AST.ConTy([], exnTyc)
    fun refTy ty = AST.ConTy([ty], refTyc)

  end
