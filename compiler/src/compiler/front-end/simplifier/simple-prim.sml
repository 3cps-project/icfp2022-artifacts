(* simple-prim.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Definitions of primitive types, data constructors, and
 * exceptions for the Simple AST representation.  These are
 * implemented by converting from the AST representations.
 *)

structure SimplePrim : sig

    val unitTyc : SimpleTypes.tycon
    val unitTy : SimpleTypes.ty

  (* Booleans *)
    val boolTyc   : SimpleTypes.tycon
    val boolTrue  : SimpleTypes.dcon
    val boolFalse : SimpleTypes.dcon

  (* references *)
    val refTyc    : SimpleTypes.tycon

  (* exceptions *)
    val exnTyc : SimpleTypes.tycon

  (* builtin abstract types *)
    val arrayTyc  : SimpleTypes.tycon
    val charTyc   : SimpleTypes.tycon
    val intTyc    : SimpleTypes.tycon
    val realTyc   : SimpleTypes.tycon
    val stringTyc : SimpleTypes.tycon
(* FIXME: we probably should just merge words and ints at this point
 * in the translation, since the operators capture the semantics of
 * the types.
 *)
    val wordTyc   : SimpleTypes.tycon

  (* builtin exceptions *)
    val exnBind      : SimpleTypes.dcon
    val exnChr       : SimpleTypes.dcon
    val exnDiv       : SimpleTypes.dcon
    val exnDomain    : SimpleTypes.dcon
    val exnFail      : SimpleTypes.dcon
    val exnMatch     : SimpleTypes.dcon
    val exnOverflow  : SimpleTypes.dcon
    val exnSize      : SimpleTypes.dcon
    val exnSubscript : SimpleTypes.dcon

  end = struct

    structure PTy = PrimTy
    structure PExn = PrimExn

    val unitTyc = SimplifyTy.cvtTyc PrimTy.unitTyc
    val unitTy = SimpleTypes.ConTy([], unitTyc)

  (* Booleans *)
    val boolTyc   = SimplifyTy.cvtTyc PrimTy.boolTyc
    val boolTrue  = SimplifyTy.cvtDCon PrimTy.boolTrue
    val boolFalse = SimplifyTy.cvtDCon PrimTy.boolFalse

  (* exceptions *)
    val exnTyc = SimpleExn.tyc

  (* builtin abstract types *)
    val arrayTyc  = SimplifyTy.cvtTyc PrimTy.arrayTyc
    val charTyc   = SimplifyTy.cvtTyc PrimTy.charTyc
    val intTyc    = SimplifyTy.cvtTyc PrimTy.intTyc
    val realTyc   = SimplifyTy.cvtTyc PrimTy.realTyc
    val refTyc    = SimplifyTy.cvtTyc PrimTy.refTyc
    val stringTyc = SimplifyTy.cvtTyc PrimTy.stringTyc
    val wordTyc   = SimplifyTy.cvtTyc PrimTy.wordTyc

  (* builtin exceptions *)
    val exnBind      = SimplifyTy.cvtDCon PrimExn.exnBind
    val exnChr       = SimplifyTy.cvtDCon PrimExn.exnChr
    val exnDiv       = SimplifyTy.cvtDCon PrimExn.exnDiv
    val exnDomain    = SimplifyTy.cvtDCon PrimExn.exnDomain
    val exnFail      = SimplifyTy.cvtDCon PrimExn.exnFail
    val exnMatch     = SimplifyTy.cvtDCon PrimExn.exnMatch
    val exnOverflow  = SimplifyTy.cvtDCon PrimExn.exnOverflow
    val exnSize      = SimplifyTy.cvtDCon PrimExn.exnSize
    val exnSubscript = SimplifyTy.cvtDCon PrimExn.exnSubscript

  end
