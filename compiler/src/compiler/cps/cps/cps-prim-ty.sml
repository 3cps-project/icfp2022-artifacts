(* cps-prim-ty.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Primitive CPS types
 *)

structure CPSPrimTy : sig

    val unitTyc : CPSTyCon.t
    val arrayTyc : CPSTyCon.t
    val charTyc : CPSTyCon.t
    val exnTyc : CPSTyCon.t
    val intTyc : CPSTyCon.t
    val wordTyc : CPSTyCon.t
    val realTyc : CPSTyCon.t
    val stringTyc : CPSTyCon.t
    val refTyc : CPSTyCon.t

    val unitTy : CPSTypes.t
    val arrayTy : CPSTypes.t -> CPSTypes.t
    val charTy : CPSTypes.t
    val exnTy : CPSTypes.t
    val intTy : CPSTypes.t
    val wordTy : CPSTypes.t
    val realTy : CPSTypes.t
    val stringTy : CPSTypes.t
    val refTy : CPSTypes.t -> CPSTypes.t

  (* the type of an exception-handler continuation *)
    val exhCTy : CPSTypes.ct

  end = struct

    structure Ty = CPSTypes
    structure Tyc = CPSTyCon

    val unitTyc = Tyc.newAbsTyc("unit", 0)
    val arrayTyc = Tyc.newAbsTyc("array", 1)
    val charTyc = Tyc.newAbsTyc("char", 0)
    val exnTyc = Tyc.newAbsTyc("exn", 0)
    val intTyc = Tyc.newAbsTyc("int", 0)
    val wordTyc = Tyc.newAbsTyc("word", 0)      (* QUESTION: maybe words are just ints in CPS? *)
    val realTyc = Tyc.newAbsTyc("real", 0)
    val stringTyc = Tyc.newAbsTyc("string", 0)
    val refTyc = Tyc.newAbsTyc("ref", 1)

    val unitTy = Ty.ConTy([], unitTyc)
    fun arrayTy ty = Ty.ConTy([ty], arrayTyc)
    val charTy = Ty.ConTy([], charTyc)
    val exnTy = Ty.ConTy([], exnTyc)
    val intTy = Ty.ConTy([], intTyc)
    val wordTy = Ty.ConTy([], wordTyc)
    val realTy = Ty.ConTy([], realTyc)
    val stringTy = Ty.ConTy([], stringTyc)
    fun refTy ty = Ty.ConTy([ty], refTyc)

    val exhCTy = Ty.ContTy[exnTy]

  end
