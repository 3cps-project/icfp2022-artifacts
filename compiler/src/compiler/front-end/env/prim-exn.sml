(* prim-exn.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Builtin exceptions.
 *)

structure PrimExn : sig

    val exnBind      : Types.dcon
    val exnChr       : Types.dcon
    val exnDiv       : Types.dcon
    val exnDomain    : Types.dcon
    val exnFail      : Types.dcon
    val exnMatch     : Types.dcon
    val exnOverflow  : Types.dcon
    val exnSize      : Types.dcon
    val exnSubscript : Types.dcon

  end = struct

    structure BB = BasisBinds

    val exnBind = Exn.new (BB.exnBind, NONE)
    val exnChr = Exn.new (BB.exnChr, NONE)
    val exnDiv = Exn.new (BB.exnDiv, NONE)
    val exnDomain = Exn.new (BB.exnDomain, NONE)
    val exnFail = Exn.new (BB.exnFail, SOME PrimTy.stringTy)
    val exnMatch = Exn.new (BB.exnMatch, NONE)
    val exnOverflow = Exn.new (BB.exnOverflow, NONE)
    val exnSize = Exn.new (BB.exnSize, NONE)
    val exnSubscript = Exn.new (BB.exnSubscript, NONE)

  end
