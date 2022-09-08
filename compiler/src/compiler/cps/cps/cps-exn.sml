(* cps-exn.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSExn : sig

    val new : string * CPSTypes.t option -> CPSDataCon.t

  (* is this dcon an exception constructor? *)
    val isExn : CPSDataCon.t -> bool

  (* builtin exceptions *)
    val exnBind      : CPSDataCon.t
    val exnDiv       : CPSDataCon.t
    val exnDomain    : CPSDataCon.t
    val exnFail      : CPSDataCon.t
    val exnMatch     : CPSDataCon.t
    val exnOverflow  : CPSDataCon.t
    val exnSize      : CPSDataCon.t
    val exnSubscript : CPSDataCon.t

  end = struct

    structure Ty = CPSTypes

    fun new (name, ty) = Ty.DCon{
            stamp = Stamp.new(),
            name = name,
            owner = CPSPrimTy.exnTyc,
            argTy = ty,
            props = PropList.newHolder()
          }

    fun isExn (Ty.DCon{owner, ...}) = CPSTyCon.same(owner, CPSPrimTy.exnTyc)

    val exnBind = new("Bind", NONE)
    val exnDiv = new("Div", NONE)
    val exnDomain = new("Domain", NONE)
    val exnFail = new("Fail", SOME CPSPrimTy.stringTy)
    val exnMatch = new("Match", NONE)
    val exnOverflow = new("Overflow", NONE)
    val exnSize = new("Size", NONE)
    val exnSubscript = new("Subscript", NONE)

  end
