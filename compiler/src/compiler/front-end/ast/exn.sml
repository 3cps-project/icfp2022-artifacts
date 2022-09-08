(* exn.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Support for the `exn` type.
 *)

structure Exn : sig

  (* the exception type *)
    val tyc : Types.tycon

  (* create a new exception constructor. *)
    val new : (BindTree.conid * AST.ty option) -> AST.dcon

  (* is this dcon an exception constructor? *)
    val isExn : AST.dcon -> bool

  end = struct

  (* we use an abstract type constructor to represent the exception type *)
    val tyc = TyCon.newAbsTyc {
            id = BasisBinds.exn_ty,
            arity = 0, span = ~1,
            eq = false, mut = false
          }

    fun new (id, argTy) = Types.DCon{
            stamp = Stamp.new(),
            name = BindTree.ConId.nameOf id,
            owner = tyc,
            argTy = argTy,
            props = PropList.newHolder()
          }

    fun isExn (Types.DCon{owner, ...}) = TyCon.same(owner, tyc)

  end
