(* llvm-func.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *)

structure LLVMFunc : sig

    type t

  (* `new mod (retTy, name, params)` creates a new function in the module `mod`.
   * The return type of the function is given by `retTy`.  Note that this operation
   * creates a new global variable that names the function.
   *)
    val new : LLVMModule.t -> LLVMType.t * string * LLVMReg.t list -> t

    val nameOf : t -> LLVMGlobal.t

    val paramsOf : t -> LLVMReg.t list

  (* get the entry block of the function *)
    val entryOf : t -> LLVMBlock.t

  (* create a new non-entry block in the function *)
    val newBlock : t * string -> LLVMBlock.t

  end = struct

    structure Rep = LLVMRep

    datatype t = datatype Rep.func

    fun newBlk lab = Rep.Blk{
            name = LLVMLabel.new lab,
            phis = ref[],
            body = ref[],
            closed = ref false
          }

    fun nameOf (Func{name, ...}) = name

    fun paramsOf (Func{params, ...}) = params

    fun entryOf (Func{entry, ...}) = entry

    fun newBlock (Func{body, ...}, lab) = let
          val blk = newBlk lab
          in
            body := blk :: !body;
            blk
          end

    fun new (Rep.Module{funs, ...}) (retTy, name, params) = let
          val ty = LLVMType.FuncTy(retTy, List.map LLVMReg.typeOf params)
          val func = Rep.Func {
                  name = LLVMGlobal.new(name, ty),
                  params = params,
                  entry = newBlk "entry",
                  body = ref[]
                }
          in
            funs := func :: !funs;
            func
          end

  end
