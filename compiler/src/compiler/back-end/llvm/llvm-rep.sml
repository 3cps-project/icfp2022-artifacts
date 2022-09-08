(* llvm-rep.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *
 * Internal representations of LLVM objects.
 *)

structure LLVMRep =
  struct

  (* simplified LLVM types *)
    datatype ty
      = VoidTy
      | Int1Ty                                  (* a 1 bit integer. for bools *)
      | Int32Ty                                 (* a 32 bit integer *)
      | Int64Ty                                 (* a 64 bit integer. for SooL ints *)
      | FuncTy of ty * ty list                  (* return type paired with argument types  *)
      | PtrTy of ty                             (* pointer *)
      | GCPtrTy of ty                           (* garbage collected pointer *)
      | ArrayTy of int * ty                     (* int = num elms *)
      | StructTy of ty list
      | Token
      | VarArg

    datatype global = Glob of {                 (* global names (e.g., function names) *)
          name : Atom.atom,                     (* variable name (including "@") *)
          ty : ty
        }

    datatype label = Lab of {
          name : string,                        (* *)
          id : Stamp.t                          (* *)
        }

    datatype reg = Reg of {
          name : string,                        (* register name; defaults to "" *)
          id : int,                             (* unique ID; generated in LLVReg *)
          ty : ty                               (* type *)
        }

    datatype var
      = VReg of reg                             (* LLVM local variable; the int is its unique ID *)
      | IConst of ty * IntInf.int               (* integer literal *)
      | Global of global
      | Label of label
      | Comment of string

(* QUESTION: what about string literals? *)
(* QUESTION: what about external functions? *)
    datatype module = Module of {
          globals : global_def list ref,        (* global definitions (other than functions) *)
          funs : func list ref                  (* *)
        }

    and global_def
      = ExternFn of global
      | ExternVar of global
      | Data of global * var list

    and func = Func of {
          name : global,                        (* the function's global name *)
          params : reg list,                    (* *)
          entry : block,                        (* entry block of function *)
          body : block list ref                 (* list of non-entry blocks *)
        }

    and block = Blk of {
          name : label,                         (* the block's label *)
          phis : phi list ref,                  (* phi nodes for block *)
          body : instr list ref,                (* instructions in the block; while the block
                                                 * is open, these are in reverse order.
                                                 *)
          closed : bool ref                     (* has the block been closed off by a terminator? *)
        }

    and phi = Phi of reg * (var * label) list   (* phi instruction *)

    and instr = Instr of {
          result : reg option,
          rator : operation,
          args : var list
        }

    and operation
      = CastOp                                  (* cast to a different type *)
      | CallOp of var list                      (* returns a token value.
                                                 * vars = pointers live during the call
                                                 *)
      | RetValOp                                (* retrieves the retval of a token *)
      | RelocOp                                 (* retrieves located livein from a token *)
    (* integer arithmetic. both args must be the same int type *)
      | AddOp                                   (* signed addition *)
      | SubOp                                   (* signed subtraction *)
      | MulOp                                   (* signed multiplication *)
      | DivOp                                   (* signed division *)
      | AShftROp                                (* arithmetic shift right *)
      | ShftLOp                                 (* shift left *)
      | XorOp                                   (* exclusive or *)
    (* comparisons. both args must be of same type. *)
      | EquOp                                   (* integer or pointer == *)
      | NEqOp                                   (* integer or pointer != *)
      | GteOp                                   (* integer or pointer >= *)
      | GtOp                                    (* integer or pointer > *)
      | LtOp                                    (* integer or pointer < *)
      | LteOp                                   (* integer or pointer <= *)
    (* memory/address operations *)
      | LoadOp                                  (* read from memory. [pointer] *)
      | StoreOp                                 (* write to memory. [pointer, value], no result *)
      | GetElemPtrOp                            (* getelementptr *)
    (* control-flow at end of block *)
      | Return                                  (* return. [] or [var] *)
      | Goto                                    (* unconditional branch. [label] *)
      | CondBr                                  (* conditional branch. [cond : i1, trueLabel, falseLabel] *)
    (* debugging *)
      | CommentOp                               (* prints a comment. [comment] *)

  end
