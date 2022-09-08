(* llvm-block.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *)

structure LLVMBlock : sig

    type t

    type var = LLVMVar.t

  (* exception raised if an attempt is made to add instructions to a closed block *)
    exception Closed

    val labelOf : t -> LLVMLabel.t

  (* is a block closed?  I.e., has a terminating control-flow instruction been added to it? *)
    val isClosed : t -> bool

  (* emit a phi instruction; this must come at the beginning of the block! *)
    val emitPhi : t * LLVMReg.t * (LLVMVar.t * LLVMLabel.t) list -> unit

  (* emit a comment (for debugging) *)
    val emitComment : t * string -> unit

    val emitCast : t * LLVMType.t * var -> var  (* typecast variable to specified type *)

  (* function calls.  Note that for calls that cannot trigger GC, the live list can
   * be empty.
   *)
    val emitCall : t * {
            func : var,                         (* the function being called *)
            args : var list,                    (* the function arguments *)
            live : var list                     (* the variables that are live after the call.
                                                 * NOTE: these should _not_ include the result
                                                 * of the call!
                                                 *)
          } -> {
            ret : var option,                   (* the result register (NONE for void) *)
            live : var list                     (* the renamed live list *)
          }

  (* integer arithmetic *)
    val emitAdd : t * var * var -> var          (* signed integer addition *)
    val emitSub : t * var * var -> var          (* signed integer subtraction *)
    val emitMul : t * var * var -> var          (* signed integer multiplication *)
    val emitDiv : t * var * var -> var          (* signed integer division *)
    val emitAShftR : t * var * var -> var       (* arithmetic right shift *)
    val emitShftL : t * var * var -> var        (* left shift *)
    val emitXor : t * var * var -> var          (* exclusive or *)
    val emitXorBit : t * var * var -> var       (* 1-bit exclusive or; used for negation *)

  (* comparisons *)
    val emitEqu : t * var * var -> var          (* equality comparison *)
    val emitNEq : t * var * var -> var          (* inequality comparison *)
    val emitLte : t * var * var -> var          (* less-than-or-equal comparison *)
    val emitLt  : t * var * var -> var          (* less-than comparison *)
    val emitGt  : t * var * var -> var          (* greater-than comparison *)
    val emitGte : t * var * var -> var          (* greater-than-or-equal comparison *)

  (* address arithmetic *)
    val emitAddr : t * var * var -> var         (* computes base+offset (where offset will
                                                 * be scaled by the pointer size.
                                                 *)

  (* memory operations *)
    val emitLd  : t * LLVMType.t * var -> var   (* emit a load instruction that loads a
                                                 * value of the specified type (a cast may be
                                                 * inserted).
                                                 *)
    val emitSt  : t * {                         (* memory store operation *)
            addr : var,                         (* specifies destination address *)
            value : var                         (* specifies value to store *)
          } -> unit

  (* control flow instructions; these close off the block *)
    val emitReturn : t * var option -> unit
    val emitGoto   : t * LLVMLabel.t -> unit
    val emitCondBr : t * var * LLVMLabel.t * LLVMLabel.t -> unit

  end = struct

    structure Rep = LLVMRep
    structure Ty = LLVMType
    structure Var = LLVMVar

    datatype t = datatype Rep.block
    datatype var = datatype Rep.var

  (* target for goto or conditional branch *)
    type target = {
        blk : t,                                (* target block *)
        args : var list                         (* ?? *)
      }

    exception Closed

  (* close off a block *)
    fun close (Blk{phis, body, closed, ...}) = (
          phis := List.rev (!phis);
          body := List.rev (!body);
          closed := true)

    fun labelOf (Blk{name, ...}) = name

    fun isClosed (Blk{closed, ...}) = !closed

    fun addInstr (Blk{body, closed=ref false, ...}, instr) = (body := instr :: !body)
      | addInstr _ = raise Closed

    val newReg = LLVMReg.new

  (* generic function for creating emitting that return results.  Arguments are
   *    ty      -- result type of operation
   *    rator   -- operation
   *    mk      -- function to process arguments
   *)
    fun emitInstr ty rator mk args = let
          val res = newReg ty
          val (blk, args) = mk args
          val instr = Rep.Instr{result = SOME res, rator = rator, args = args}
          in
            addInstr (blk, instr);
            Rep.VReg res
          end

    fun emitInstr' ty rator (blk, args) = let
          val res = newReg ty
          val instr = Rep.Instr{result = SOME res, rator = rator, args = args}
          in
            addInstr (blk, instr);
            Rep.VReg res
          end

    fun emitNoResI blk rator args = let
          val instr = Rep.Instr{result = NONE, rator = rator, args = args}
          in
            addInstr (blk, instr)
          end

    fun mkArgs1 (blk, a) = (blk, [a])
    fun mkArgs2 (blk, a, b) = (blk, [a, b])

  (* emit a phi instruction; this must come at the beginning of the block! *)
    fun emitPhi (Blk{phis, closed=ref false, ...}, lhs, rhs) =
          phis := Rep.Phi(lhs, rhs) :: !phis
      | emitPhi _ = raise Closed

    fun emitComment (blk, msg) = emitNoResI blk Rep.CommentOp [Rep.Comment msg]

    fun emitCast (blk, ty, var) = emitInstr' ty Rep.CastOp (blk, [var])

  (* integer arithmetic *)
    val emitAdd = emitInstr Ty.Int64Ty Rep.AddOp mkArgs2
    val emitSub = emitInstr Ty.Int64Ty Rep.SubOp mkArgs2
    val emitMul = emitInstr Ty.Int64Ty Rep.MulOp mkArgs2
    val emitDiv = emitInstr Ty.Int64Ty Rep.DivOp mkArgs2
    val emitAShftR = emitInstr Ty.Int64Ty Rep.AShftROp mkArgs2
    val emitShftL = emitInstr Ty.Int64Ty Rep.ShftLOp mkArgs2
    val emitXor = emitInstr Ty.Int64Ty Rep.XorOp mkArgs2

  (* single-bit xor; used to implement logical negation *)
    val emitXorBit = emitInstr Ty.Int1Ty Rep.XorOp mkArgs2

  (* integer comparisons *)
    val emitLte = emitInstr Ty.Int1Ty Rep.LteOp mkArgs2
    val emitLt  = emitInstr Ty.Int1Ty Rep.LtOp mkArgs2
    val emitGt  = emitInstr Ty.Int1Ty Rep.GtOp mkArgs2
    val emitGte = emitInstr Ty.Int1Ty Rep.GteOp mkArgs2

  (* equality tests *)
    local
    (* For equality tests, we might have pointer/int comparisons because of nil.
     * This function checks for that case and adds a cast if required.  We also
     * check for address-space type conflicts.
     *)
      fun castEqArgs (blk, a, b) = let
            val aTy = Var.typeOf a
            val bTy = Var.typeOf b
            in
              if Ty.same(aTy, bTy)
                then (blk, [a, b])
                else (case (aTy, bTy)
                   of (Ty.Int64Ty, _) => (blk, [a, emitCast(blk, Ty.Int64Ty, b)])
                    | (_, Ty.Int64Ty) => (blk, [emitCast(blk, Ty.Int64Ty, a), b])
                    | _ => raise Fail(concat[
                          "equality between ", Ty.toString aTy, " and ", Ty.toString bTy
                        ])
                  (* end case *))
            end
    in
    val emitEqu = emitInstr Ty.Int1Ty Rep.EquOp castEqArgs
    val emitNEq = emitInstr Ty.Int1Ty Rep.NEqOp castEqArgs
    end (* local *)

  (* memory operations *)
    fun emitLd (blk, ty, ptr) = let
          val SOME resTy = Ty.deref (Var.typeOf ptr)
          val res = emitInstr' resTy Rep.LoadOp (blk, [ptr])
          in
            if Ty.same(resTy, ty)
              then res
              else emitCast (blk, ty, res)
          end

  (* map a pointer to something as a pointer to baseTy *)
    fun rewrapPtrAs (ptr, baseTy) = (case ptr
           of Ty.PtrTy _ => Ty.PtrTy baseTy
            | Ty.GCPtrTy _ => Ty.GCPtrTy baseTy
            | ty => raise Fail(concat["rewrapPtrAs(", Ty.toString ty, ")"])
          (* end case *))

    fun emitSt (blk, {value, addr}) = let
          val addrTy = Var.typeOf addr
          val SOME pointeeTy = Ty.deref addrTy
          val valueTy = Var.typeOf value
          val addr = if Ty.same(valueTy, pointeeTy)
                then addr
                else emitCast (blk, rewrapPtrAs(addrTy, valueTy), addr)
          in
            emitNoResI blk Rep.StoreOp [value, addr]
          end

    fun emitAddr (blk, base, offset) = let
          val resTy = LLVMType.gepTy (Var.typeOf base, [offset])
          in
          (* NOTE that we're skipping the first offset. *)
            emitInstr' resTy Rep.GetElemPtrOp (blk, [base, offset])
          end

  (* See documentation about gc.statepoint for the details. *)
    fun emitCall (blk, {func, args, live}) = let
          val Ty.FuncTy(retT, paramTys) = Var.typeOf func
        (* add casts for arguments that are ints, where the expected type is a pointer *)
          val args = let
                fun addCast (x, ty as Ty.GCPtrTy _) = if Ty.same(Var.typeOf x, ty)
                      then x
                      else emitCast(blk, ty, x)
                (* also need casts when passing metadata of type [n x i64]* to sool_new, which expects i64* *)
                  | addCast (x, ty as Ty.PtrTy _) = (case Var.typeOf x
                      of Ty.PtrTy(Ty.ArrayTy _) => emitCast(blk, ty, x)
                       | _ => x
                     (* end case *))
                  | addCast (x, _) = x
                in
                  ListPair.map addCast (args, paramTys)
                end
          val tok = emitInstr' Rep.Token (Rep.CallOp live) (blk, func :: args)
          val ret = (case retT
                 of Ty.VoidTy => NONE
                  | _ => SOME(emitInstr' retT Rep.RetValOp (blk, [tok]))
                (* end case *))
          fun cvt (inputVar, (i, rest)) = (case Var.typeOf inputVar
                 of ty as Ty.GCPtrTy _ => let
                    (* for live variables that are garbage collected, we have to rename *)
                      val offset = Var.const(Ty.Int32Ty, Int.toLarge i)
                      val output = emitInstr' ty Rep.RelocOp (blk, [tok, offset, offset])
                      in
                        (i+1, output::rest)
                      end
                  | _ => (i, inputVar::rest)
                (* end case *))
          val startIdx = 5 + (List.length args) + 2 (* magic *)
          val (_, cvtd) = List.foldl cvt (startIdx, []) live
          in
            { ret = ret, live = List.rev cvtd }
          end

  (* terminators, which close the block *)

    fun emitReturn (blk, NONE) = (emitNoResI blk Rep.Return []; close blk)
      | emitReturn (blk, SOME var) = (emitNoResI blk Rep.Return [var]; close blk)

    fun emitGoto (blk, lab) = (
          emitNoResI blk Rep.Goto [Rep.Label lab];
          close blk)

    fun emitCondBr (blk, cond, trueLab, falseLab) = (
          emitNoResI blk Rep.CondBr [cond, Rep.Label trueLab, Rep.Label falseLab];
          close blk)

  end
