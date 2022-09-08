(* llvm-type.sml
 *
 * COPYRIGHT (c) 2016 Kavon Farvardin and John Reppy
 * All rights reserved.
 *
 * Sample code
 * CMSC 22600
 * Autumn 2016
 * University of Chicago
 *)

structure LLVMType : sig

    type addr_space

    datatype t
      = VoidTy
      | Int1Ty                                  (* a 1 bit integer. for bools *)
      | Int32Ty                                 (* a 32 bit integer *)
      | Int64Ty                                 (* a 64 bit integer. for SooL ints *)
      | FuncTy of t * t list                    (* return type paired with argument types  *)
      | PtrTy of t                              (* pointer *)
      | GCPtrTy of t                            (* garbage collected pointer *)
      | ArrayTy of int * t                      (* int = num elms *)
      | StructTy of t list
      | Token
      | VarArg

    val heap : addr_space

    val toString : t -> string

    val deref : t -> t option

    val gepTy : t * LLVMRep.var list -> t

  (* are two types equal? *)
    val same : t * t -> bool

  end = struct

    structure Rep = LLVMRep

    type addr_space = int

    datatype t = datatype Rep.ty

    val heap : addr_space = 1

    fun toString ty = (case ty
           of VoidTy => "void"
            | Int1Ty => "i1"
            | Int32Ty => "i32"
            | Int64Ty => "i64"
            | FuncTy(retTy, paramTys) => String.concat [
                  toString retTy, " (", String.concatWithMap "," toString paramTys, ")*"
                ]
            | GCPtrTy ty => toString ty ^ " addrspace(1)*"
            | PtrTy ty => toString ty ^ "*"
            | ArrayTy(sz, ty) => String.concat ["[", Int.toString sz, " x ", toString ty, "]"]
            | StructTy tys => String.concat [
                  "{", String.concatWithMap "," toString tys, "}"
                ]
            | Token => "token"
            | VarArg => "..."
          (* end case *))

    fun deref ty = (case ty
           of PtrTy ty => SOME ty
            | GCPtrTy ty => SOME ty
            | _ => NONE
          (* end case *))

  (* error checking/reporting is light here, we just care about
   * getting the right type for well-formed queries.
   *)
    fun gepTy (ptrTy, _::offsets) = let
          fun lp ([], ty) = ty
            | lp (v::vs, ty) = (case (ty, v)
                 of (StructTy us, Rep.IConst(_, i)) => lp(vs, List.nth(us, IntInf.toInt i))
                  | (ArrayTy(_, u), _) => u
                  | _ => ty    (* optimistic. it's either ty or an error *)
                (* end case *))
          in
            case ptrTy
             of PtrTy ty => PtrTy(lp(offsets, ty)) (* step through the pointer *)
              | GCPtrTy ty => GCPtrTy(lp(offsets, ty))
              | _ => raise Fail(concat[
                    "gepTy (", toString ptrTy, "); argument must be pointer type"
                  ])
            (* end case *)
          end

  (* are two types equal? *)
    fun same (ty1, ty2) = (case (ty1, ty2)
           of (VoidTy, VoidTy) => true
            | (Int1Ty, Int1Ty) => true
            | (Int32Ty, Int32Ty) => true
            | (Int64Ty, Int64Ty) => true
            | (FuncTy(retTy1, tys1), FuncTy(retTy2, tys2)) =>
                same(retTy1, retTy2) andalso ListPair.allEq same (tys1, tys2)
            | (PtrTy ty1, PtrTy ty2) => same (ty1, ty2)
            | (GCPtrTy ty1, GCPtrTy ty2) => same (ty1, ty2)
            | (ArrayTy(n1, ty1), ArrayTy(n2, ty2)) => (n1 = n2) andalso same (ty1, ty2)
            | (StructTy tys1, StructTy tys2) => ListPair.allEq same (tys1, tys2)
            | (Token, Token) => true
            | (VarArg, VarArg) => true
            | _ => false
          (* end case *))

  end
