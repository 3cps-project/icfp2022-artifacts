(* prim-op.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Primitive operators.  These are used both in the SimpleAST and CPS IRs.
 *
 * TODO: we could clean this up quite a bit by adding a foreign-function-call
 * mechanism for the math libraries.
 *
 * Also note that if we make the test for divide-by-zero explicit, then the
 *)

structure PrimOp =
  struct

  (* "pure" primitive operators that have no effects and cannot be influenced by
   * effects (i.e., they do not read from mutable memory.
   *
   * NOTE: in SimpleAST, "Floor" can raise the Domain exception on NaNs,
   * so it is not strictly pure!  We probably should generate the NaN test
   * in the simplifier, instead of during CPS conversion.
   *)
    structure Pure =
      struct
      (* numeric operations; the precision is specified separately *)
        datatype num_op
          = WAdd | WSub | WMul | WDiv | WMod | WNeg     (* unsigned word arithmetic *)
          | Andb | Orb | XOrb | Notb                    (* bitwise operations *)
          | LShift | RShift | RShiftL                   (* shift operations *)
          | FAdd | FSub | FMul | FDiv | FNeg            (* floating-point arithmetic *)

      (* some math functions for benchmarking *)
        datatype math_op
          = Sqrt | Ln | Exp | Pow
          | Sin | Cos | Tan
          | ASin | ACos | ATan | ATan2

        datatype t
          = NumOp of num_op * int
          | IIAdd | IISub | IIMul | IINeg               (* IntInf arithmetic; these are
                                                         * pure since they cannot overflow.
                                                         *)
        (* non-trapping conversions between ints and words *)
          | ZExt of {from : int, to : int}              (* zero-extend to larger size *)
          | SExt of {from : int, to : int}              (* sign-extend to larger size *)
          | Trunc of {from : int, to : int}             (* truncate to smaller size *)
        (* convert integers to real *)
          | IntToReal of {from : int, to : int}
        (* array and ref operators *)
          | Array0 | ArrayAlloc | ArrayLength | Ref
        (* string operators *)
          | StrSize
          | CharToStr
        (* some not-so-primitive operators *)
          | SAppend
          | Implode
          | MathOp of math_op * int

        fun arity rator = (case rator
           of NumOp(WAdd, _) => 2
            | NumOp(WSub, _) => 2
            | NumOp(WMul, _) => 2
            | NumOp(WDiv, _) => 2
            | NumOp(WMod, _) => 2
            | NumOp(Andb, _) => 2
            | NumOp(Orb, _) => 2
            | NumOp(XOrb, _) => 2
            | NumOp(LShift, _) => 2
            | NumOp(RShift, _) => 2
            | NumOp(RShiftL, _) => 2
            | NumOp(FAdd, _) => 2
            | NumOp(FSub, _) => 2
            | NumOp(FMul, _) => 2
            | NumOp(FDiv, _) => 2
            | IIAdd => 2
            | IISub => 2
            | IIMul => 2
            | Array0 => 0
            | ArrayAlloc => 2
            | SAppend => 2
            | MathOp(Pow, _) => 2
            | MathOp(ATan2, _) => 2
            | _ => 1
          (* end case *))

        fun toString rator = (case rator
           of NumOp(rator, sz) => let
                val rator = (case rator
                       of WAdd => "WAdd"
                        | WSub => "WSub"
                        | WMul => "WMul"
                        | WDiv => "WDiv"
                        | WMod => "WMod"
                        | WNeg => "WNeg"
                        | Andb => "Andb"
                        | Orb => "Orb"
                        | XOrb => "XOrb"
                        | Notb => "Notb"
                        | LShift => "LShift"
                        | RShift => "RShift"
                        | RShiftL => "RShiftL"
                        | FAdd => "FAdd"
                        | FSub => "FSub"
                        | FMul => "FMul"
                        | FDiv => "FDiv"
                        | FNeg => "FNeg"
                      (* end case *))
                in
                  rator ^ Int.toString sz
                end
            | IIAdd => "IIAdd"
            | IISub => "IISub"
            | IIMul => "IIMul"
            | IINeg => "IINeg"
            | ZExt{from, to} => concat["ZExt", Int.toString from, "to", Int.toString to]
            | SExt{from, to} => concat["SExt", Int.toString from, "to", Int.toString to]
            | Trunc{from, to} => concat["Trunc", Int.toString from, "to", Int.toString to]
            | IntToReal{from, to} => concat["Int", Int.toString from, "toReal", Int.toString to]
            | Array0 => "Array0"
            | ArrayAlloc => "ArrayAlloc"
            | ArrayLength => "ArrayLength"
            | Ref => "Ref"
            | StrSize => "StrSize"
            | CharToStr => "CharToStr"
            | Implode => "Implode"
            | SAppend => "SAppend"
            | MathOp(rator, sz) => let
                val rator = (case rator
                       of Sqrt => "Sqrt"
                        | Ln => "Ln"
                        | Exp => "Exp"
                        | Pow => "Pow"
                        | Sin => "Sin"
                        | Cos => "Cos"
                        | Tan => "Tan"
                        | ASin => "ASin"
                        | ACos => "ACos"
                        | ATan => "ATan"
                        | ATan2 => "ATan2"
                      (* end case *))
                in
                  rator ^ Int.toString sz
                end
          (* end case *))
      end

  (* arithmetic primops that can raise exceptions. *)
    structure Arith =
      struct

      (* trapping arithmetic operations; the precision is specified separately *)
        datatype int_op = IAdd | ISub | IMul | IDiv | IMod | INeg

        datatype t
          = IntOp of int_op * int
        (* real to integer conversion *)
          | Floor of {from : int, to : int}
        (* get a character from a string *)
          | StrSub

        fun arity rator = (case rator
           of IntOp(INeg, _) => 1
            | Floor _ => 1
            | _ => 2
          (* end case *))

        fun toString rator = (case rator
           of IntOp(rator, sz) => let
                val rator = (case rator
                       of IAdd => "IAdd"
                        | ISub => "ISub"
                        | IMul => "IMul"
                        | IDiv => "IDiv"
                        | IMod => "IMod"
                        | INeg => "INeg"
                      (* end case *))
                in
                  if sz = 0
                    then "I" ^ rator    (* IntInf division or modulo *)
                    else rator ^ Int.toString sz
                end
            | Floor{from, to} => concat["Floor", Int.toString from, "to", Int.toString to]
            | StrSub => "StrSub"
          (* end case *))

      end

  (* operations that read mutable memory, but do not change it *)
    structure Getter =
      struct
        datatype t = ArraySub | Deref

        fun arity ArraySub = 2
          | arity Deref = 1

        fun toString ArraySub = "ArraySub"
          | toString Deref = "Deref"

      end

  (* operations that change mutable memory *)
    structure Setter =
      struct
        datatype t = ArrayUpdate | Assign | Print

        fun arity ArrayUpdate = 3
          | arity Assign = 2
          | arity Print = 1

        fun toString ArrayUpdate = "ArrayUpdate"
          | toString Assign = "Assign"
          | toString Print = "Print"

      end

    structure Test =
      struct

      (* integer/word comparisons *)
        datatype icmp_op
         = ILt | ILte | IGt | IGte      (* signed comparisons *)
         | ULt | ULte | UGt | UGte      (* unsigned comparisons *)
         | IEq | INEq                   (* equality *)

      (* floating-point comparisons.
       * NOTE: this should eventually include all of the IEEE comparison modes.
       *)
        datatype fcmp_op
          = FLt | FLte | FEq | FNEq | FGte | FGt

        datatype t
          = ICmp of icmp_op * int
          | FCmp of fcmp_op * int
          | SLt | SLte | SEq | SNEq | SGte | SGt        (* string comparisons *)
          | PtrEq | PtrNEq                              (* pointer equality tests *)
          | PolyEq | PolyNEq                            (* polymorphic equality tests *)

        fun arity rator = 2

        fun toString tst = (case tst
               of ICmp(rator, sz) => let
                    val (prefix, rator) = (case rator
                           of ILt => ("I", "Lt")
                            | ILte => ("I", "Lte")
                            | IEq => ("I", "Eq")
                            | INEq => ("I", "NEq")
                            | IGte => ("I", "Gte")
                            | IGt => ("I", "Gt")
                            | ULt => ("U", "Lt")
                            | ULte => ("U", "Lte")
                            | UGte => ("U", "Gte")
                            | UGt => ("U", "Gt")
                          (* end case *))
                    in
                      if (sz = 0)
                        then "II" ^ rator
                        else concat[prefix, Int.toString sz, rator]
                    end
                | FCmp(rator, sz) =>let
                    val rator = (case rator
                           of FLt => "Lt"
                            | FLte => "Lte"
                            | FEq => "Eq"
                            | FNEq => "NEq"
                            | FGte => "Gte"
                            | FGt => "Gt"
                          (* end case *))
                    in
                      concat["F", Int.toString sz, rator]
                    end
                | SLt => "SLt"
                | SLte => "SLte"
                | SEq => "SEq"
                | SNEq => "SNEq"
                | SGte => "SGte"
                | SGt => "SGt"
                | PtrEq => "PtrEq"
                | PtrNEq => "PtrNEq"
                | PolyEq => "PolyEq"
                | PolyNEq => "PolyNEq"
              (* end case *))

      end

      datatype pure = datatype Pure.t
      datatype arith = datatype Arith.t
      datatype getter = datatype Getter.t
      datatype setter = datatype Setter.t
      datatype test = datatype Test.t

  end
