(* chk-lit.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ChkLit : sig

    val check : Context.t * Literal.t -> Literal.t * Types.ty

  end = struct

    structure L = Literal
    structure C = Context

  (* error reporting *)
    datatype token = datatype TypeError.token
    val error = Context.error
    val warning = Context.warning

  (* typecheck a literal; numbers should be representable in 63 bits, but
   * this is just a warning for now, since some examples require IntInf.int
   * and we only have one integer type.
   *)
    fun check (cxt, lit) = (case lit
           of L.Int i =>
                if ((i < ~0x4000000000000000) orelse (0x3FFFFFFFFFFFFFFF < i))
                  then (
                    warning(cxt, [
                        S "integer literal ", S(IntInf.toString i),
                        S " out of range"
                      ]);
                    (L.Int 0, PrimTy.intTy))
                  else (lit, PrimTy.intTy)
            | L.Word w =>
                if (0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF < w)
                  then (
                    warning(cxt, [
                        S "word literal ", S(IntInf.toString w),
                        S " out of range"
                      ]);
                    (L.Word 0, PrimTy.wordTy))
                  else (lit, PrimTy.wordTy)
            | L.Real _ => (lit, PrimTy.realTy)
            | L.Char _ => (lit, PrimTy.charTy)
            | L.String _ => (lit, PrimTy.stringTy)
          (* end case *))

  end
