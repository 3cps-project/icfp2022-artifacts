(* cps.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The 3-CPS IR
 *)

structure CPS =
  struct

    type ty = CPSTypes.t
    type label = Label.t

  (* datatype and exception constructors *)
    type dcon = CPSTypes.dcon

  (* lambda variables: use for functions, parameters, etc. *)
    type lvar = LVar.t

  (* continuation variables: use for continuations *)
    type cvar = CVar.t

  (* constant values *)
    datatype atom
      = LVAR of lvar * ty list          (* Type instantiated variable *)
      | LIT of Literal.t * ty
      | DCON of dcon * ty list
      | UNIT

    datatype exp = EXP of label * term

    and term
      = LETFUN of lambda list * exp
      | LETCONT of clambda list * exp
      | IF of PrimOp.test * lvar list * exp * exp
      | SWITCH of lvar * (pat * exp) list
      | APPLY of lvar * ty list * lvar list * cvar list
      | THROW of cvar * lvar list
    (* primitive operations: these embed a "flattened" CLAMBDA continuation *)
      | DCAPPLY of dcon * ty list * lvar * lvar * exp
      | PURE of PrimOp.pure * lvar list * lvar * exp
      | ARITH of PrimOp.arith * lvar list * lvar * exp * exp    (* second exp is exh *)
      | GET of PrimOp.getter * lvar list * lvar * exp
      | SET of PrimOp.setter * lvar list * lvar * exp
      | TUPLE of lvar list * lvar * exp
      | SELECT of int * lvar * lvar * exp
      | ATOM of atom * lvar * exp

    and pat
      = VPAT of lvar
      | LPAT of Literal.t * ty
      | DCPAT of dcon * ty list * lvar option

    withtype lambda = lvar * label * lvar list * cvar list * exp
         and clambda = cvar * label * lvar list * exp

    datatype comp_unit = CU of lambda

    fun mkLambda (f, xs, ks, e) = (f, Label.new(), xs, ks, e)
    fun mkCLambda (k, xs, e) = (k, Label.new(), xs, e)

    fun mkEXP term = EXP(Label.new(), term)
    fun mkLETFUN (binds, e) = mkEXP(LETFUN(binds, e))
    (* FIXME.
       BQ: I made a change where mkLETFUN does not call mkLambda anymore.
       Since mkLETFUN is only called once in convert, this was small. 
       I need to propagate the change to mkCLambdas now. *)
    fun mkLETCONT (binds, e) = mkEXP(LETCONT(binds, e))
    fun mkIF arg = mkEXP(IF arg)
    fun mkSWITCH arg = mkEXP(SWITCH arg)
    fun mkAPPLY arg = mkEXP(APPLY arg)
    fun mkDCAPPLY arg = mkEXP(DCAPPLY arg)
    fun mkPURE arg = mkEXP(PURE arg)
    fun mkARITH arg = mkEXP(ARITH arg)
    fun mkGET arg = mkEXP(GET arg)
    fun mkSET arg = mkEXP(SET arg)
    fun mkTHROW arg = mkEXP(THROW arg)
    fun mkTUPLE arg = mkEXP(TUPLE arg)
    fun mkSELECT arg = mkEXP(SELECT arg)
    fun mkATOM arg = mkEXP(ATOM arg)

    fun compare (EXP(l1, e1), EXP(l2,e2)) = Label.compare (l1, l2)
    fun same (EXP(l1, e1), EXP(l2,e2)) = Label.same (l1, l2)
    fun hash (EXP(l, e)) = Label.hash l

    local
      structure Key =
        struct
          type ord_key = exp
          val compare = compare
        end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    structure Tbl = HashTableFn (struct
        type hash_key = exp
        val hashVal = hash
        val sameKey = same
      end)

  end
