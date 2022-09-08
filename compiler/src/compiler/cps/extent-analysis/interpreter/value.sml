(* value.sml
 *
 * Concrete values.
 *)

(* closures *)
structure CCloValue =
  struct

    type t = (CPS.lambda * CEnv.t * (Frame.t list))

    fun compare (clo1 : t, clo2 : t) = (case Label.compare(#2(#1 clo1), #2(#1 clo2))
           of EQUAL => CEnv.compare (#2 clo1, #2 clo2)
            | order => order
          (* end case *))

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (((_, lab, _, _, _), env, _) : t) = concat[
            "(clo<", Label.toString lab, "> ", CEnv.toString env, ")"
          ]

  end (* CCloValue *)

(* data values *)
structure CDataValue =
  struct

    type t = Label.t * CPSDataCon.t * CAddr.t option

    fun compare ((l1, dc1, a1o), (l2, dc2, a2o)) =
        (case CPSDataCon.compare (dc1, dc2)
          of EQUAL =>
             (case (a1o, a2o)
               of (NONE, NONE) => EQUAL
                | (SOME _, NONE) => GREATER
                | (NONE, SOME _) => LESS
                | (SOME a1, SOME a2) => CAddr.compare (a1, a2)
             (* end case *))
           | order => order
        (* end case *))

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (l, dcon, ao) = "(dv " ^ (CPSDataCon.toString dcon)
                                 ^ (case ao of NONE => "" | SOME a => " " ^ (CAddr.toString a))
                                 ^ ")"

  end

(* references *)
structure CRefValue =
  struct

    type t = CAddr.t

    fun compare (a1, a2) = CAddr.compare (a1, a2)

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (a) = "(ref " ^ (CAddr.toString a) ^ ")"

  end

(* references *)
structure CArrayValue =
  struct

    type t = CAddr.t list

    val compare = List.collate CAddr.compare

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (addrs) = "(array " ^ (String.concatWithMap " " CAddr.toString addrs) ^ ")"

  end

(* tuples *)
structure CTupleValue =
  struct

    type t = Label.t * (CAddr.t list)

    fun compare ((l1, addrs1), (l2, addrs2)) = List.collate CAddr.compare (addrs1, addrs2)

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString ((l, alist) : t) =
        "(tv " ^
        (String.concatWithMap " " CAddr.toString alist)
        ^ ")"

  end

(* minimal interface to CValue and CValueK structures *)
signature CVALUE =
  sig

    type base
    type t

    val make : CId.t * base * Frame.Set.set -> t

    val base : t -> base
    val id : t -> CId.t

    val compare : t * t -> order

    val toString : t -> string

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t

  end

(* The base value type for concrete values. *)
structure CValueBase : sig

    datatype t = CLO of CCloValue.t
               | DATA of CDataValue.t
               | REF of CRefValue.t
               | ARRAY of CArrayValue.t
               | TUPLE of CTupleValue.t
               | FLOAT of real
(* JHR: should really use IntInf.int to represent integer values, since the
 * actual range of values might be bigger than the `int` type supports.
 * At this point though, we are only running the interpreter on programs where this doesn't occur
 * BQ: Since the interpreter is only used at this point to test the analyses, I think it is probably fine to leave it as int.
 * Also, there is a program or two which has overflow.
 *)
               | INT of int
               | WORD of word
               | CHAR of char
               | STRING of string
               | UNIT

    val compare : t * t -> order
    val toString : t -> string

end = struct

structure DV = CDataValue
structure TV = CTupleValue

datatype t = CLO of CCloValue.t
           | DATA of DV.t
           | REF of CRefValue.t
           | ARRAY of CArrayValue.t
           | TUPLE of TV.t
           | FLOAT of real
(* JHR: should really use IntInf.int to represent integer values, since the
 * actual range of values might be bigger than the `int` type supports.
 * At this point though, we are only running the interpreter on programs where this doesn't occur
 * BQ: Since the interpreter is only used at this point to test the analyses, I think it is probably fine to leave it as int.
 * Also, there is a program or two which has overflow.
 *)
           | INT of int
           | WORD of word
           | CHAR of char
           | STRING of string
           | UNIT

fun compare (d1, d2) =
    case (d1, d2)
     of (CLO clo1, CLO clo2) => CCloValue.compare (clo1, clo2)
      | (CLO _, _) => LESS
      | (_, CLO _) => GREATER
      | (DATA data1, DATA data2) => DV.compare (data1, data2)
      | (DATA _, _) => LESS
      | (_, DATA _) => GREATER
      | (REF r1, REF r2) => CRefValue.compare (r1, r2)
      | (REF _, _) => LESS
      | (_, REF _) => GREATER
      | (ARRAY arr1, ARRAY arr2) => CArrayValue.compare (arr1, arr2)
      | (ARRAY _, _) => LESS
      | (_, ARRAY _) => GREATER
      | (TUPLE t1, TUPLE t2) => TV.compare (t1, t2)
      |  (TUPLE _, _) => LESS
      |  (_, TUPLE _) => GREATER
      | (UNIT, UNIT) => EQUAL
      | (UNIT, _) => LESS
      | (_, UNIT) => GREATER
      | (INT i1, INT i2) => Int.compare (i1, i2)
      | (INT _, _) => LESS
      | (_, INT _) => GREATER
      | (WORD w1, WORD w2) => Word.compare (w1, w2)
      | (WORD _, _) => LESS
      | (_, WORD _) => GREATER
      | (FLOAT f1, FLOAT f2) => Real.compare (f1, f2)
      | (FLOAT _, _) => LESS
      | (_, FLOAT _) => GREATER
      | (CHAR c1, CHAR c2) => Char.compare (c1, c2)
      | (CHAR _, _) => LESS
      | (_, CHAR _) => GREATER
      | (STRING s1, STRING s2) => String.compare (s1, s2)

fun toString d = (case d
     of CLO clo => CCloValue.toString clo
      | DATA data => DV.toString data
      | REF r => CRefValue.toString r
      | ARRAY arr => CArrayValue.toString arr
      | TUPLE tup => TV.toString tup
      | UNIT => "(unit)"
      | INT i => Int.toString i
      | WORD w => Word.toString w
      | FLOAT f => Real.toString f
      | CHAR c => concat["#\"", Char.toString c, "\""]
      | STRING s => concat["\"", String.toString s, "\""]
    (* end case *))

end

(* The actual concrete value type.
   consists of a base and a level *)
structure CValue : sig

  include CVALUE
  val hasLabel : t * Label.t -> bool
  val label : t -> Label.t option
  val frms : t -> Frame.Set.set

end = struct

  type base = CValueBase.t
  type t = CId.t * base * Frame.Set.set

  fun make (id, base, frms) = (id, base, frms)
  fun base (id, d, frms) = d
  fun id (id, d, frms) = id
  fun frms (id, d, frms) = frms

  (* Returns whether the given value has the given label? *)
  fun hasLabel (d, l) = (case base d
         of (CValueBase.CLO ((_, l', _, _, _), _, _)) => Label.same (l, l')
          | (CValueBase.TUPLE (l', addrs)) => Label.same (l, l')
          | (CValueBase.DATA (l', _, _)) => Label.same (l, l')
          | _ => false
        (* end case *))

  (* Returns the label of the given value if it has one *)
  fun label d = (case base d
         of (CValueBase.CLO((_, l, _, _, _), _, _)) => SOME l
          | (CValueBase.TUPLE (l, addrs)) => SOME l
          | (CValueBase.DATA (l, _, _)) => SOME l
          | _ => NONE
        (* end case *))

  fun compare ((id1, d1, frms1), (id2, d2, frms2)) = CId.compare (id1, id2)

  fun toString (id, d, frms) = CValueBase.toString d

  local
      structure Key = struct type ord_key = t val compare = compare end
  in
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  end (* local *)

end
