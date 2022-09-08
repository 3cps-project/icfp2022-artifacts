(* value.sml
 *
 * Concrete values.
 *)

(* closures *)
structure ThreeCPSCloValue =
  struct

    type t = (CPS.lambda * (int LVar.Map.map) * (CPSTypes.t CPSTyVar.Map.map))

    fun compare (clo1 : t, clo2 : t) = (case Label.compare(#2(#1 clo1), #2(#1 clo2))
           of EQUAL => LVar.Map.collate Int.compare (#2 clo1, #2 clo2)
            | order => order
          (* end case *))

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (((_, lab, _, _, _), env, tenv) : t) = concat[
            "(clo<", Label.toString lab, "> ",
            "(" ^ (String.concatWithMap " " (fn (x, a) => "(" ^ (LVar.toString x) ^ " => " ^ (Int.toString a ^ ")"))
                                                (LVar.Map.listItemsi env))
                    ^ ")",
                    ")"
          ]

  end (* CCloValue *)

(* data values *)
structure ThreeCPSDataValue =
  struct

    type t = CPSDataCon.t * ThreeCPSAddr.t option

    fun compare ((dc1, a1o), (dc2, a2o)) =
        (case CPSDataCon.compare (dc1, dc2)
          of EQUAL =>
             (case (a1o, a2o)
               of (NONE, NONE) => EQUAL
                | (SOME _, NONE) => GREATER
                | (NONE, SOME _) => LESS
                | (SOME a1, SOME a2) => ThreeCPSAddr.compare (a1, a2)
             (* end case *))
           | order => order
        (* end case *))

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (dcon, ao) = "(dv " ^ (CPSDataCon.toString dcon)
                              ^ (case ao of NONE => "" | SOME a => " " ^ (ThreeCPSAddr.toString a))
                              ^ ")"

  end

(* references *)
structure ThreeCPSRefValue =
  struct

    type t = ThreeCPSAddr.t

    fun compare (a1, a2) = ThreeCPSAddr.compare (a1, a2)

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (a) = "(ref " ^ (ThreeCPSAddr.toString a) ^ ")"

  end

(* references *)
structure ThreeCPSArrayValue =
  struct

    type t = ThreeCPSAddr.t list

    val compare = List.collate ThreeCPSAddr.compare

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (addrs) = "(array " ^ (String.concatWithMap " " ThreeCPSAddr.toString addrs) ^ ")"

  end

(* tuples *)
structure ThreeCPSTupleValue =
  struct

    type t = ThreeCPSAddr.t list

    val compare = List.collate ThreeCPSAddr.compare

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

    fun toString (alist : t) =
        "(tv " ^
        (String.concatWithMap " " ThreeCPSAddr.toString alist)
        ^ ")"

  end

(* minimal interface to CValue and CValueK structures *)
signature ThreeCPSVALUE =
  sig

    type base
    type t

    val make : base -> t

    val base : t -> base

    val compare : t * t -> order

    val toString : t -> string

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t

  end

(* The base value type for concrete values. *)
structure ThreeCPSValueBase : sig

    datatype t = CLO of ThreeCPSCloValue.t
               | DATA of ThreeCPSDataValue.t
               | REF of ThreeCPSRefValue.t
               | ARRAY of ThreeCPSArrayValue.t
               | TUPLE of ThreeCPSTupleValue.t
               | FLOAT of real
               | INT of IntInf.int
               | WORD of word
               | CHAR of IntInf.int
               | STRING of string
               | UNIT

    val compare : t * t -> order
    val toString : t -> string

end = struct

structure DV = ThreeCPSDataValue
structure TV = ThreeCPSTupleValue

datatype t = CLO of ThreeCPSCloValue.t
           | DATA of DV.t
           | REF of ThreeCPSRefValue.t
           | ARRAY of ThreeCPSArrayValue.t
           | TUPLE of TV.t
           | FLOAT of real
           | INT of IntInf.int
           | WORD of word
           | CHAR of IntInf.int
           | STRING of string
           | UNIT

fun compare (d1, d2) =
    case (d1, d2)
     of (CLO clo1, CLO clo2) => ThreeCPSCloValue.compare (clo1, clo2)
      | (CLO _, _) => LESS
      | (_, CLO _) => GREATER
      | (DATA data1, DATA data2) => DV.compare (data1, data2)
      | (DATA _, _) => LESS
      | (_, DATA _) => GREATER
      | (REF r1, REF r2) => ThreeCPSRefValue.compare (r1, r2)
      | (REF _, _) => LESS
      | (_, REF _) => GREATER
      | (ARRAY arr1, ARRAY arr2) => ThreeCPSArrayValue.compare (arr1, arr2)
      | (ARRAY _, _) => LESS
      | (_, ARRAY _) => GREATER
      | (TUPLE t1, TUPLE t2) => TV.compare (t1, t2)
      |  (TUPLE _, _) => LESS
      |  (_, TUPLE _) => GREATER
      | (UNIT, UNIT) => EQUAL
      | (UNIT, _) => LESS
      | (_, UNIT) => GREATER
      | (INT i1, INT i2) => IntInf.compare (i1, i2)
      | (INT _, _) => LESS
      | (_, INT _) => GREATER
      | (WORD w1, WORD w2) => Word.compare (w1, w2)
      | (WORD _, _) => LESS
      | (_, WORD _) => GREATER
      | (FLOAT f1, FLOAT f2) => Real.compare (f1, f2)
      | (FLOAT _, _) => LESS
      | (_, FLOAT _) => GREATER
      | (CHAR c1, CHAR c2) => IntInf.compare (c1, c2)
      | (CHAR _, _) => LESS
      | (_, CHAR _) => GREATER
      | (STRING s1, STRING s2) => String.compare (s1, s2)

fun toString d = (case d
     of CLO clo => ThreeCPSCloValue.toString clo
      | DATA data => DV.toString data
      | REF r => ThreeCPSRefValue.toString r
      | ARRAY arr => ThreeCPSArrayValue.toString arr
      | TUPLE tup => TV.toString tup
      | UNIT => "(unit)"
      | INT i => IntInf.toString i
      | WORD w => Word.toString w
      | FLOAT f => Real.toString f
      | CHAR c => concat["#\"", Char.toString (Char.chr (IntInf.toInt c)), "\""]
      | STRING s => concat["\"", String.toString s, "\""]
    (* end case *))

end

(* The actual concrete value type.
   consists of a base and a level *)
structure ThreeCPSValue : sig

  include ThreeCPSVALUE
(*
  val hasLabel : t * Label.t -> bool
  val label : t -> Label.t option
  *)                         
end = struct

  type base = ThreeCPSValueBase.t
  type t = base

  fun make base = base
  fun base d = d
(*

  (* Returns whether the given value has the given label? *)
  (* So far the only values with labels are closures *)
  fun hasLabel (d, l) = (case base d
         of (ThreeCPSValueBase.CLO ((_, l', _, _, _, _), _)) => Label.same (l, l')
          | _ => false
        (* end case *))

  (* Returns the label of the given value if it has one *)
  fun label d = (case base d
         of (ThreeCPSValueBase.CLO((_, l, _, _, _, _), _)) => SOME l
          | _ => NONE
        (* end case *))
*)
  fun compare (d1, d2) = ThreeCPSValueBase.compare (d1, d2)

  fun toString d = ThreeCPSValueBase.toString d

  local
      structure Key = struct type ord_key = t val compare = compare end
  in
  structure Map = RedBlackMapFn (Key)
  structure Set = RedBlackSetFn (Key)
  end (* local *)

end
