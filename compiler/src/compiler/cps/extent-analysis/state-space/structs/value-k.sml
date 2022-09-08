(* value-k.sml
 *
 * Abstract continuation closures and values.
 *)

(* Continuation closures *)
structure CloKBase = struct

    type t = (CPS.clambda * Env.t * EnvK.t * TEnv.t)

    fun toString (((_, lab, _, _), env, envK, tenv) : t) =
          String.concat["(cont ", Label.toString lab, ")"]

    fun compare (cloK1 : t, cloK2 : t) =
        (case Label.compare(#2(#1 cloK1), #2(#1 cloK2))
          of EQUAL => 
             (case Env.compare (#2 cloK1, #2 cloK2)
               of EQUAL =>
                  (case EnvK.compare (#3 cloK1, #3 cloK2)
                    of EQUAL => TEnv.compare (#4 cloK1, #4 cloK2)
                     | ord => ord)
                | ord => ord
             (* end case *))
           | ord => ord
        (* end case *))

    fun same (cloK1, cloK2) =
        case compare (cloK1, cloK2)
         of EQUAL => true
          | _ => false

    fun hash ((_, lab, _, _), _, _, _) = Label.hash lab

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
      structure Map = RedBlackMapFn (Key)
      structure Set = RedBlackSetFn (Key)
    end (* local *)

  end

structure CloK = MyHashCons (structure Base = CloKBase)

structure ValueK =
  struct

    datatype t = CLOK of CloK.Set.set
               | INDEX of int

    fun empty () = INDEX ~1

    fun isEmpty _ = raise Fail "ValueK.isEmpty"

    fun join (dK1, dK2) = (case (dK1, dK2)
         of (CLOK cloKs1, CLOK cloKs2) => CLOK (CloK.Set.union (cloKs1, cloKs2))
          | (INDEX index1, INDEX index2) =>
            if index1 = index2
            then INDEX index1
            else raise Fail "ValueK.join"
          | _ => raise Fail "ValueK.join"
        (* end case *))

    fun difference (dK1, dK2) = raise Fail "ValueK.difference"

    fun from_cloK (cloK) = CLOK (CloK.Set.singleton cloK)

    fun from_index (index) = INDEX index

    fun compare (dK1, dK2) = (case (dK1, dK2)
         of (CLOK cloKs1, CLOK cloKs2) => CloK.Set.compare (cloKs1, cloKs2)
          | (CLOK _, _) => LESS
          | (_, CLOK _) => GREATER
          | (INDEX index1, INDEX index2) =>
              if index1 > index2 then GREATER
              else if index1 = index2 then EQUAL
              else LESS
        (* end case *))

    fun toString dK = (case dK
         of CLOK cloKs =>
              "cloKs: " ^ String.concatWithMap " " CloK.toString (CloK.Set.listItems cloKs)
          | INDEX index => "index: " ^ Int.toString index
        (* end case *))

  end
