(* value-k.sml
 *
 * Concrete continuation values.
 *)

structure CValueKBase = struct

    type cloK = (CPS.clambda * CEnv.t * CEnvK.t * (Frame.t list))

    datatype t = HALT | CLOK of cloK

  end

(* concrete continuation values *)
structure CValueK = struct

    structure VKB = CValueKBase

    type base = CValueKBase.t

    val halt = (CId.special, VKB.HALT, Frame.Set.empty)

    type t = CId.t * base * Frame.Set.set

    fun make (id, base, frms) : t = (id, base, frms)

    fun base (id, k, frms) = k
    fun id (id, d, frms) = id
    fun frms (id, d, frms) = frms

    fun label ((_, base, _) : t) =
        case base
         of VKB.HALT => NONE
          | VKB.CLOK ((_, lab_lamK, _, _) : CPS.clambda, _, _, _) => SOME lab_lamK

    fun frms_lex (id, cont, frms) = (case cont
           of VKB.HALT => []
            | VKB.CLOK(_, _, _, frms_lex) => frms_lex
          (* end case *))

    fun toString (id, cont, frms) = (case cont
           of VKB.HALT => "HALT"
            | VKB.CLOK((_, lab, _, _), env, envK, _) => String.concat[
                  "(cont (", Label.toString lab, ")", " ",
                  CEnv.toString env, " ", CEnvK.toString envK, ")"
                ]
          (* end case *))

    fun compare ((id1, cont1, frms1) : t, (id2, cont2, frms2) : t) = CId.compare (id1, id2)

    local
      structure Key = struct type ord_key = t val compare = compare end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    end (* local *)

  end
