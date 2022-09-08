(* value-k.sml
 *
 * Concrete continuation values.
 *)

structure ThreeCPSValueKBase = struct

    type cloK = (CPS.clambda * (int LVar.Map.map) * (int CVar.Map.map) * (CPSTypes.t CPSTyVar.Map.map) * int * int)

    datatype t = HALT | CLOK of cloK

    fun stack_pointer (cloK : t) : int =
        case cloK
         of HALT => 0
          | CLOK (_, _, _, _, stack_pointer, _) => stack_pointer

    fun stackK_pointer (cloK : t) : int =
        case cloK
         of HALT => 0
          | CLOK (_, _, _, _, _, stackK_pointer) => stackK_pointer

  end

(* concrete continuation values *)
structure ThreeCPSValueK = struct

    structure VKB = ThreeCPSValueKBase

    type base = ThreeCPSValueKBase.t

    val halt = VKB.HALT

    type t = base

    fun make base : t = base

    fun base k = k

    fun toString cont = (case cont
           of VKB.HALT => "HALT"
            | VKB.CLOK((_, lab, _, _), env, envK, _, _, _) => String.concat[
                  "(cont (", Label.toString lab, ")", " ",
                  "(" ^ (String.concatWithMap " " (fn (x, a) => "(" ^ (LVar.toString x) ^ " => " ^ (Int.toString a ^ ")"))
                                              (LVar.Map.listItemsi env))
                  ^ ")",
                  " ",
                  "(" ^ (String.concatWithMap " " (fn (k, aK) => "(" ^ (CVar.toString k) ^ " => " ^ (Int.toString aK) ^ ")")
                                              (CVar.Map.listItemsi envK))
                  ^ ")"
                ]
          (* end case *))

  end
