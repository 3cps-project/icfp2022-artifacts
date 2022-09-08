(* good23.sml
 *
 * test string primops
 *)

datatype 'a option = NONE | SOME of 'a

structure String =
  struct
    val sub = string_sub

    fun explode s = let
          fun lp (ix, chrs) = if (ix < 0)
                then chrs
                else lp (ix - 1, sub(s, ix) :: chrs)
          in
            lp (size s - 1, [])
          end

  end

structure Int =
  struct

    fun isSpace #" " = true
      | isSpace #"\t" = true
      | isSpace #"\n" = true
      | isSpace #"\r" = true
      | isSpace _ = false

    fun fromString s = let
          fun skipWS [] = NONE
            | skipWS (c::cs) = if isSpace c
                then skipWS cs
                else doSign (c, cs)
          and doSign (#"~", cs) = doNum (true, cs)
            | doSign (#"-", cs) = doNum (true, cs)
            | doSign (#"+", cs) = doNum (false, cs)
            | doSign (c, cs) = doNum (false, c::cs)
          and doNum (_, []) = NONE
            | doNum (isNeg, d::ds) = let
                fun cvtDigit d = if (#"0" <= d) andalso (d <= #"9")
                      then SOME(ord d - ord #"0")
                      else NONE
                fun finish n = if isNeg then SOME(~n) else SOME n
                fun doDigits ([], n) = finish n
                  | doDigits (d::ds, n) = (case cvtDigit d
                       of SOME m => doDigits (ds, 10*n + m)
                        | NONE => finish n
                      (* end case *))
                in
                  case cvtDigit d
                   of SOME n => doDigits (ds, n)
                    | NONE => NONE
                end
          in
            skipWS (String.explode s)
          end

  end

(* test *)
fun chk (SOME(n1 : int), SOME n2) = (n1 = n2)
  | chk (NONE, NONE) = true
  | chk _ = false

val ok = chk(SOME 10, Int.fromString " +10 ")
      andalso chk(SOME ~42, Int.fromString "~42")
      andalso chk(SOME 17, Int.fromString "17xxx");
