(* parser-comb.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * This example is a simple parser implemented using a stripped-down
 * version of the parser combinators from the SML/NJ Library.
 * As such, it is an example of a program that makes heavy use
 * of higher-order functions.
 *)

structure Char =
  struct

    fun isDigit c = ((#"0" <= c) andalso (c <= #"9"))

    fun isAlpha c = ((#"a" <= c) andalso (c <= #"z")) orelse ((#"A" <= c) andalso (c <= #"Z"))

    fun isAlphaNum c = isAlpha c orelse isDigit c

    fun isSpace (#" ") = true
      | isSpace (#"\t") = true
      | isSpace (#"\n") = true
      | isSpace _ = false

  end

structure List =
  struct

    fun revAppend (xs, ys) = (case xs of [] => ys | x::xr => revAppend (xr, x::ys))

    fun rev xs = revAppend (xs, [])

    fun foldl f init xs = let
          fun foldf ([], acc) = acc
            | foldf (x::xr, acc) = foldf (xr, f(x, acc))
          in
            foldf (xs, init)
          end

  end

structure String =
  struct

    val sub = string_sub
    val implode = implode

  end

structure StringCvt =
  struct

    datatype radix = BIN | OCT | DEC | HEX

    type ('a, 'strm) reader = 'strm -> ('a * 'strm) option

    fun scanString scanFn s = let
          val n = size s
          fun getc i = if (i < n) then SOME(String.sub(s, i), i+1) else NONE
          in
            case (scanFn getc 0)
             of NONE => NONE
              | SOME(x, _) => SOME x
            (* end case *)
          end

    fun skipWS (getc : 'a -> (char * 'a) option) = let
          fun lp cs = (case (getc cs)
                 of (SOME(c, cs')) => if (Char.isSpace c) then lp cs' else cs
                  | NONE => cs
                (* end case *))
          in
            lp
          end

  end

structure Int =
  struct

    fun scan radix getc = let
          fun scan' strm = let
                val strm = StringCvt.skipWS getc strm
                val (isNeg, strm) = (case getc strm
                       of SOME(#"-", strm') => (true, strm')
                        | SOME(#"~", strm') => (true, strm')
                        | _ => (false, strm)
                      (* end case *))
                fun getDigit strm = (case getc strm
                       of SOME(c, strm') => if Char.isDigit c
                             then SOME(ord c - ord #"0", strm')
                             else NONE
                        | NONE => NONE
                      (* end case *))
                fun lp (strm, n) = (case getDigit strm
                         of SOME(d, strm') => lp (strm', 10*n + d)
                          | NONE => if isNeg then SOME(~n, strm) else SOME(n, strm)
                        (* end case *))
                in
                  case getDigit strm
                   of SOME(d, strm') => lp (strm', d)
                    | NONE => NONE
                  (* end case *)
                end
          in
            scan'
          end

  end

structure ParserComb =
  struct

    type ('a, 'strm) parser = (char, 'strm) StringCvt.reader -> ('a, 'strm) StringCvt.reader

    fun wrap (p, f) getc strm = (case (p getc strm)
           of NONE => NONE
            | (SOME(x, strm)) => SOME(f x, strm)
          (* end case *))

    fun seqWith f (p1, p2) getc strm = (case (p1 getc strm)
           of SOME(t1, strm1) => (case (p2 getc strm1)
                 of SOME(t2, strm2) => SOME(f(t1, t2), strm2)
                  | NONE => NONE
                (* end case *))
            | NONE => NONE
          (* end case *))
    fun seq (p1, p2) = seqWith (fn x => x) (p1, p2)

    fun eatChar pred getc strm = (case getc strm
           of (res as SOME(c, strm')) => if (pred c) then res else NONE
            | _ => NONE
          (* end case *))

    fun char (c: char) = eatChar (fn c' => (c = c'))

    fun string s getc strm = let
          fun eat (i, strm) = if (i < size s)
                then (case (String.sub(s, i), getc strm)
                   of (c1, SOME(c2, strm')) =>
                        if (c1 = c2) then eat(i+1, strm') else NONE
                    | _ => NONE
                  (* end case *))
                else SOME(s, strm)
          in
            eat (0, strm)
          end

    fun skipBefore pred p getc strm = let
          fun skip' strm = (case getc strm
                 of NONE => NONE
                  | SOME(c, strm') =>
                      if (pred c) then skip' strm' else p getc strm
                (* end case *))
          in
            skip' strm
          end

    fun or' l getc strm = let
          fun tryNext [] = NONE
            | tryNext (p::r) = (case (p getc strm)
                 of NONE => tryNext r
                  | res => res
                (* end case *))
          in
            tryNext l
          end

    fun zeroOrMore p getc strm = let
          val p = p getc
          fun parse (l, strm) = (case (p strm)
                 of (SOME(item, strm)) => parse (item::l, strm)
                  | NONE => SOME(List.rev l, strm)
                (* end case *))
          in
            parse ([], strm)
          end

    fun token pred getc strm = (case (zeroOrMore (eatChar pred) getc strm)
           of (SOME(res as _::_, strm)) => SOME(implode res, strm)
            | _ => NONE
          (* end case *))

  end

structure Main =
  struct

    structure P = ParserComb

    datatype exp
      = VAR of string
      | NUM of int
      | ADD of exp * exp
      | LET of string * exp * exp

    fun snd (_, x) = x

    val seq = P.seq

    fun skipWS getc = P.skipBefore Char.isSpace getc

    fun numParser getc = P.wrap (Int.scan StringCvt.DEC, NUM) getc

    fun idParser getc = P.seqWith (op ^) (
          P.wrap (P.eatChar Char.isAlpha, str),
          P.token Char.isAlphaNum) getc

    fun varParser getc = P.wrap(idParser, VAR) getc

    fun letParser getc = P.wrap (
          seq(P.string "let", seq(skipWS(idParser), seq(skipWS(P.char #"="), seq(expParser,
            seq(skipWS(P.string "in"), expParser))))),
          fn (_, (x, (_, (e1, (_, e2))))) => LET(x, e1, e2)) getc
    and expParser getc = P.wrap (
          skipWS (P.seq (
            P.or' [letParser, numParser, varParser],
            addParser)),
          fn (e, es) => List.foldl (fn (a, b) => ADD(b, a)) e es) getc
    and addParser getc =
          P.zeroOrMore (skipWS (P.wrap (seq(P.char #"+", expParser), snd))) getc

    val _ = StringCvt.scanString addParser  " let x = 1+2 in x + x "

  (* should return SOME (LET ("x", ADD (NUM 1, NUM 2), ADD (VAR "x", VAR "x"))) *)
    val res = StringCvt.scanString expParser "1+1+1"
    val res = StringCvt.scanString expParser " let x = 1+2 in x + x "
    val res2 = StringCvt.scanString expParser " let xx = 1+2 in let      yy3 = xx + \n 38 \t in xx + yy3 + (let x = 1 in xx) "

    val _ = Char.isDigit #"1"
    val _ = Char.isDigit #"a"
    val _ = Char.isDigit #" "
    val _ = Char.isAlpha #"1"
    val _ = Char.isAlpha #"a"
    val _ = Char.isAlpha #" "
    val _ = Char.isSpace #"\t"
    val _ = Char.isSpace #"\n"
    val _ = Char.isSpace #" "
    val _ = Char.isSpace #"a"
    val _ = Char.isSpace #"1"
    val _ = Char.isAlphaNum #"1"
    val _ = Char.isAlphaNum #"a"
    val _ = Char.isAlphaNum #" "

  end
