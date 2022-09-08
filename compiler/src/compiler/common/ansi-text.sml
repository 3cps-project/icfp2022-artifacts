(* ansi-text.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * A utility module for producing stylized text using the ANSI teminal
 * control codes.
 *)

structure ANSIText : sig

  (* text style *)
    type t = {
        fg : int option,        (* foreground color (0-7) *)
        bg : int option,        (* background color (0-7) *)
        bf : bool,              (* bold? *)
        ul : bool               (* underline? *)
      }

    val fmt : t * string -> string

  (* remove ANSI escape sequences from a string *)
    val strip : string -> string

    val black : int
    val red : int
    val green : int
    val yellow : int
    val blue : int
    val purple : int
    val teal : int
    val white : int

  end = struct

    structure A = ANSITerm

    type t = {fg :int option, bg : int option, bf : bool, ul : bool}

    val colors = #[
            A.Black, A.Red, A.Green, A.Yellow, A.Blue, A.Magenta, A.Cyan, A.White
          ]

    val black = 0
    val red = 1
    val green = 2
    val yellow = 3
    val blue = 4
    val purple = 5
    val teal = 6
    val white = 7

    (* TODO: in 110.97, there will be an ANSITerm.RESET *)
    val reset = "\027[0m"

    fun fmt ({fg, bg, bf, ul}, msg) = if Controls.get Ctl.enableColor
          then let
            val cmds = if ul then [A.UL] else []
            val cmds = if bf then A.BF :: cmds else cmds
            val cmds = (case fg
                    of SOME fg => A.FG(Vector.sub(colors, fg)) :: cmds
                     | NONE => cmds
                  (* end case *))
            val cmds = (case bg
                    of SOME bg => A.BG(Vector.sub(colors, bg)) :: cmds
                     | NONE => cmds
                  (* end case *))
            in
              String.concat[A.toString cmds, msg, reset]
            end
          else msg

    structure SS = Substring

    fun strip s = let
        (* ANSI control sequences begin with an ESC (#"\027") and end with "m" *)
          fun removeEsc ss =
                Substring.triml 1 (Substring.dropl (fn #"m" => false | _ => true) ss)
          fun lp (ss, chars) = (case SS.getc ss
                 of SOME(#"\027", ss) => lp (removeEsc ss, chars)
                  | SOME(c, ss) => lp (ss, c::chars)
                  | NONE => String.implode(List.rev chars)
                (* end case *))
          in
            lp (SS.full s, [])
          end

  end
