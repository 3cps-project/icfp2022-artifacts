(* parser.sml
 *
 * COPYRIGHT (c) 2007 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * CMSC 22610 Sample code (Winter 2007)
 *)

structure Parser : sig

  (* parse a file; return NONE if there are syntax errors *)
    val parseFile : (Error.err_stream * TextIO.instream) -> ParseTree.comp_unit option

  end = struct

  (* glue together the lexer and parser *)
    structure MinMLParser = MinMLParseFn(MinMLLex)

  (* error function for lexer *)
    fun lexErr errStrm (pos, msg) = Error.errorAt(errStrm, (pos, pos), [msg])

  (* error function for parser *)
    local
      datatype add_or_delete = datatype AntlrRepair.add_or_delete
      fun tokToString ADD (MinMLTokens.INT _) = "<int>"
        | tokToString ADD (MinMLTokens.FLOAT _) = "<real>"
        | tokToString ADD (MinMLTokens.CHAR _) = "<char>"
        | tokToString ADD (MinMLTokens.STRING _) = "<string>"
        | tokToString ADD (MinMLTokens.TYVAR _) = "<tyvar>"
        | tokToString ADD (MinMLTokens.NAME _) = "<id>"
        | tokToString ADD (MinMLTokens.QNAME _) = "<qualified-id>"
        | tokToString _ (MinMLTokens.INT n) = IntInf.toString n
        | tokToString _ (MinMLTokens.FLOAT f) = FloatLit.toString f
        | tokToString _ (MinMLTokens.CHAR c) = concat["#\"", Char.toString c, "\""]
        | tokToString _ (MinMLTokens.STRING s) = concat["\"", String.toString s, "\""]
        | tokToString _ (MinMLTokens.TYVAR tv) = Atom.toString tv
        | tokToString _ (MinMLTokens.NAME id) = Atom.toString id
        | tokToString _ (MinMLTokens.QNAME(prefix, id)) =
            String.concatWithMap "." Atom.toString (prefix @ [id])
        | tokToString _ tok = MinMLTokens.toString tok
    in
    val parseErr = Error.parseError tokToString
    end

  (* parse a file, returning a parse tree *)
    fun parseFile (errStrm, file) = let
          fun get () = TextIO.input file
          val lexer = MinMLLex.lex (Error.sourceMap errStrm) (lexErr errStrm)
          in
            case MinMLParser.parse lexer (MinMLLex.streamify get)
             of (SOME pt, _, []) => (TextIO.closeIn file; SOME pt)
              | (_, _, errs) => (
                  TextIO.closeIn file;
                  List.app (parseErr errStrm) errs;
                  NONE)
            (* end case *)
          end

  end
