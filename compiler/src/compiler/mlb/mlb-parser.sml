(* mlb-parser.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Parser for the MLB language.
 *)

structure MLBParser : sig

  (* parse a MLB specification from the input stream and return the parse tree
   * if successful and `NONE` if there are syntax errors
   *)
    val parse : (Error.err_stream * TextIO.instream) -> MLBParseTree.mlb option

  end = struct

    structure Tok = MLBTokens

  (* glue together the lexer and parser *)
    structure MLBParser = MLBParseFn(MLBLex)

  (* error function for lexers *)
    fun lexErr errStrm (pos, msg) = Error.errorAt(errStrm, (pos, pos), msg)

  (* error function for parsers *)
    local
      datatype add_or_delete = datatype AntlrRepair.add_or_delete
      fun tokToString ADD (Tok.STRING _) = "<string>"
        | tokToString ADD (Tok.PATH _) = "<path>"
        | tokToString ADD (Tok.NAME _) = "<id>"
        | tokToString _ (Tok.STRING s) = concat["\"", String.toString s, "\""]
        | tokToString _ (Tok.PATH p) = p
        | tokToString _ (Tok.NAME id) = Atom.toString id
        | tokToString _ tok = Tok.toString tok
    in
    val parseErr = Error.parseError tokToString
    end

  (* parse a file, returning a parse tree *)
    fun parse (errStrm, inS) = let
	  fun get () = TextIO.input inS
	  val lexer = MLBLex.lex (Error.sourceMap errStrm) (lexErr errStrm)
	  in
	    case MLBParser.parse lexer (MLBLex.streamify get)
	     of (SOME pt, _, []) => SOME pt
	      | (_, _, errs) => (
		  List.app (parseErr errStrm) errs;
		  NONE)
	    (* end case *)
	  end

  end
