(* minml.lex
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * ml-ulex specification for MinML
 *
 * TODO: hexidecimal literals
 *)

%name MinMLLex;

%arg (lexErr);

%defs(

    structure T = MinMLTokens

  (* some type lex_result is necessitated by ml-ulex *)
    type lex_result = T.token

  (* the depth int ref will be used for keeping track of comment depth *)
    val depth = ref 0

  (* list of string fragments to concatenate *)
    val buf : string list ref = ref []

  (* true when processing a character literal *)
    val charLit = ref false

  (* add a string to the buffer *)
    fun addStr s = (buf := s :: !buf)

  (* make a string from buf *)
    fun mkString () = String.concat(List.rev(!buf)) before buf := []

  (* eof : unit -> lex_result *)
  (* ml-ulex requires this as well *)
    fun eof () = T.EOF

  (* keyword lookup table *)
    local
      val find = let
	    val tbl = AtomTable.mkTable (17, Fail "keywords")
	    fun ins (id, tok) = AtomTable.insert tbl (Atom.atom id, tok)
	    in
	      app ins [
		  ("and",	T.KW_and),
		  ("andalso",	T.KW_andalso),
		  ("as",	T.KW_as),
		  ("case",	T.KW_case),
		  ("datatype",	T.KW_datatype),
		  ("div",	T.KW_div),
		  ("else",	T.KW_else),
		  ("end",	T.KW_end),
		  ("exception",	T.KW_exception),
		  ("fn",	T.KW_fn),
		  ("fun",	T.KW_fun),
		  ("handle",	T.KW_handle),
		  ("if",	T.KW_if),
		  ("in",	T.KW_in),
		  ("let",	T.KW_let),
		  ("local",	T.KW_local),
		  ("mod",	T.KW_mod),
		  ("of",	T.KW_of),
		  ("op",	T.KW_op),
		  ("orelse",	T.KW_orelse),
		  ("raise",	T.KW_raise),
		  ("struct",	T.KW_struct),
		  ("structure",	T.KW_structure),
		  ("then",	T.KW_then),
		  ("type",	T.KW_type),
		  ("val",	T.KW_val)
		];
	      AtomTable.find tbl
	    end
    in
  (* return either a keyword token or a NAME token *)
    fun idToken id = let
	  val ida = Atom.atom id
	  in
	    case find ida
	     of NONE => T.NAME ida
	      | SOME kw => kw
	    (* end case *)
	  end
    end (* local *)

  (* make a qualified ID *)
    fun qualIdToken ss = let
	  val (last::prefix) = List.rev(Substring.fields (fn #"." => true | _ => false) ss)
	  in
	    T.QNAME(List.revMap Atom.atom' prefix, Atom.atom' last)
	  end

    local
      fun cvt radix (s, i) =
	    #1(valOf(IntInf.scan radix Substring.getc (Substring.extract(s, i, NONE))))
    in
    val atoi = cvt StringCvt.DEC
    val xtoi = cvt StringCvt.HEX
    end (* local *)

  (* make a FLOAT token from a substring *)
    fun mkFloat ss = let
          val (isNeg, rest) = (case Substring.getc ss
                 of SOME(#"-", r) => (true, r)
                  | SOME(#"~", r) => (true, r)
                  | _ => (false, ss)
                (* end case *))
          val (whole, rest) = Substring.splitl Char.isDigit rest
          val rest = Substring.triml 1 rest (* remove "." *)
          val (frac, rest) = Substring.splitl Char.isDigit rest
          val exp = if Substring.isEmpty rest
                then 0
                else let
                  val rest = Substring.triml 1 rest (* remove "e" or "E" *)
                  in
                    #1(valOf(IntInf.scan StringCvt.DEC Substring.getc rest))
                  end
          in
            T.FLOAT(FloatLit.float{
                isNeg = isNeg,
                whole = Substring.string whole,
                frac = Substring.string frac,
                exp = exp
              })
          end

);

%states INITIAL STRING COMMENT;

%let letter = [a-zA-Z];
%let dig = [0-9];
%let xdig = [0-9a-fA-F];
%let num = {dig}+;
%let xnum = {xdig}+;
%let idchar = {letter}|{dig}|"_"|"'";
%let id = {letter}{idchar}*;
%let operator = [-+*/@]|"^"|"<="|"<"|">="|">"|":=";
%let tyvarid = "'"{idchar}*;
%let esc = "\\"[abfnrtv\\\"]|"\\"{dig}{dig}{dig};
%let sgood = [\032-\126]&[^\"\\]; (* characters that are allowed inside strings *)
%let ws = " "|[\t\n\v\f\r];

<INITIAL> "("	=> (T.LP);
<INITIAL> ")"	=> (T.RP);
<INITIAL> "["	=> (T.LB);
<INITIAL> "]"	=> (T.RB);
<INITIAL> "<="	=> (T.LTEQ);
<INITIAL> "<"	=> (T.LT);
<INITIAL> ">="	=> (T.GTEQ);
<INITIAL> ">"	=> (T.GT);
<INITIAL> "="	=> (T.EQ);
<INITIAL> "<>"	=> (T.NEQ);
<INITIAL> "::"	=> (T.DCOLON);
<INITIAL> ":="	=> (T.ASSIGN);
<INITIAL> "@"	=> (T.AT);
<INITIAL> "^"	=> (T.HAT);
<INITIAL> "+"	=> (T.PLUS);
<INITIAL> "-"	=> (T.MINUS);
<INITIAL> "*"	=> (T.STAR);
<INITIAL> "/"	=> (T.SLASH);
<INITIAL> "~"	=> (T.TILDE);
<INITIAL> "!"	=> (T.BANG);
<INITIAL> ","	=> (T.COMMA);
<INITIAL> ";"	=> (T.SEMI);
<INITIAL> "|"	=> (T.BAR);
<INITIAL> ":"	=> (T.COLON);
<INITIAL> "->"	=> (T.ARROW);
<INITIAL> "=>"	=> (T.DARROW);
<INITIAL> "_"	=> (T.WILD);

<INITIAL> {id}		=> (idToken yytext);
<INITIAL> {id}("."{id})+
			=> (qualIdToken yysubstr);
<INITIAL> {id}("."{id})*"."{operator}
			=> (qualIdToken yysubstr);
<INITIAL> {tyvarid}	=> (T.TYVAR(Atom.atom yytext));

<INITIAL> {num}		=> (T.INT(atoi(yytext, 0)));
<INITIAL> "~"{num}	=> (T.INT(~(atoi(yytext, 1))));
<INITIAL> "0x"{xnum}	=> (T.INT(xtoi(yytext, 2)));
<INITIAL> "~0x"{xnum}	=> (T.INT(~(xtoi(yytext, 3))));

<INITIAL> "0w"{num}	=> (T.WORD(atoi(yytext, 2)));
<INITIAL> "0wx"{xnum}	=> (T.WORD(xtoi(yytext, 3)));

<INITIAL,PRIMCODE> "~"?{num}"."{num}([eE][+~]?{num})?
			=> (mkFloat yysubstr);
<INITIAL> {ws}		=> (continue ());
<INITIAL> "(*"		=> (YYBEGIN COMMENT; depth := 1; continue());
<INITIAL> "#\""		=> (YYBEGIN STRING; charLit := true; continue());
<INITIAL> "\""		=> (YYBEGIN STRING; charLit := false; continue());

<STRING>{esc}		=> (addStr(valOf(String.fromString yytext)); continue());
<STRING>{sgood}+	=> (addStr yytext; continue());
<STRING>"\""		=> (let
			    val s = mkString()
			    in
			      YYBEGIN INITIAL;
			      if not (!charLit)
				then T.STRING s
			      else if (size s = 1)
				then T.CHAR(String.sub(s, 0))
				else (
				  lexErr(yypos, "invalid character literal");
				(* use the first character of the string *)
				  case Substring.getc(Substring.full s)
				   of SOME(c, _) => T.CHAR c
				    | NONE => T.CHAR #" "
				  (* end case *))
			    end);
<STRING>"\\".		=> (lexErr(yypos, concat[
				"bad escape character `", String.toString yytext,
				"' in string literal"
			      ]);
			    continue());
<STRING>.		=> (lexErr(yypos, concat[
				"bad character `", String.toString yytext,
				"' in string literal"
			      ]);
			    continue());

<INITIAL> . => (
	lexErr(yypos, concat["bad character `", String.toString yytext, "'"]);
	continue());

<COMMENT> "(*" => (
	depth := !depth + 1;
	continue());
<COMMENT> "*)" => (
	depth := !depth - 1;
        if (!depth = 0) then YYBEGIN INITIAL else ();
	continue ());
<COMMENT> .|"\n" => (continue ());
