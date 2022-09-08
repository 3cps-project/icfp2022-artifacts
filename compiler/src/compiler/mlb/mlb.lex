(* mlb.lex
 *
 * COPYRIGHT (c) 2021 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * MLULex specification for MLB.
 *)


%name MLBLex;

%arg (lexErr);

%defs (

    structure T = MLBTokens

  (* some type lex_result is necessitated by ml-ulex *)
    type lex_result = T.token

  (* the depth int ref will be used for keeping track of comment depth *)
    val depth = ref 0

  (* list of string fragments to concatenate *)
    val buf : string list ref = ref []

  (* add a string to the buffer *)
    fun addStr s = (buf := s :: !buf)

  (* make a string from buf *)
    fun mkString () = let
	  val s = String.concat(List.rev(!buf))
	  in
	    buf := [];
            T.STRING s
	  end

  (* eof : unit -> lex_result *)
  (* ml-ulex requires this as well *)
    fun eof () = T.EOF

  (* keyword lookup table *)
    local
      val find =
	  let val tbl = AtomTable.mkTable (17, Fail "keywords")
	      fun ins (id, tok) = AtomTable.insert tbl (Atom.atom id, tok)
	  in
	      app ins [
	        ("bas",         T.KW_bas),
	        ("basis",       T.KW_basis),
		("in",		T.KW_in),
		("let",		T.KW_let),
		("end",         T.KW_end),
		("and",         T.KW_and),
		("open",        T.KW_open),
		("local",       T.KW_local),
		("signature",   T.KW_signature),
		("functor",     T.KW_functor),
		("structure",   T.KW_structure),
		("ann",         T.KW_ann)
	      ];
	      AtomTable.find tbl
	  end
    in
  (* return either a keyword token or a NAME token *)
    fun idToken id =
	let val ida = Atom.atom id
	in
	    case find ida
	     of NONE => T.NAME ida
	      | SOME kw => kw
	end
    end
);

%states INITIAL STRING COMMENT;

%let letter = [a-zA-Z];
%let digit = [0-9];

(* SML-style alpha IDs *)
%let idchar = {letter}|{digit}|"_"|"'";
%let id = {letter}{idchar}*;

(* path variable occurrences; note that path vars are always upper-case *)
%let pvarletter = [A-Z_];
%let pvarchar = {pvarletter}|{digit};
%let pathvar = "$("{pvarletter}{pvarchar}*")";

(* a path arc is the concatenation of path variables and file characters;
 * note that the arcs "." and ".." are included.
 *)
%let filechar = {letter}|{digit}|"_"|"-"|".";
%let arc = ({pathvar}|{filechar})+;
%let relpath = ({arc}"/")*;
%let abspath = "/"{relpath};
%let path = {relpath}|{abspath};
%let file = {path}{arc};

%let esc = "\\"[abfnrtv\\\"]|"\\"{digit}{digit}{digit};
%let sgood = [\032-\126]&[^\"\\]; (* sgood means "characters good inside strings" *)
%let ws = " "|[\t\n\v\f\r];

<INITIAL>{ws}	=> (skip ());
<INITIAL>"="	=> (T.EQ);
<INITIAL>";"	=> (T.SEMI);
<INITIAL>{id}	=> (idToken yytext);
<INITIAL>{file} => (T.PATH yytext);
<INITIAL>"(*"	=> (YYBEGIN COMMENT; depth := 1; continue());

<INITIAL> "\""	=> (YYBEGIN STRING; skip());

<STRING>{esc}	=> (addStr(valOf(String.fromString yytext)); continue());
<STRING>{sgood}+
		=> (addStr yytext; continue());
<STRING>"\""	=> (YYBEGIN INITIAL; mkString());
<STRING>"\\".	=> (lexErr(yypos, [
			"bad escape character `", String.toString yytext,
			"' in string literal"
		      ]);
		    continue());
<STRING>.	=> (lexErr(yypos, [
			"bad character `", String.toString yytext,
			"' in string literal"
		      ]);
		    continue());

<COMMENT> "(*" => (
	depth := !depth + 1;
	continue());
<COMMENT> "*)" => (
	depth := !depth - 1;
        if (!depth = 0) then YYBEGIN INITIAL else ();
	continue ());
<COMMENT> .|"\n" => (continue ());
