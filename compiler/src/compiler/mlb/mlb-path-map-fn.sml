(* mlb-path-map-fn.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * MLB Path Maps are association lists that map path variables to strings.
 * A path variable is a string that has the form "[A-Z_] ( [A-Z0-9_]* )".
 *)

functor MLBPathMapFn (Err : MLB_ERROR) : sig

  (* the error reporting context *)
    type context = Err.context

  (* a path map, which is a mapping from path map variables to strings *)
    type t

  (* the empty path map *)
    val empty : t

  (* extend a path map by loading variable/value bindings from a file.  If successful,
   * the function returns `SOME pmap`, where `pmap` is the extended path map.  If
   * there is an error, then `NONE` is returned and the error is reported using
   * the `error` callback function.
   *)
    val load : context * string * t -> t option

  (* extend the pathmap with a binding *)
    val extend : t * string * string -> t

  (* resolve a path variable; returns `NONE` if the variable is undefined *)
    val resolveVar : t * string -> string option

  (* the components of a split path *)
    datatype component = PVar of string | Str of substring

  (* split a path into a sequence of substrings and path variables; if there
   * are ill-formed variable occurrences, then the error function is used to
   * report them, and the variables are *not* split out into `PVar` fragments.
   *)
    val split : context * string -> component list

  (* resolve a path by expanding any path variables in the path.  This helper
   * function combines the `split` and `resolve` operations and uses the
   * `error` function to report any undefined variables.
   *)
    val resolve : context * t * string -> string option

  end = struct

    structure SS = Substring
    structure SMap = RedBlackMapFn (
      struct
        type ord_key = string
        val compare = String.compare
      end)

  (* the error reporting context *)
    type context = Err.context

    type t = string SMap.map

    val empty = SMap.empty

    val extend = SMap.insert

  (* variables start with upper-case letters or an underscore *)
    fun isVarStartChr #"_" = true
      | isVarStartChr c = Char.isUpper c

  (* variable characters *)
    fun isVarChr c = isVarStartChr c orelse Char.isDigit c

  (* is a substring a valid variable name? *)
    fun validVar ss = (SS.size ss > 0)
	  andalso isVarStartChr (SS.sub(ss, 0))
	  andalso CharVectorSlice.all isVarChr (SS.slice(ss, 1, NONE))

  (* load a pathmap from a file; returns `NONE` if there is an error processing
   * the file.
   *)
    fun load (cxt, fname, pmap) = if OS.FileSys.access(fname, [OS.FileSys.A_READ])
	  then let
	    val inS = TextIO.openIn fname
	  (* test if the first character of the substring `ss` is `#` *)
	    fun isComment ss = (case SS.getc ss of SOME(#"#", _) => true | _ => false)
	    fun err (lnum, msg) = (
		  Err.errorAt (cxt, lnum, concat msg);
		  NONE)
	  (* read the lines of the path map file; we ignore blank and comment lines *)
	    fun read (lnum, pmap) = (case TextIO.inputLine inS
		   of NONE => SOME pmap
		    | SOME ln => (case SS.tokens Char.isSpace (SS.full ln)
			 of [] => read (lnum+1, pmap) (* blank line *)
			  | [key, value] => if isComment key
			      then read (lnum+1, pmap)
			    else if validVar key
			      then read (lnum+1, extend(pmap, SS.string key, SS.string value))
			      else err (lnum, ["invalid variable name '", SS.string key, "'"])
			  | tok::_ => if isComment tok
			      then read (lnum+1, pmap)
			      else err (lnum, ["invalid input line"])
			(* end case *))
		  (* end case *))

	    in
	      read (1, pmap) before TextIO.closeIn inS
	    end
	  else (
	    Err.error (cxt, concat["file '", fname, "' does not exist or is not readable"]);
	    NONE)

  (* resolve a path variable; returns `NONE` if the variable is undefined *)
    val resolveVar = SMap.find

    datatype component = PVar of string | Str of substring

  (* split a path into a sequence of substrings and path variables *)
    fun split (cxt, path) = let
	(* create a `Str` component from the prefix of the substring `start`
         * that is not part of `ss` and add it to the `frags` list.
	 *)
	  fun mkStr (start, ss, frags) = (case SS.size start - SS.size ss
		 of 0 => frags
		  | n => Str(SS.slice(start, 0, SOME n)) :: frags
		(* end case *))
	  fun scan (ss, start, frags) = (case SS.getc ss
		 of SOME(#"$", ss') => (case scanVar ss'
		       of SOME(x, ss'') =>
			    scan (ss'', ss'', PVar x :: mkStr(start, ss, frags))
			| NONE => scan (ss', start, frags)
		      (* end case *))
		  | SOME(_, ss') => scan (ss', start, frags)
		  | NONE => List.rev frags
		(* end case *))
	  and scanVar ss = (case SS.getc ss
		 of SOME(#"(", varStart) => (case SS.getc varStart
		       of SOME(c, ss'') => if isVarStartChr c
			    then let
			      fun scan ss = (case SS.getc ss
				     of SOME(#")", ss') => let
					  val n = SS.size varStart - SS.size ss
					  val x = SS.string(SS.slice(varStart, 0, SOME n))
					  in
					    SOME(x, ss')
					  end
				      | SOME(c, ss') => if isVarChr c
					  then scan ss'
					  else (
					    Err.error (cxt, concat[
						"invalid character #\"", Char.toString c,
						"\" in variable occurence"
					      ]);
					    NONE)
				      | NONE => (
					    Err.error (cxt, "invalid varible occurence");
					    NONE)
				    (* end case *))
			      in
				scan ss''
			      end
			    else (
			      Err.error (cxt, concat[
				  "invalid initial character #\"", Char.toString c,
				  "\" in variable occurence"
				]);
			      NONE)
			| NONE => (
			    Err.error (cxt, "invalid varible occurence");
			    NONE)
		      (* end case *))
		  | _ => (
		      Err.error (cxt, "invalid varible occurence");
		      NONE)
		(* end case *))
	  val start = SS.full path
	  in
	    scan (start, start, [])
	  end

  (* resolve a path by expanding any path variables in the path.  This helper
   * function combines the `split` and `resolve` operations and uses the
   * `error` function to report any undefined variables.
   *)
    fun resolve (cxt, pmap, path) = let
	(* process the fragments that come from splitting the path (or recursively spliting
	 * the value of variable occurrences).  The list `pvs` is used to detect recursive
	 * uses of variables that would lead to an infinite expansion.
	 *)
	  fun doFrags ([], pvs, bits) = SOME(Substring.concat(rev bits))
	    | doFrags (PVar pv :: pvr, pvs, bits) =
		if List.exists (fn pv' => pv = pv') pvs
		  then (
		    Err.error (cxt, concat ["cycle detected in expansion of '", pv, "'"]);
		    NONE)
		  else (case SMap.find(pmap, pv)
		     of SOME s => doFrags (split(cxt, s) @ pvr, pv::pvs, bits)
		      | NONE => (
			  Err.error (cxt, concat ["undefined path variable '", pv, "'"]);
			  NONE)
		    (* end case *))
	    | doFrags (Str ss :: pvr, pvs, bits) = doFrags (pvr, pvs, ss :: bits)
	  in
	    doFrags (split (cxt, path), [], [])
	  end

  end
