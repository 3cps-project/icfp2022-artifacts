(* type-error.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure TypeError : sig

    datatype token
      = S of string                     (* literal string *)
      | ID of string                    (* identifier; will print in single quotes ('...') *)
      | V of AST.var                    (* AST variable; will print name in single
                                         * quotes ('...')
                                         *)
      | TY of Types.ty                  (* type expression *)
      | PAT of AST.pat                  (* pattern used as counter example *)
      | LN of Error.location            (* source-code location; prints as a line number *)
      | LNS of Error.location list      (* source-code locations *)

  (* format a qualified ID as a `ID` *)
    val qualId : ('a -> string) -> 'a BindTree.qualid -> token

  (* format an error message *)
    val format : token list -> string list

  end = struct

    structure TU = TypeUtil

    datatype token
      = S of string | ID of string
      | V of AST.var | TY of Types.ty
      | PAT of AST.pat
      | LN of Error.location
      | LNS of Error.location list

    fun qualId nameOf ([], id) = ID(nameOf id)
      | qualId nameOf (path, id) =
          ID(String.concat[String.concatWithMap "." BindTree.StrId.nameOf path, ".", nameOf id])

    fun tok2str (S s) = s
      | tok2str (ID id) = concat["'", id, "'"]
      | tok2str (V x) = concat["'", Var.nameOf x, "'"]
      | tok2str (TY ty) = TU.toString ty
      | tok2str (PAT p) = "<pat>" (* FIXME *)
      | tok2str (LN loc) = Error.fmt ("line %l", "<unknown>") loc
      | tok2str (LNS locs) = let
          fun lineNum Error.UNKNOWN = NONE
            | lineNum (Error.LOC{l1, ...}) = SOME l1
          val lns = List.mapPartial lineNum locs
          fun getSpans ([], l) = List.rev l
            | getSpans (n::ns, l) = let
                fun getSpan ([], n1, n2) = List.rev((n1, n2)::l)
                  | getSpan (n::ns, n1, n2) = if (n = n2+1)
                      then getSpan (ns, n1, n)
                      else getSpans (ns, (n1, n2)::l)
                in
                  getSpan (ns, n, n)
                end
          in
            case getSpans (List.mapPartial lineNum locs, [])
             of [] => "<unknown>"
              | [(n1, n2)] => if (n1 = n2)
                  then "line " ^ Int.toString n1
                  else concat["lines ", Int.toString n1, "-", Int.toString n2]
              | sp1::sps => let
                  fun fmtSpan (n1, n2) = if (n1 = n2)
                        then Int.toString n1
                        else concat[Int.toString n1, "-", Int.toString n2]
                  fun fmt [] = raise Match
                    | fmt [sp] = [", and", fmtSpan sp]
                    | fmt (sp::sps) = fmtSpan sp :: ", " :: fmt sps
                  in
                    String.concat("lines " :: fmt sps)
                  end
            (* end case *)
          end

    fun format toks = List.map tok2str toks

  end
