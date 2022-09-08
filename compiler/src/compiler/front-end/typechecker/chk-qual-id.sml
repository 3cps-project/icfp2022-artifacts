(* chk-qual-id.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure ChkQualId : sig

  (* resolve a qualified ID to a module environment and the base ID.  The
   * possible results are as follows:
   *
   *    `NONE`                  -- there was an unknown structure in the path
   *                               This situation only happens when there was
   *                               an error during Binding analysis, so the
   *                               error was already reported
   *    `SOME(NONE, id)`        -- there was no path (i.e., an unqualified ID)
   *    `SOME(SOME me, id)`     -- the path resolved to a module with environment `me`
   *)
    val check : Context.t * 'a BindTree.qualid -> (StructEnv.t option * 'a) option

  (* check a qualified structure ID *)
    val checkStrId : Context.t * BindTree.strid BindTree.qualid
          -> (StrId.t * StructEnv.t) option

  end = struct

    structure C = Context

  (* error reporting *)
    datatype token = datatype TypeError.token
    val error = Context.error

    fun chkPath (cxt, strId, rest) = (case C.findStruct(cxt, strId)
           of SOME(strId', modEnv) => let
                fun chk (strId', modEnv, []) = SOME(strId', modEnv)
                  | chk (strId', modEnv, strId::rest) = (
                      case Env.findStruct'(modEnv, strId)
                       of SOME(strId', modEnv) => chk (strId', modEnv, rest)
                        | NONE => NONE
                      (* end case *))
                in
                  chk (strId', modEnv, rest)
                end
            | NONE => NONE
          (* end case *))

    fun check (cxt, ([], id)) = SOME(NONE, id)
      | check (cxt, (strId::rest, id)) = (case chkPath(cxt, strId, rest)
           of SOME(_, modEnv) => SOME(SOME modEnv, id)
            | NONE => NONE
          (* end case *))

    fun checkStrId (cxt, ([], id)) = (case C.findStruct(cxt, id)
           of NONE => NONE
            | someEnv => someEnv
          (* end case *))
      | checkStrId (cxt, (strId::rest, id)) = chkPath(cxt, strId, rest @ [id])

  end
