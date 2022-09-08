(* context.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Typechecking contexts, which bundle up the error stream, current source location,
 * and environment.
 *)

structure Context : sig

    datatype t = Cxt of {
        errS : Error.err_stream,
        span : Error.span,
        env : Env.t,
        ovlds : Overloads.t
      }

    val setSpan : t * Error.span -> t
    val withMark : t * 'a Error.mark -> t * 'a

  (* if a term is wrapped with a mark, then use it to set the span of
   * the context.  Otherwise, the context is unchanged.
   *)
    val setSpanFromPat : t * BindTree.pat -> t
    val setSpanFromExp : t * BindTree.exp -> t

    val spanToLoc : t * Error.span -> Error.location
    val getSpan : t -> Error.span
    val getLocation : t -> Error.location

    val getEnv : t -> Env.t
    val setEnv : t * Env.t -> t

  (* record a warning message *)
    val warning : t * TypeError.token list -> unit
  (* record an error message *)
    val error : t * TypeError.token list -> unit

  (* support for structure declarations *)
    val structBegin : t -> t
    val structEnd : t * BindTree.strid -> StrId.t * Env.struct_env * t
    val findStruct : t * BindTree.strid -> (StrId.t * Env.struct_env) option
    val insertStruct : t * BindTree.strid * StrId.t * Env.struct_env -> t

  (* support for local declarations *)
    val localBegin : t -> t
    val localIn : t -> t
    val localEnd : t -> t

    val findTyVar : t * BindTree.tyvar -> Types.tyvar option
    val insertTyVar : t * BindTree.tyvar * Types.tyvar -> t

    val findTyId : t * BindTree.tycon -> Env.ty_def option
    val insertTyDef : t * BindTree.tycon * Types.ty_scheme -> t
    val insertTyCon : t * BindTree.tycon * Types.tycon -> t

    val findDCon : t * BindTree.conid -> Types.dcon option
    val findVar : t * BindTree.varid -> Env.val_bind option
    val insertDCon : t * BindTree.conid * Types.dcon -> t
    val insertVar : t * BindTree.varid * Var.t -> t

    val varsFromList : t * (BindTree.varid * Var.t) list -> t

  (* overloading support *)
    val addOverloadVar : t * AST.overload_var ref -> unit
    val resolveOverloads : t -> unit

  end = struct

    structure E = Env

    datatype t = Cxt of {
        errS : Error.err_stream,
        span : Error.span,
        env : E.t,
        ovlds : Overloads.t
      }

    fun setSpan (Cxt{errS, env, ovlds, ...}, span) =
          Cxt{errS=errS, span=span, env=env, ovlds=ovlds}

    fun withMark (cxt, {span, tree}) = (setSpan(cxt, span), tree)

    fun setSpanFromPat (cxt, BindTree.MarkPat{span, ...}) = setSpan(cxt, span)
      | setSpanFromPat (cxt, _) = cxt

    fun setSpanFromExp (cxt, BindTree.MarkExp{span, ...}) = setSpan(cxt, span)
      | setSpanFromExp (cxt, _) = cxt

    fun spanToLoc (Cxt{errS, ...}, span) = Error.location(errS, span)
    fun getSpan (Cxt{span, ...}) = span
    fun getLocation (Cxt{errS, span, ...}) = Error.location(errS, span)

    fun getEnv (Cxt{env, ...}) = env
    fun setEnv (Cxt{errS, span, ovlds, ...}, env) = Cxt{errS=errS, span=span, env=env, ovlds=ovlds}

(* FIXME: the warnings control ought to be part of the Error module *)
    fun warning (Cxt{errS, span, ...}, toks) = if Controls.get Ctl.warnings
          then Error.warningAt(errS, span, TypeError.format toks)
          else ()
    fun error (Cxt{errS, span, ...}, toks) =
          Error.errorAt(errS, span, TypeError.format toks)

    local
      fun appToEnv f (Cxt{errS, span, env, ovlds}) = Cxt{
            errS = errS, span = span, ovlds = ovlds,
            env = f env
          }
    in

    val structBegin = appToEnv E.structBegin

    fun structEnd (Cxt{errS, span, env, ovlds}, id) = let
          val (id', strEnv, env') = E.structEnd(env, id)
handle ex => (Env.dump (TextIO.stdOut, "", env); raise ex)
          in
            (id', strEnv, Cxt{errS = errS, span = span, env = env', ovlds = ovlds})
          end

    val localBegin = appToEnv E.localBegin
    val localIn = appToEnv E.localIn
    val localEnd = appToEnv E.localEnd

    end (* local *)

    local
      fun find f (Cxt{env, ...}, id) = f (env, id)
      fun ins f (Cxt{errS, span, env, ovlds}, id, item) = Cxt{
              errS=errS, span=span,
              env = f(env, id, item),
              ovlds = ovlds
            }
    in
    val findStruct = find E.findStruct
    fun insertStruct (Cxt{errS, span, env, ovlds}, id, id', senv) = Cxt{
            errS=errS, span=span,
            env = E.insertStruct(env, id, id', senv),
            ovlds = ovlds
          }

    val findTyVar = find E.findTyVar
    val insertTyVar = ins E.insertTyVar

    val findTyId = find E.findTyId
    val insertTyDef = ins E.insertTyDef
    val insertTyCon = ins E.insertTyCon

    val findDCon = find E.findDCon
    val findVar = find E.findVar
    val insertDCon = ins E.insertDCon
    val insertVar = ins E.insertVar
    end (* local *)

    fun varsFromList (Cxt{errS, span, env, ovlds}, binds) = Cxt{
            errS = errS, span = span,
            env = E.varsFromList (env, binds),
            ovlds = ovlds
          }

    fun addOverloadVar (Cxt{span, ovlds, ...}, inst) = Overloads.addVar(ovlds, span, inst)

    fun resolveOverloads (Cxt{errS, ovlds, ...}) = Overloads.resolve(errS, ovlds)

  end

