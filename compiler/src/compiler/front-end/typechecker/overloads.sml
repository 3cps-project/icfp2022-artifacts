(* overloads.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Support for overload resolution.
 *)

structure Overloads : sig

    type t

    val new : unit -> t

    val addVar : t * Error.span * AST.overload_var ref -> unit

    val resolve : Error.err_stream * t -> unit

  end = struct

    structure Ty = Types
    structure U = Unify

  (* error reporting *)
    datatype token = datatype TypeError.token

    datatype t = OV of (Error.span * AST.overload_var ref) list ref

    val debug = Ctl.debugOverloads
    val say = Log.msg

    fun new () = OV(ref[])

    fun addVar (OV ovlds, span, inst) = ovlds := (span, inst) :: !ovlds

    fun defaultTy Ty.Int = PrimTy.intTy
      | defaultTy Ty.Real = PrimTy.realTy
      | defaultTy Ty.Num = PrimTy.intTy
      | defaultTy Ty.Order = PrimTy.intTy
      | defaultTy Ty.Any = raise Fail "unexpected Any class"

  (* instantiate free meta variables that have a class with the default type for the class *)
    fun instWithDefaults Ty.ErrorTy = ()
      | instWithDefaults (ty as Ty.MetaTy(Ty.MVar{info, ...})) = (case !info
           of Ty.UNIV{cls, ...} => if not(U.unify (ty, defaultTy cls))
                then raise Fail "impossible"
                else ()
            | Ty.INSTANCE ty => instWithDefaults ty
          (* end case *))
      | instWithDefaults (Ty.VarTy _) = ()
      | instWithDefaults (Ty.ConTy(tys, _)) = List.app instWithDefaults tys
      | instWithDefaults (Ty.FunTy(ty1, ty2)) = (
          instWithDefaults ty1; instWithDefaults ty2)
      | instWithDefaults (Ty.TupleTy tys) = List.app instWithDefaults tys

  (* variable at a given type *)
    fun toString x = concat[
            Var.nameOf x, " : ", TypeUtil.fmt {long=true} (Var.monoTypeOf x)
          ]

    fun resolve (errS, OV ovlds) = let
          fun error (span, toks) = Error.errorAt(errS, span, TypeError.format toks)
          val anyChange = ref false
          fun tryVar (span, rc) = (case !rc
                 of AST.Unknown(ty, vl) => let
                      fun isOK v = if U.unifiable(ty, Var.monoTypeOf v)
                            then true
                            else (
                              if (Controls.get debug)
                                then say ["    reject ", toString v,  "\n"]
                                else ();
                              anyChange := true;
                              false)
                      in
                        if (Controls.get debug)
                          then say["  try {", String.concatWithMap "," toString vl, "}\n"]
                          else ();
                        case List.filter isOK vl
                         of [] => (
                              anyChange := true;
                              error(span, [
                                  S "no suitable candidate for overloaded variable '",
                                  S(Var.nameOf(hd vl)), S "'"
                                ]);
                              false)
                          | [x] => (
                              if (Controls.get debug)
                                then say["  pick ", toString x, "\n"]
                                else ();
                              anyChange := true;
                              U.unify (ty, Var.monoTypeOf x);
                              rc := AST.Instance x;
                              false)
                          | vl' => (rc := AST.Unknown(ty, vl'); true)
                       (* end case *)
                      end
                  | _ => false
                (* end case *))
          fun setVarToDefault (span, rc) = (case !rc
                 of AST.Unknown(ty, vl) => instWithDefaults (TypeUtil.prune ty)
                  | _ => ()
                (* end case *))
          fun resolveLp [] = if (Controls.get debug)
                then say ["done\n"]
                else ()
            | resolveLp instances = let
                val _ = anyChange := false
                val instances = List.filter tryVar instances
                in
                  if !anyChange
                    then resolveLp instances
                    else let
                      fun err (span, ref(AST.Unknown(_, x::_))) = error(span, [
                              S "unable to resolve overloading for '",
                              S(Var.nameOf x), S "'"
                            ])
                        | err _ = ()
                      in
                      (* set unresolved types to defaults *)
                        if (Controls.get debug)
                          then say["  try defaults\n"]
                          else ();
                        List.app setVarToDefault instances;
                      (* resolve overloadings with default types *)
                        List.app err (List.filter tryVar instances)
                      end
                end
          in
            if (Controls.get debug)
              then say ["resolve overloads:\n"]
              else ();
            resolveLp (!ovlds)
          end

  end
