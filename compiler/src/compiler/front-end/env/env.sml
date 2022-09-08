(* env.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * TODO: support import/export of environments
 *)

structure Env : sig

    type t

    type struct_env = StructEnv.t

    datatype ty_def
      = TyDef of Types.ty_scheme
      | TyCon of Types.tycon

    datatype val_bind
      = Var of Var.t
      | Overload of Types.ty_scheme * Var.t list

  (* initial environment *)
    val env0 : t

  (* support for structure declarations *)
    val structBegin : t -> t
    val structEnd : t * BindTree.strid -> StrId.t * struct_env * t
    val findStruct : t * BindTree.strid -> (StrId.t * struct_env) option
    val insertStruct : t * BindTree.strid * StrId.t * struct_env -> t

  (* support for local declarations *)
    val localBegin : t -> t
    val localIn : t -> t
    val localEnd : t -> t

    val findTyVar : t * BindTree.tyvar -> Types.tyvar option
    val insertTyVar : t * BindTree.tyvar * Types.tyvar -> t

    val findTyId : t * BindTree.tycon -> ty_def option
    val insertTyDef : t * BindTree.tycon * Types.ty_scheme -> t
    val insertTyCon : t * BindTree.tycon * Types.tycon -> t

    val findDCon : t * BindTree.conid -> Types.dcon option
    val findVar : t * BindTree.varid -> val_bind option
    val insertDCon : t * BindTree.conid * Types.dcon -> t
    val insertVar : t * BindTree.varid * Var.t -> t

    val varsFromList : t * (BindTree.varid * Var.t) list -> t

  (* structure environments *)
    val findStruct' : struct_env * BindTree.strid -> (StrId.t * struct_env) option
    val findTyId' : struct_env * BindTree.tycon -> ty_def option
    val findDCon' : struct_env * BindTree.conid -> Types.dcon option
    val findVar' : struct_env * BindTree.varid -> val_bind option

  (* debugging *)
    val dump : TextIO.outstream * string * t -> unit

  end = struct

    structure BT = BindTree
    structure StrMap = EnvRep.StrMap
    structure TycMap = EnvRep.TycMap
    structure TVMap = EnvRep.TVMap
    structure ConMap = EnvRep.ConMap
    structure VarMap = EnvRep.VarMap

    datatype t = datatype EnvRep.env
    datatype struct_env = datatype EnvRep.struct_env
    datatype env_stk = datatype EnvRep.env_stk
    datatype ty_def = datatype EnvRep.ty_def
    datatype val_bind = datatype EnvRep.val_bind

    val env0 = let
          val {tcMap, cMap, vMap} = Basis.env0
          val extEnv = SE{strMap = StrMap.empty, tcMap = tcMap, cMap = cMap, vMap = vMap}
          in
            E{ stk = Top{ ext = extEnv, top = StructEnv.empty }, tvMap = TVMap.empty }
          end

  (* generic lookup function that searches an environment stack *)
    fun lookup find = let
          fun look (Top{ext, top}, x) = (case find (top, x)
                 of NONE => find (ext, x)
                  | something => something
                (* end case *))
            | look (Str(senv, rest), x) = (case find(senv, x)
                 of NONE => look (rest, x)
                  | something => something
                (* end case *))
            | look (Loc1(senv, rest), x) = (case find(senv, x)
                 of NONE => look (rest, x)
                  | something => something
                (* end case *))
            | look (Loc2(menv1, menv2, rest), x) = (case find(menv2, x)
                 of NONE => (case find(menv1, x)
                       of NONE => look (rest, x)
                        | something => something
                      (* end case *))
                  | something => something
                (* end case *))
          in
            fn (E{stk, ...}, x) => look (stk, x)
          end

  (* map `f` over the current `struct_env` *)
    fun map (f : struct_env -> struct_env) = let
          fun mapf (Top{ext, top}) = Top{ext=ext, top=f top}
            | mapf (Str(senv, rest)) = Str(f senv, rest)
            | mapf (Loc1(senv, rest)) = Loc1(f senv, rest)
            | mapf (Loc2(menv1, menv2, rest)) = Loc2(menv1, f menv2, rest)
          in
            mapf
          end

  (* generic insertion function *)
    fun insert ins (E{stk, tvMap}, x, y) =
          E{stk = map (fn senv => ins(senv, x, y)) stk, tvMap = tvMap}

  (* merge a module environment into the top of the stack *)
    fun merge (stk, SE menv2) = let
          fun merge' (SE menv1) = SE{
                  strMap = StrMap.unionWith #2 (#strMap menv1, #strMap menv2),
                  tcMap = TycMap.unionWith #2 (#tcMap menv1, #tcMap menv2),
                  cMap = ConMap.unionWith #2 (#cMap menv1, #cMap menv2),
                  vMap = VarMap.unionWith #2 (#vMap menv1, #vMap menv2)
                }
          in
            map merge' stk
          end

    val emptySE = StructEnv.empty

  (* support for structure declarations *)
    fun structBegin (E{stk, ...}) = E{stk = Str(emptySE, stk), tvMap = TVMap.empty}
    fun structEnd (E{stk, ...}, id) = (case stk
           of Str(senv, rest) => let
                val id' = StrId.new id
                val env = E{
                        stk = map
                          (fn (SE{strMap, tcMap, cMap, vMap}) => SE{
                                strMap = StrMap.insert(strMap, id, (id', senv)),
                                tcMap = tcMap, cMap = cMap, vMap = vMap
                              })
                            rest,
                        tvMap = TVMap.empty
                      }
                in
                  (id', senv, env)
                end
            | _ => raise Fail "Env.structEnd: bogus environment"
          (* end case *))

    local
      val insertStruct' = insert (fn (SE{strMap, tcMap, cMap, vMap}, id, item) => SE{
              strMap = StrMap.insert(strMap, id, item),
              tcMap = tcMap, cMap = cMap, vMap = vMap
            })
    in
    fun insertStruct (senv, id, id', senv') = insertStruct' (senv, id, (id', senv'))
    end (* local *)

  (* structure-environment operations *)
    val findStruct' = StructEnv.findStruct
    val findTyId' = StructEnv.findTyId
    val findDCon' = StructEnv.findDCon
    val findVar' = StructEnv.findVar

  (* support for local declarations *)
    fun localBegin (E{stk, ...}) = E{stk = Loc1(emptySE, stk), tvMap = TVMap.empty}
    fun localIn (E{stk, ...}) = (case stk
           of Loc1(senv, rest) => E{stk = Loc2(senv, emptySE, rest), tvMap = TVMap.empty}
            | _ => raise Fail "Env.localIn: bogus environment"
          (* end case *))
    fun localEnd (E{stk, ...}) = (case stk
           of Loc2(_, senv, rest) => E{stk = merge(rest, senv), tvMap = TVMap.empty}
            | _ => raise Fail "Env.localEnd: bogus environment"
          (* end case *))

    fun findTyVar (E{tvMap, ...}, id) = TVMap.find (tvMap, id)
    fun insertTyVar (E{stk, tvMap}, id, tv) = E{ stk = stk, tvMap = TVMap.insert(tvMap, id, tv) }
    fun tyvsFromList (E{stk, tvMap}, binds) = E{
            stk = stk,
            tvMap = List.foldl
                (fn ((id, tyv), tvMap) => TVMap.insert(tvMap, id, tyv))
                  tvMap binds
          }

    val findStruct = lookup findStruct'

    val findTyId = lookup findTyId'
    val insertTyDef = insert (fn (SE{strMap, tcMap, cMap, vMap}, id, tyScm) => SE{
            strMap = strMap,
            tcMap = TycMap.insert(tcMap, id, TyDef tyScm),
            cMap = cMap,
            vMap = vMap
          })
    val insertTyCon = insert (fn (SE{strMap, tcMap, cMap, vMap}, id, tyc) => SE{
            strMap = strMap,
            tcMap = TycMap.insert(tcMap, id, TyCon tyc),
            cMap = cMap,
            vMap = vMap
          })

    val findDCon = lookup findDCon'
    val findVar = lookup findVar'
    val insertDCon = insert (fn (SE{strMap, tcMap, cMap, vMap}, id, dc) => SE{
            strMap = strMap,
            tcMap = tcMap,
            cMap = ConMap.insert(cMap, id, dc),
            vMap = vMap
          })
    val insertVar = insert (fn (SE{strMap, tcMap, cMap, vMap}, id, x) => SE{
            strMap = strMap,
            tcMap = tcMap,
            cMap = cMap,
            vMap = VarMap.insert(vMap, id, Var x)
          })

    fun varsFromList (E{stk, tvMap}, binds) = E{
            stk = map (fn (SE{strMap, tcMap, cMap, vMap}) => SE{
                strMap = strMap,
                tcMap = tcMap,
                cMap = cMap,
                vMap = List.foldl (fn ((x, x'), vm) => VarMap.insert(vm, x, Var x')) vMap binds
              }) stk,
            tvMap = tvMap
          }

  (* debugging *)
    fun prIndent (outS, 0) = ()
      | prIndent (outS, n) = (print "  "; prIndent(outS, n-1))

    fun prStructEnv (outS, indent, prefix, strEnv) = let
          fun pr s = TextIO.output(outS, s)
          fun prLn (indent, s) = (prIndent (outS, indent); pr(concat s); pr "\n")
          fun prBind key2s prItem indent (id, item) = (
                prIndent (outS, indent);
                pr (key2s id ^ " ==> ");
                prItem item)
          fun prTyc _ = pr "...\n"
          fun prCon x = pr "...\n"
          fun prVal x = pr "...\n"
          fun prStr indent (SE{strMap, tcMap, cMap, vMap}) = (
                pr "STRUCT\n";
                  StrMap.appi
                    (prBind BT.StrId.nameOf (prStr (indent+2) o #2) (indent+1))
                      strMap;
                  TycMap.appi (prBind BT.TycId.nameOf prTyc (indent+1)) tcMap;
                  ConMap.appi (prBind BT.ConId.nameOf prCon (indent+1)) cMap;
                  VarMap.appi (prBind BT.VarId.nameOf prVal (indent+1)) vMap;
                prLn (indent, ["END"]))
          in
            prIndent (outS, indent); pr prefix;
            prStr indent strEnv
          end

    fun dump (outS, msg, E{stk, tvMap}) = let
          fun pr s = TextIO.output(outS, s)
          fun dump' (Top{ext, top}) = (
                prIndent(outS, 1); pr "**** Top ****\n";
                prStructEnv (outS, 2, "ext = ", ext);
                prStructEnv (outS, 2, "top = ", top))
            | dump' (Str(strEnv, rest)) = (
                prIndent(outS, 1); pr "**** Str ****\n";
                prStructEnv (outS, 2, "strEnv = ", strEnv);
                dump' rest)
            | dump' (Loc1(strEnv, rest)) = (
                prIndent(outS, 1); pr "**** Loc1 ****\n";
                prStructEnv (outS, 2, "strEnv = ", strEnv);
                dump' rest)
            | dump' (Loc2(strEnv1, strEnv2, rest)) = (
                prIndent(outS, 1); pr "**** Loc2 ****\n";
                prStructEnv (outS, 2, "strEnv1 = ", strEnv1);
                prStructEnv (outS, 2, "strEnv2 = ", strEnv2);
                dump' rest)
          in
            pr (msg ^ " [\n");
            dump' stk;
            pr (concat [
                "  tvMap = {",
                String.concatWithMap "," BT.TyVar.toString (TVMap.listKeys tvMap),
                "}\n"
              ]);
            pr "]\n"
          end

  end
