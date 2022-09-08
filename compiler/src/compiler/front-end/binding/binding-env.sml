(* binding-env.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Environment for the binding check pass over the parse tree.
 *)

structure BindingEnv : sig

    type t

    type struct_env

  (* create the initial top-level environment *)
    val new : unit -> t

  (* support for structure declarations *)
    val structBegin : t -> t
    val structEnd : t * Atom.atom * BindTree.strid -> struct_env * t
    val findStruct : t * Atom.atom -> (BindTree.strid * struct_env) option
    val insertStruct : t * Atom.atom * BindTree.strid * struct_env -> t

  (* get the "signature" from a structure environment *)
    val signOf : struct_env -> BindTree.sign

  (* support for local declarations *)
    val localBegin : t -> t
    val localIn : t -> t
    val localEnd : t -> t

  (* support for tracking implicit type variables, which are bound at value declarations *)
    val pushTyVarScope : t -> unit
    val popTyVarScope : t -> BindTree.tyvar list

    val findTyVar : t * Atom.atom -> BindTree.tyvar option
    val bindTyVar : t * Atom.atom * Error.location -> BindTree.tyvar

    val findTyId : t * Atom.atom -> BindTree.tycon option
    val bindTy : t * Atom.atom * Error.location -> BindTree.tycon * t

    val findConId : t * Atom.atom -> BindTree.conid option
    val findValId : t * Atom.atom -> BindTree.val_bind option
    val insertConId : t * Atom.atom * BindTree.conid -> t

    val tyvsFromList : t * (Atom.atom * BindTree.tyvar) list -> t
    val tycsFromList : t * (Atom.atom * BindTree.tycon) list -> t
    val consFromList : t * (Atom.atom * BindTree.conid) list -> t
    val varsFromList : t * (Atom.atom * BindTree.varid) list -> t

  (* structure environments *)
    val findStruct' : struct_env * Atom.atom -> (BindTree.strid * struct_env) option
    val findTyId' : struct_env * Atom.atom -> BindTree.tycon option
    val findConId' : struct_env * Atom.atom -> BindTree.conid option
    val findValId' : struct_env * Atom.atom -> BindTree.val_bind option

  (* debugging *)
    val dump : TextIO.outstream * string * t -> unit

  end = struct

    structure BT = BindTree
    structure Map = AtomMap

    datatype t = E of {
        stk : env_stk,
        tvMaps : BT.TyVar.t Map.map list ref    (* one map per nested value declaration *)
      }

  (* the environment stack tracks environments for nested structures and
   * `local ... in ... end` declarations.
   *)
    and env_stk
      = Top of {                                (* top-level environment for compilation unit *)
            ext : struct_env,                   (*   - externally defined stuff *)
            top : struct_env                    (*   - locally defined stuff *)
          }
      | Str of struct_env * env_stk             (* structure environment *)
      | Loc1 of struct_env * env_stk            (* environment for processing the local part of
                                                 * a local declaration
                                                 *)
      | Loc2 of struct_env * struct_env * env_stk (* environment for processing the visible part
                                                 * of a local declaration; the first environment
                                                 * is the local part and the second is the public
                                                 * part.
                                                 *)

    and struct_env = SE of {
        strMap : (BT.StrId.t * struct_env) Map.map,     (* structures *)
        tcMap : BT.TycId.t Map.map,                     (* type constructors *)
        vMap : BT.val_bind Map.map                      (* values *)
      }

    val emptySE = SE{strMap = Map.empty, tcMap = Map.empty, vMap = Map.empty}

    fun new () = let
          val {tcMap, vMap} = BasisBinds.env0
          in
            E{
                stk = Top{
                    ext = SE{
                        strMap = Map.empty,
                        tcMap = tcMap,
                        vMap = vMap
                      },
                    top = emptySE
                  },
                tvMaps = ref [Map.empty]
              }
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
    fun insert ins (E{stk, tvMaps}, x, y) =
          E{stk = map (fn senv => ins(senv, x, y)) stk, tvMaps = tvMaps}

  (* merge a module environment into the top of the stack *)
    fun merge (stk, SE menv2) = let
          fun mergeMap (map1, map2) = Map.unionWith #2 (map1, map2)
          fun merge' (SE menv1) = SE{
                  strMap = mergeMap (#strMap menv1, #strMap menv2),
                  tcMap = mergeMap (#tcMap menv1, #tcMap menv2),
                  vMap = mergeMap (#vMap menv1, #vMap menv2)
                }
          in
            map merge' stk
          end

  (* support for structure declarations *)
    fun structBegin (E{stk, tvMaps}) = E{stk = Str(emptySE, stk), tvMaps = tvMaps}
    fun structEnd (E{stk, tvMaps}, id, id') = (case stk
           of Str(senv, rest) => let
                val env = E{
                        stk = map
                          (fn (SE{strMap, tcMap, vMap}) => SE{
                                strMap=Map.insert(strMap, id, (id', senv)),
                                tcMap=tcMap, vMap=vMap
                              })
                            rest,
                        tvMaps = tvMaps
                      }
                in
                  (senv, env)
                end
            | _ => raise Fail "Env.structEnd: bogus environment"
          (* end case *))

    local
      val insertStruct' = insert (fn (SE{strMap, tcMap, vMap}, id, strIdEnv) => SE{
              strMap = Map.insert(strMap, id, strIdEnv),
              tcMap = tcMap,
              vMap = vMap
            })
    in
    fun insertStruct (env, id, id', senv) = insertStruct' (env, id, (id', senv))
    end (* local *)

  (* structure-environment operations *)
    fun findStruct' (SE{strMap, ...}, id) = Map.find(strMap, id)
    fun findTyId' (SE{tcMap, ...}, id) = Map.find(tcMap, id)
    fun findConId' (SE{vMap, ...}, id) = (case Map.find(vMap, id)
           of SOME(BT.Con id') => SOME id'
            | _ => NONE
          (* end case *))
    fun findValId' (SE{vMap, ...}, id) = Map.find(vMap, id)

    fun signOf (SE{strMap, tcMap, vMap}) = let
          val (cons, vals) = let
                fun f (BT.Var x, (cons, vals)) = (cons, x::vals)
                  | f (BT.Con c, (cons, vals)) = (c::cons, vals)
                in
                  Map.foldl f ([], []) vMap
                end
          in
            BT.Sign{
                strs = Map.foldl (fn ((id, _), strs) => id::strs) [] strMap,
                tycs = Map.listItems tcMap,
                cons = cons,
                vals = vals
              }
          end

  (* support for local declarations *)
    fun localBegin (E{stk, tvMaps}) = E{stk = Loc1(emptySE, stk), tvMaps = tvMaps}
    fun localIn (E{stk, tvMaps}) = (case stk
           of Loc1(senv, rest) => E{stk = Loc2(senv, emptySE, rest), tvMaps = tvMaps}
            | _ => raise Fail "Env.localIn: bogus environment"
          (* end case *))
    fun localEnd (E{stk, tvMaps}) = (case stk
           of Loc2(_, senv, rest) => E{stk = merge(rest, senv), tvMaps = tvMaps}
            | _ => raise Fail "Env.localEnd: bogus environment"
          (* end case *))

    fun pushTyVarScope (E{stk, tvMaps}) = tvMaps := Map.empty :: !tvMaps
    fun popTyVarScope (E{stk, tvMaps}) = (case !tvMaps
           of tvMap::tvMapr => (tvMaps := tvMapr; Map.listItems tvMap)
            | _ => raise Fail "impossible: empty tyMaps list"
          (* end case *))

    fun findTyVar (E{tvMaps, ...}, id) = let
          fun find [] = NONE
            | find (tvMap::tvMaps) = (case Map.find (tvMap, id)
                 of NONE => find tvMaps
                  | someTV => someTV
                (* end case *))
          in
            find (!tvMaps)
          end
    fun bindTyVar (E{stk, tvMaps}, id, loc) = (case !tvMaps
           of tvMap :: tvMapr => let
                val id' = BT.TyVar.new(id, loc)
                in
                  tvMaps := Map.insert(tvMap, id, id') :: tvMapr;
                  id'
                end
            | _ => raise Fail "impossible: empty tvMap list"
          (* end case *))
    fun tyvsFromList (E{stk, ...}, binds) = E{
            stk = stk,
            tvMaps = ref [
                List.foldl
                  (fn ((id, tyv), tvMaps) => Map.insert(tvMaps, id, tyv))
                    Map.empty binds
              ]
          }

    val findStruct = lookup findStruct'

    val findTyId = lookup findTyId'
    val insertTy = insert (fn (SE{strMap, tcMap, vMap}, id, id') => SE{
            strMap = strMap,
            tcMap = Map.insert(tcMap, id, id'),
            vMap = vMap
          })
    fun bindTy (env, id, loc) = let
          val id' = BT.TycId.new (id, loc)
          in
            (id', insertTy (env, id, id'))
          end

    val findConId = lookup findConId'
    val findValId = lookup findValId'
    val insertConId = insert (fn (SE{strMap, tcMap, vMap}, id, id') => SE{
            strMap = strMap,
            tcMap = tcMap,
            vMap = Map.insert(vMap, id, BT.Con id')
          })

    fun tycsFromList (E{stk, tvMaps}, binds) = E{
            stk = map (fn (SE{strMap, tcMap, vMap}) => SE{
                strMap = strMap,
                tcMap = List.foldl
                    (fn ((id, tyc), tcMap) => Map.insert(tcMap, id, tyc))
                      tcMap binds,
                vMap = vMap
              }) stk,
            tvMaps = tvMaps
          }

    fun consFromList (E{stk, tvMaps}, binds) = E{
            stk = map (fn (SE{strMap, tcMap, vMap}) => SE{
                strMap = strMap,
                tcMap = tcMap,
                vMap = List.foldl (fn ((x, x'), vm) => Map.insert(vm, x, BT.Con x')) vMap binds
              }) stk,
            tvMaps = tvMaps
          }

    fun varsFromList (E{stk, tvMaps}, binds) = E{
            stk = map (fn (SE{strMap, tcMap, vMap}) => SE{
                strMap = strMap,
                tcMap = tcMap,
                vMap = List.foldl (fn ((x, x'), vm) => Map.insert(vm, x, BT.Var x')) vMap binds
              }) stk,
            tvMaps = tvMaps
          }

  (* debugging *)
    fun prIndent (outS, 0) = ()
      | prIndent (outS, n) = (print "  "; prIndent(outS, n-1))

    fun prStructEnv (outS, indent, prefix, strEnv) = let
          fun pr s = TextIO.output(outS, s)
          fun prLn (indent, s) = (prIndent (outS, indent); pr(concat s); pr "\n")
          fun prBind prItem indent (id, item) = (
                prIndent (outS, indent);
                pr (Atom.toString id ^ " ==> ");
                prItem item)
          fun prTyc x = pr(BT.TycId.toString x ^ "\n")
          fun prVal (BT.Con x) = pr(concat["con ", BT.ConId.toString x, "\n"])
            | prVal (BT.Var x) = pr(concat["var ", BT.VarId.toString x, "\n"])
          fun prStr indent (SE{strMap, tcMap, vMap}) = (
                pr "STRUCT\n";
                  Map.appi
                    (prBind (prStr (indent+2) o #2) (indent+1))
                      strMap;
                  Map.appi (prBind prTyc (indent+1)) tcMap;
                  Map.appi (prBind prVal (indent+1)) vMap;
                prLn (indent, ["END"]))
          in
            prIndent (outS, indent); pr prefix;
            prStr indent strEnv
          end

    fun dump (outS, msg, E{stk, tvMaps}) = let
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
            pr "]\n"
          end

  end
