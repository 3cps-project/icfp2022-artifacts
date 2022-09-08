(* call-webs.sml
 *
 * The data structure for managing web information 
 *)

signature WEB_INNER = sig
    type t
    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
end

functor Webs (structure Const : WEB_INNER
              structure Deconst : WEB_INNER) (* : sig

  structure CS = Const.Set
  structure DS = Deconst.Set
  structure CM = Const.Map
  structure DM = Deconst.Map

  type web = {consts : CS.set,
              deconsts : DS.set,
              unknown_const : bool,
              unknown_deconst : bool}

  type t

  val initial : {consts : const list,
                 deconsts : deconst list} -> t

  val add_unknown_const : t * {const : const} -> t
  val add_unknown_deconst : t * {deconst : deconst} -> t

  val add : t * {const : const, deconst : deconst} -> t

  val allConst : t * deconst -> CS.set
  val allDeconst : t * const -> DS.set

  val all : t -> web list
(*
  val maps : t -> {const_map : (DS.set * bool) CM.map, 
                     deconst_map : (CS.set * bool) DM.map}
*)
  val fromMaps : {const_map : (DS.set * bool) CM.map,
                    dconst_map : (CS.set * bool) DM.map} -> t

end *) = struct

  structure CS = Const.Set
  structure DS = Deconst.Set
  structure CM = Const.Map
  structure DM = Deconst.Map

  type web = {consts : CS.set,
              deconsts : DS.set,
              unknown_const : bool,
              unknown_deconst : bool}

  type t = web list

  val empty_web = {consts = CS.empty,
                   deconsts = DS.empty,
                   unknown_const = false,
                   unknown_deconst = false}

  fun initial {consts, deconsts} = let
      val initial_webs = []
      val initial_webs =
          List.foldl (fn (const, acc) =>
                         {deconsts=DS.empty, consts=CS.singleton const, 
                          unknown_deconst=false, unknown_const=false} :: acc)
                     initial_webs consts
      val initial_webs =
          List.foldl (fn (deconst, acc) =>
                         {deconsts=DS.singleton deconst, consts=CS.empty, 
                          unknown_deconst=false, unknown_const=false} :: acc)
                     initial_webs deconsts
  in initial_webs end

  fun with_deconsts ({deconsts, consts, unknown_deconst, unknown_const}, deconsts') =
      {deconsts=deconsts', consts=consts, unknown_deconst=unknown_deconst, unknown_const=unknown_const}
  fun with_consts ({deconsts, consts, unknown_deconst, unknown_const}, consts') =
      {deconsts=deconsts, consts=consts', unknown_deconst=unknown_deconst, unknown_const=unknown_const}
  fun with_unknown_deconst ({deconsts, consts, unknown_deconst, unknown_const}, unknown_deconst') =
      {deconsts=deconsts, consts=consts, unknown_deconst=unknown_deconst', unknown_const=unknown_const}
  fun with_unknown_const ({deconsts, consts, unknown_deconst, unknown_const}, unknown_const') =
      {deconsts=deconsts, consts=consts, unknown_deconst=unknown_deconst, unknown_const=unknown_const'}

  fun add_unknown_const (webs : t, {deconst=deconst}) = let
      fun search webs =
          case webs
           of [] => [{deconsts=DS.singleton deconst, consts=CS.empty, unknown_deconst=false, unknown_const=true}]
            | (web : web) :: rst =>
              if DS.member (#deconsts web, deconst)
              then let
                  val web = with_unknown_const (web, true)
              in web :: rst end
              else web :: (search rst)
  in search webs end

  fun add_unknown_deconst (webs : t, {const=const}) = let
      fun search webs =
          case webs
           of [] => [{deconsts=DS.empty, consts=CS.singleton const, unknown_deconst=true, unknown_const=false}]
            | (web : web) :: rst =>
              if CS.member (#consts web, const)
              then let
                  val web = with_unknown_deconst (web, true)
              in web :: rst end
              else web :: (search rst)
  in search webs end

  fun add (lst, {deconst=deconst : Deconst.t, const=const : Const.t}) = let
      fun aux (lst, deconst_web_opt, const_web_opt, acc) =
          case lst 
           of [] => let
               val acc = List.rev acc
           in case (deconst_web_opt, const_web_opt)
               of (SOME deconst_web, SOME const_web) => let
                   val deconsts = DS.union (#deconsts deconst_web, #deconsts const_web)
                   val consts = CS.union (#consts deconst_web, #consts const_web)
                   val unknown_deconst = (#unknown_deconst deconst_web) orelse (#unknown_deconst const_web)
                   val unknown_const = (#unknown_const deconst_web) orelse (#unknown_const const_web)
                   val web = {deconsts=deconsts,
                              consts=consts,
                              unknown_deconst=unknown_deconst,
                              unknown_const=unknown_const}
               in web :: acc end
                | (NONE, SOME const_web) => let
                    val web = with_deconsts (const_web, DS.add (#deconsts const_web, deconst))
                in web :: acc end
                | (SOME deconst_web, NONE) => let
                    val web = with_consts (deconst_web, CS.add (#consts deconst_web, const))
                in web :: acc end
                | (NONE, NONE) => let
                    val web = {deconsts=DS.singleton deconst,
                               consts=CS.singleton const,
                               unknown_deconst=false,
                               unknown_const=false}
                in web :: acc end
           end
            | web :: rst =>
              case (DS.member (#deconsts web, deconst), CS.member (#consts web, const))
               of (true, true) => lst @ (List.rev acc) (* deconst, const is already in the same web *)
                | (false, true) => aux (rst, deconst_web_opt, SOME web, acc) (* assert: deconst_set_opt = NONE *)
                | (true, false) => aux (rst, SOME web, const_web_opt, acc) (* assert: const_set_opt = NONE *)
                | (false, false) => aux (rst, deconst_web_opt, const_web_opt, web :: acc)
  in aux (lst, NONE, NONE, []) end

  fun allConsts (webs : t, {deconst=deconst : Deconst.t}) =
      case webs
       of [] => CS.empty
        | web :: rst =>
          if DS.member (#deconsts web, deconst)
          then #consts web
          else allConsts (rst, {deconst=deconst})
                       
  fun allDeconsts (webs : t, {const=const : Const.t}) =
      case webs
       of [] => DS.empty
        | web :: rst =>
          if CS.member (#consts web, const)
          then #deconsts web
          else allDeconsts (rst, {const=const})

  fun all (webs) = webs

  fun fromMaps {const_map, deconst_map} = let
      val consts = CM.foldli (fn (x, _, acc) => x :: acc) [] const_map
      val deconsts = DM.foldli (fn (x, _, acc) => x :: acc) [] deconst_map
      val webs = initial {consts=consts, deconsts=deconsts}
      val webs = CM.foldli (fn (x, (ys, unknown), webs) => let
                                val webs = DS.foldl (fn (y, webs) => add (webs, {const=x, deconst=y})) webs ys
                                val webs = if unknown then add_unknown_deconst (webs, {const=x}) else webs
                            in webs end)

                           webs const_map
      val webs = DM.foldli (fn (y, (xs, unknown), webs) => let
                                val webs = CS.foldl (fn (x, webs) => add (webs, {const=x, deconst=y})) webs xs
                                val webs = if unknown then add_unknown_const (webs, {deconst=y}) else webs
                            in webs end)
                           webs deconst_map
  in webs end

end


structure LLWebs = Webs (structure Const = Label
                         structure Deconst = Label)
