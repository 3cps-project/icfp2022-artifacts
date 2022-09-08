(* tuple-flow.sml
 *
 * Determines tuple flow information from the given state space,
 * i.e. which tuples flow to which select sites
 *)

structure DetermineTupleFlow :> DETERMINE_INFO =
  struct

  structure C = CPS
  structure PInfo = CPSInformation

  structure AInfo = AnalysisInformation
  structure U = TransitionUtil

  structure LM = Label.Map
  structure LS = Label.Set

  fun determine (analysis_space : AnalysisSpace.t, ainfo) = let
      val pinfo = #pinfo analysis_space
      val state_space = #state_space analysis_space
      val configs = #configs state_space
      val store = #store state_space
      val storeK = #storeK state_space
      val storeP = #storeP state_space

      fun addUnknown (map, x) = let
          val (prev, _) = LM.lookup (map, x)
      in LM.insert (map, x, (prev, true)) end
      fun addMap (map, x, l) = let
          val (prev, unknown) = LM.lookup (map, x)
      in LM.insert (map, x, (LS.add (prev, l), unknown)) end

      fun handle_config (xi, (tupleToSelect, selectToTuple)) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.SELECT (offset, arg, x, e') => let
               val d = U.evalLVar (arg, env, store)
               fun handle_tuple (tuple, (tupleToSelect, selectToTuple)) = let
                   val (lab_tup, _) = TupleValue.get tuple
                   val tupleToSelect = addMap (tupleToSelect, lab_tup, lab_e)
                   val selectToTuple = addMap (selectToTuple, lab_e, lab_tup)
               in (tupleToSelect, selectToTuple) end
               fun handle_unknown selectToTuple = let
                   val selectToTuple = addUnknown (selectToTuple, lab_e)
               in selectToTuple end
               val (tupleToSelect, selectToTuple) = Value.fold_tvs handle_tuple (tupleToSelect, selectToTuple) d
               val selectToTuple = Value.fold_unknown handle_unknown selectToTuple d
               in (tupleToSelect, selectToTuple) end
            | _ => (tupleToSelect, selectToTuple)
      end
      fun handle_ld_passed_to_unknown (ld, lamToCall) =
          if LM.inDomain (lamToCall, ld)
          then let
              val lamToCall = addUnknown (lamToCall, ld)
          in lamToCall end
          else lamToCall
      val ld_passed_to_unknown = #ldata_passed_to_unknown state_space
      fun init lst = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lst
      val tupleToSelect = init (PInfo.tuples pinfo)
      val selectToTuple = init (PInfo.selects pinfo)
      val (tupleToSelect, selectToTuple) =
            Config.Set.foldl handle_config (tupleToSelect, selectToTuple) configs
      val tupleToSelect = Label.Set.foldl
            handle_ld_passed_to_unknown tupleToSelect ld_passed_to_unknown
      val ainfo = AInfo.with_tupleInfo (ainfo, {tupleToSelect=tupleToSelect, selectToTuple=selectToTuple})
  in ainfo end

end
