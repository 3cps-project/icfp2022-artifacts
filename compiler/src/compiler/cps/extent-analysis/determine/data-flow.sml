(* data-flow.sml
 *
 * Determines data flow information from the given state space,
 * i.e. which data structures flow to which match sites
 *)

structure DetermineDataFlow :> DETERMINE_INFO =
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

      fun handle_config (xi, (dataToMatch, matchToData)) = let
          val (exp as C.EXP(lab_e,e), env, envK, tenv, aP) = Config.get xi
      in case e
           of C.SWITCH (arg, pats) => let
               val d = U.evalLVar (arg, env, store)
               fun handle_data (data, (dataToMatch, matchToData)) = let
                   val (lab_data, _, _) = DataValue.get data
                   val dataToMatch = addMap (dataToMatch, lab_data, lab_e)
                   val matchToData = addMap (matchToData, lab_e, lab_data)
               in (dataToMatch, matchToData) end
               fun handle_unknown matchToData = let
                   val matchToData = addUnknown (matchToData, lab_e)
               in matchToData end
               val (dataToMatch, matchToData) = Value.fold_dvs handle_data (dataToMatch, matchToData) d
               val matchToData = Value.fold_unknown handle_unknown matchToData d
               in (dataToMatch, matchToData) end
            | _ => (dataToMatch, matchToData)
      end
      fun handle_ld_passed_to_unknown (ld, lamToCall) =
          if LM.inDomain (lamToCall, ld)
          then let
              val lamToCall = addUnknown (lamToCall, ld)
          in lamToCall end
          else lamToCall
      val ld_passed_to_unknown = #ldata_passed_to_unknown state_space
      fun init lst = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lst
      val dataToMatch = init (PInfo.datas pinfo)
      val matchToData = init (PInfo.matches pinfo)
      val (dataToMatch, matchToData) =
            Config.Set.foldl handle_config (dataToMatch, matchToData) configs
      val dataToMatch = Label.Set.foldl
            handle_ld_passed_to_unknown dataToMatch ld_passed_to_unknown
      val ainfo = AInfo.with_dataInfo (ainfo, {dataToMatch=dataToMatch, matchToData=matchToData})
  in ainfo end

end
