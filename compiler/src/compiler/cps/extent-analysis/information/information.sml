(* information.sml
 *
 * The data structure for mangaging information produced by the analysis.
 *)

structure AnalysisInformation : sig

  type t

  val info : CPSInformation.t -> CPS.comp_unit -> t

  val lvarExtents : t -> ExtentSet.t LVar.Map.map
  (* val cvarExtents : t -> ExtentSet.t CVar.Map.map *)
  val ldataExtents : t -> ExtentSet.t Label.Map.map

  type tupleInfo = {tupleToSelect : (Label.Set.set * bool) Label.Map.map,
                    selectToTuple : (Label.Set.set * bool) Label.Map.map}
  val tupleInfo : t -> tupleInfo
  val tupleWebs : t -> LLWebs.t

  type dataInfo = {dataToMatch : (Label.Set.set * bool) Label.Map.map,
                   matchToData : (Label.Set.set * bool) Label.Map.map}
  val dataInfo : t -> dataInfo
  val dataWebs : t -> LLWebs.t

  type funInfo = {lamToCall : (Label.Set.set * bool) Label.Map.map,
                  callToLam : (Label.Set.set * bool) Label.Map.map}
  val funInfo : t -> funInfo
  val callWebs : t -> CallWebs.t

  type funKInfo= {lamKToCallK : (Label.Set.set * bool) Label.Map.map,
                  callKToLamK : (Label.Set.set * bool) Label.Map.map}
  val funKInfo : t -> funKInfo
  val callWebsK : t -> CallWebs.t

  val unknownLVars : t -> LVar.Set.set
  val unknownCVars : t -> CVar.Set.set

  val lvarUniquenessCrit : t -> Label.Set.set LVar.Map.map
  val ldataUniquenessCrit : t -> Label.Set.set Label.Map.map
  val lvarExtentCrit : t -> Label.Set.set LVar.Map.map
  val ldataExtentCrit : t -> Label.Set.set Label.Map.map
  val crit_birth_lv : t -> Label.Set.set LVar.Map.map
  val crit_birth_ld : t -> Label.Set.set Label.Map.map
  val crit_death_lv : t -> Label.Set.set LVar.Map.map
  val crit_death_ld : t -> Label.Set.set Label.Map.map
  val displayPass : t -> Label.Set.set Label.Map.map
  val lvarEnvMatch : t -> Label.Set.set LVar.Map.map
  val cvarEnvMatch : t -> Label.Set.set CVar.Map.map
  val relativePop : t -> Label.Set.set
  val continuationOrder : t -> CVar.Set.set CVar.Map.map

  val with_lvarExtents : t * ExtentSet.t LVar.Map.map -> t
  (* val with_cvarExtents : t * ExtentSet.t CVar.Map.map -> t *)
  val with_ldataExtents : t * ExtentSet.t Label.Map.map -> t
  val with_tupleInfo : t * tupleInfo -> t
  val with_dataInfo : t * dataInfo -> t
  val with_funInfo : t * funInfo -> t
  val with_callWebs : t * CallWebs.t -> t
  val with_funKInfo : t * funKInfo -> t
  val with_callWebsK : t * CallWebs.t -> t
  val with_unknownLVars : t * LVar.Set.set -> t
  val with_unknownCVars : t * CVar.Set.set -> t
  val with_lvarUniquenessCrit : t * Label.Set.set LVar.Map.map -> t
  val with_ldataUniquenessCrit : t * Label.Set.set Label.Map.map -> t
  val with_lvarExtentCrit : t * Label.Set.set LVar.Map.map -> t
  val with_ldataExtentCrit : t * Label.Set.set Label.Map.map -> t
  val with_crit_birth_lv : t * Label.Set.set LVar.Map.map -> t
  val with_crit_birth_ld : t * Label.Set.set Label.Map.map -> t
  val with_crit_death_lv : t * Label.Set.set LVar.Map.map -> t
  val with_crit_death_ld : t * Label.Set.set Label.Map.map -> t
  val with_displayPass : t * Label.Set.set Label.Map.map -> t
  val with_lvarEnvMatch : t * Label.Set.set LVar.Map.map -> t
  val with_cvarEnvMatch : t * Label.Set.set CVar.Map.map -> t
  val with_relativePop : t * Label.Set.set -> t
  val with_continuationOrder : t * CVar.Set.set CVar.Map.map -> t

end = struct

  structure PInfo = CPSInformation
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map


  type tupleInfo = {tupleToSelect : (Label.Set.set * bool) Label.Map.map,
                    selectToTuple : (Label.Set.set * bool) Label.Map.map}
  type dataInfo = {dataToMatch : (Label.Set.set * bool) Label.Map.map,
                   matchToData : (Label.Set.set * bool) Label.Map.map}
  type funInfo = {lamToCall : (Label.Set.set * bool) Label.Map.map,
                  callToLam : (Label.Set.set * bool) Label.Map.map}
  type funKInfo= {lamKToCallK : (Label.Set.set * bool) Label.Map.map,
                  callKToLamK : (Label.Set.set * bool) Label.Map.map}

  type t = {
      lvarExtents : ExtentSet.t LVM.map,
      cvarExtents : ExtentSet.t CVM.map,
      ldataExtents : ExtentSet.t LM.map,
      tupleInfo : tupleInfo,
      (* tupleWebs : LLWebs.t, *)
      dataInfo : dataInfo,
      (* dataWebs : LLWebs.t, *)
      funInfo : funInfo,
      callWebs : CallWebs.t,
      funKInfo : funKInfo,
      callWebsK : CallWebs.t,
      unknownLVars : LVar.Set.set,
      unknownCVars : CVar.Set.set,
      lvarUniquenessCrit : LS.set LVM.map,
      lvarExtentCrit : LS.set LVM.map,
      ldataUniquenessCrit : LS.set LM.map,
      ldataExtentCrit : LS.set LM.map,
      crit_birth_lv : LS.set LVM.map,
      crit_birth_ld : LS.set LM.map,
      crit_death_lv : LS.set LVM.map,
      crit_death_ld : LS.set LM.map,
      displayPass : LS.set LM.map,
      lvarEnvMatch : LS.set LVM.map,
      cvarEnvMatch : LS.set CVM.map,
      relativePop : LS.set,
      continuationOrder : CVS.set CVM.map
  }

  fun initial_crit_lv pinfo = let
      val crit = List.foldl (fn (x, acc) => LVM.insert (acc, x, LS.empty)) LVM.empty (PInfo.lvars pinfo)
  in crit end


  fun initial_crit_ld pinfo = let
      val crit = List.foldl (fn (ld, acc) => LM.insert (acc, ld, LS.empty)) LM.empty (PInfo.ldata pinfo)
  in crit end

  fun initial_lvarExtentCrit pinfo = 
      initial_crit_lv pinfo

  fun initial_ldataExtentCrit pinfo = 
      initial_crit_ld pinfo

  fun initial_lvarUniquenessCrit pinfo =
      initial_crit_lv pinfo

  fun initial_ldataUniquenessCrit pinfo =
      initial_crit_ld pinfo
                              
  fun initial_crit_birth_lv pinfo =
      initial_crit_lv pinfo

  fun initial_crit_birth_ld pinfo =
      initial_crit_ld pinfo

  fun initial_crit_death_lv pinfo =
      initial_crit_lv pinfo

  fun initial_crit_death_ld pinfo =
      initial_crit_ld pinfo

  fun initial_displayPass pinfo = let
      fun addCallSite (site, acc) = LM.insert (acc, site, LS.empty)
      val displayPass = LM.empty
      val displayPass = List.foldl addCallSite displayPass (PInfo.call_sites pinfo)
      val displayPass = List.foldl addCallSite displayPass (PInfo.callK_sites pinfo)
  in displayPass end
                                      
  fun initial_lvarEnvMatch pinfo = let
      val lvarEnvMatch = List.foldr (fn (x, acc) => LVM.insert (acc, x, LS.empty)) LVM.empty (PInfo.lvars pinfo)
  in lvarEnvMatch end

  fun initial_cvarEnvMatch pinfo = let
      val cvarEnvMatch = List.foldr (fn (k, acc) => CVM.insert (acc, k, LS.empty)) CVM.empty (PInfo.cvars pinfo)
  in cvarEnvMatch end

  fun initial_continuationOrder pinfo = let
      fun add_k (k, acc) = CVM.insert (acc, k, CVS.singleton k)
      val contOrder = List.foldl add_k CVM.empty (PInfo.cvars pinfo)
  in contOrder end 

  fun initial_tupleInfo (tuples, selects) = let
      val tupleToSelect = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty tuples
      val selectToTuple = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty selects
  in {tupleToSelect=tupleToSelect,
      selectToTuple=selectToTuple}
  end

  fun initial_dataInfo (datas, matches) = let
      val dataToMatch = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty datas
      val matchToData = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty matches
  in {dataToMatch=dataToMatch,
      matchToData=matchToData}
  end

  fun initial_funInfo (lams, calls) = let
      val lamToCall = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty lams
      val callToLam = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty calls
  in {lamToCall=lamToCall,
      callToLam=callToLam}
  end

  fun initial_funKInfo (lamKs, callKs) = let
      val lamKToCallK = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty lamKs
      val callKToLamK = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, true))) LM.empty callKs
  in {lamKToCallK=lamKToCallK,
      callKToLamK=callKToLamK}
  end

  fun info pinfo cu = let
      fun add_lvar (x, acc) = LVM.insert(acc, x, ExtentSet.H (* ExtentSet.extentOfLVar x *) )
      fun add_cvar (k, acc) = CVM.insert(acc, k, ExtentSet.H (* ExtentSet.extentOfCVar k *) )
      fun add_ldata (lab, acc) = LM.insert(acc, lab, ExtentSet.H)
      val lvarExtents = List.foldl add_lvar LVM.empty (PInfo.lvars pinfo)
      val cvarExtents = List.foldl add_cvar CVM.empty (PInfo.cvars pinfo)
      val ldataExtents = List.foldl add_ldata LM.empty (PInfo.ldata pinfo)
      val tupleInfo = initial_tupleInfo (PInfo.tuples pinfo, PInfo.selects pinfo)
      val dataInfo : dataInfo = initial_dataInfo (PInfo.datas pinfo, PInfo.matches pinfo)
      val funInfo = initial_funInfo (PInfo.lams pinfo, PInfo.call_sites pinfo)
      val callWebs =
          CallWebs.initial {lams=PInfo.lams pinfo, calls=PInfo.call_sites pinfo}
      val funKInfo = initial_funKInfo (PInfo.lamKs pinfo, PInfo.callK_sites pinfo)
      val callWebsK =
          CallWebs.initial {lams=PInfo.lamKs pinfo, calls=PInfo.callK_sites pinfo}
      val unknownLVars = LVS.empty
      val unknownCVars = CVS.empty
      val lvarUniquenessCrit = initial_lvarUniquenessCrit pinfo
      val lvarExtentCrit = initial_lvarExtentCrit pinfo
      val ldataUniquenessCrit = initial_ldataUniquenessCrit pinfo
      val ldataExtentCrit = initial_ldataExtentCrit pinfo
      val crit_birth_lv = initial_crit_birth_lv pinfo
      val crit_birth_ld = initial_crit_birth_ld pinfo
      val crit_death_lv = initial_crit_death_lv pinfo
      val crit_death_ld = initial_crit_death_ld pinfo
      val displayPass = initial_displayPass pinfo
      val lvarEnvMatch = initial_lvarEnvMatch pinfo
      val cvarEnvMatch = initial_cvarEnvMatch pinfo
      val relativePop = LS.empty
      val continuationOrder = initial_continuationOrder pinfo
  in
      { lvarExtents=lvarExtents,
        cvarExtents=cvarExtents,
        ldataExtents=ldataExtents,
        tupleInfo=tupleInfo,
        dataInfo=dataInfo,
        funInfo=funInfo,
        callWebs=callWebs,
        funKInfo=funKInfo,
        callWebsK=callWebsK,
        unknownLVars=unknownLVars,
        unknownCVars=unknownCVars,
        lvarUniquenessCrit=lvarUniquenessCrit,
        lvarExtentCrit=lvarExtentCrit,
        ldataUniquenessCrit=ldataUniquenessCrit,
        ldataExtentCrit=ldataExtentCrit,
        crit_birth_lv=crit_birth_lv,
        crit_birth_ld=crit_birth_ld,
        crit_death_lv=crit_death_lv,
        crit_death_ld=crit_death_ld,
        displayPass = displayPass,
        lvarEnvMatch = lvarEnvMatch,
        cvarEnvMatch = cvarEnvMatch,
        relativePop = relativePop,
        continuationOrder = continuationOrder } : t
  end

  fun lvarExtents (ainfo : t) = #lvarExtents ainfo
  fun cvarExtents (ainfo : t) = #cvarExtents ainfo
  fun ldataExtents (ainfo : t) = #ldataExtents ainfo
  fun tupleInfo (ainfo : t) = #tupleInfo ainfo
  fun tupleWebs (ainfo : t) = let
      val {tupleToSelect, selectToTuple} = #tupleInfo ainfo
  in LLWebs.fromMaps {const_map=tupleToSelect, deconst_map=selectToTuple} end
  fun dataInfo (ainfo : t) = #dataInfo ainfo
  fun dataWebs (ainfo : t) = let
      val {dataToMatch, matchToData} = #dataInfo ainfo
  in LLWebs.fromMaps ({const_map=dataToMatch, deconst_map=matchToData}) end
  fun funInfo (ainfo : t) = #funInfo ainfo
  fun callWebs (ainfo : t) = #callWebs ainfo
  fun funKInfo (ainfo : t) = #funKInfo ainfo
  fun callWebsK (ainfo : t) = #callWebsK ainfo
  fun unknownLVars (ainfo : t) = #unknownLVars ainfo
  fun unknownCVars (ainfo : t) = #unknownCVars ainfo
  fun lvarUniquenessCrit (ainfo : t) = #lvarUniquenessCrit ainfo
  fun lvarExtentCrit (ainfo : t) = #lvarExtentCrit ainfo
  fun ldataUniquenessCrit (ainfo : t) = #ldataUniquenessCrit ainfo
  fun ldataExtentCrit (ainfo : t) = #ldataExtentCrit ainfo
  fun displayPass (ainfo : t) = #displayPass ainfo
  fun lvarEnvMatch (ainfo : t) = #lvarEnvMatch ainfo
  fun cvarEnvMatch (ainfo : t) = #cvarEnvMatch ainfo
  fun relativePop (ainfo : t) = #relativePop ainfo
  fun continuationOrder (ainfo : t) = #continuationOrder ainfo
  fun crit_birth_lv (ainfo : t) = #crit_birth_lv ainfo
  fun crit_birth_ld (ainfo : t) = #crit_birth_ld ainfo
  fun crit_death_lv (ainfo : t) = #crit_death_lv ainfo
  fun crit_death_ld (ainfo : t) = #crit_death_ld ainfo

  fun with_lvarExtents (ainfo : t, lvarExtents') =
      {lvarExtents = lvarExtents',
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_cvarExtents (ainfo : t, cvarExtents') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = cvarExtents',
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_ldataExtents (ainfo : t, ldataExtents') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = ldataExtents',
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_tupleInfo (ainfo : t, tupleInfo') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = tupleInfo',
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_dataInfo (ainfo : t, dataInfo') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = dataInfo',
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_funInfo (ainfo : t, funInfo') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = funInfo',
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_callWebs (ainfo : t, callWebs') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = callWebs',
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_funKInfo (ainfo : t, funKInfo') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = funKInfo',
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_callWebsK (ainfo : t, callWebsK') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = callWebsK',
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_unknownLVars (ainfo : t, unknownLVars') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = unknownLVars',
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_unknownCVars (ainfo : t, unknownCVars') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = unknownCVars',
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_lvarUniquenessCrit (ainfo : t, lvarUniquenessCrit') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = lvarUniquenessCrit',
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_lvarExtentCrit (ainfo : t, lvarExtentCrit') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = lvarExtentCrit',
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_ldataUniquenessCrit (ainfo : t, ldataUniquenessCrit') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = ldataUniquenessCrit',
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_ldataExtentCrit (ainfo : t, ldataExtentCrit') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = ldataExtentCrit',
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_crit_birth_lv (ainfo : t, crit_birth_lv') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = crit_birth_lv',
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_crit_birth_ld (ainfo : t, crit_birth_ld') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = crit_birth_ld',
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_crit_death_lv (ainfo : t, crit_death_lv') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = crit_death_lv',
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_crit_death_ld (ainfo : t, crit_death_ld') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = crit_death_ld',
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_displayPass (ainfo : t, displayPass') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = displayPass',
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_lvarEnvMatch (ainfo : t, lvarEnvMatch') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = lvarEnvMatch',
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_cvarEnvMatch (ainfo : t, cvarEnvMatch') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = cvarEnvMatch',
       relativePop = #relativePop ainfo,
       continuationOrder = #continuationOrder ainfo}
  fun with_relativePop (ainfo : t, relativePop') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = relativePop',
       continuationOrder = #continuationOrder ainfo}
  fun with_continuationOrder (ainfo : t, continuationOrder') = 
      {lvarExtents = #lvarExtents ainfo,
       cvarExtents = #cvarExtents ainfo,
       ldataExtents = #ldataExtents ainfo,
       tupleInfo = #tupleInfo ainfo,
       dataInfo = #dataInfo ainfo,
       funInfo = #funInfo ainfo,
       callWebs = #callWebs ainfo,
       funKInfo = #funKInfo ainfo,
       callWebsK = #callWebsK ainfo,
       unknownLVars = #unknownLVars ainfo,
       unknownCVars = #unknownCVars ainfo,
       lvarUniquenessCrit = #lvarUniquenessCrit ainfo,
       lvarExtentCrit = #lvarExtentCrit ainfo,
       ldataUniquenessCrit = #ldataUniquenessCrit ainfo,
       ldataExtentCrit = #ldataExtentCrit ainfo,
       crit_birth_lv = #crit_birth_lv ainfo,
       crit_birth_ld = #crit_birth_ld ainfo,
       crit_death_lv = #crit_death_lv ainfo,
       crit_death_ld = #crit_death_ld ainfo,
       displayPass = #displayPass ainfo,
       lvarEnvMatch = #lvarEnvMatch ainfo,
       cvarEnvMatch = #cvarEnvMatch ainfo,
       relativePop = #relativePop ainfo,
       continuationOrder = continuationOrder'}

end
