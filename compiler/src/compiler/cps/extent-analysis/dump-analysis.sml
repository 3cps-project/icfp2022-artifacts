(* analysis-dump.sml
 *
 * Various functions for debugging the analysis and dumping information.
 *)

structure DumpAnalysis : sig

    val dumpAnalysisSummary : CPSInformation.t * StateSpace.t -> unit

    val dumpStateSpace : string * StateSpace.t -> unit

    val dumpExtents : CPSInformation.t * AnalysisInformation.t * AnalysisInformation.t -> unit

    val dumpExtentSummary : CPSInformation.t * AnalysisInformation.t * AnalysisInformation.t -> unit

    val dumpInterpreterExtentSummary : CPSInformation.t * AnalysisInformation.t * AnalysisInformation.t * (int LVar.Tbl.hash_table) * (int Label.Tbl.hash_table) -> unit

  end = struct

    structure PInfo = CPSInformation
    structure AInfo = AnalysisInformation
    structure LV = LVar
    structure CV = CVar
    structure LS = Label.Set
    structure ES = ExtentSet
    structure ST = Stats
    structure LM = Label.Map 
    structure LVM = LVar.Map 

    fun dumpAnalysisSummary (pinfo, stateSpace : StateSpace.t) = 
        DumpAnalysisSummary.run (fn say => let
            fun colorStr color msg = ANSIText.fmt ({fg=SOME color, bg=NONE, bf=true, ul=false}, msg)
            fun getPercentString (n1, n2) =
                if n2 = 0 (* don't want to divide by 0 *)
                then "-"
                else let
                    val percent = Real.floor (100.0 * (real n1) / (real n2))
                    val color =
                        if percent >= 90
                        then ANSIText.green
                        else if percent >= 70
                        then ANSIText.yellow
                        else ANSIText.red
                in colorStr color (Int.toString percent) end
            fun say_nums (msg, n1, n2) =
                say [StringCvt.padRight #" " 30 msg, ": ",
                     StringCvt.padLeft #" " 4 (Int.toString n1),
                     " / ",
                     StringCvt.padLeft #" " 4 (Int.toString n2),
                     "   ", getPercentString (n1, n2), "%", "\n"];
            val exps = PInfo.exps pinfo 
            val missedExps = let 
                val tbl = Label.Tbl.mkTable (100, Fail "")
                val () = List.app (fn lab_e => Label.Tbl.insert tbl (lab_e, NONE)) exps
                fun handle_config c = let val (CPS.EXP (lab_e, _), _, _, _, _) = Config.get c
                                      in Label.Tbl.insert tbl (lab_e, SOME 0) end
                val () = Config.Set.app handle_config (#configs stateSpace)
                fun handle_tbl_entry  (l, i, acc) = case i of NONE => l :: acc | _ => acc
            in Label.Tbl.foldi handle_tbl_entry [] tbl end
                               
            val format = {fg=SOME ANSIText.blue, bg=NONE, bf=true, ul=false}
            val () = List.app (fn lab_e => PrintCPS.formatLabel (lab_e, format)) missedExps
            val () = say_nums ("expressions visited by analysis",
                               List.length exps - List.length missedExps,
                               List.length exps)

            val numConfigs = Config.Set.numItems (#configs stateSpace)
            val () = say ["total configurations: ", Int.toString numConfigs, "\n"]
            val {update_addr_count=update_addr_count,
                 update_addrP_count=update_addrP_count} = StateSpace.stats ()
            val () = say ["addr update count: ", Int.toString update_addr_count, "\n"]
            val () = say ["addrP update count: ", Int.toString update_addrP_count, "\n"]
        in () end)


    (* dump a representation of the state space if
       Ctl.dumpAnalysisStateSpace is enabled *)
    fun dumpStateSpace (msg, stateSpace : StateSpace.t) = let
        val configs = #configs stateSpace
        val store = #store stateSpace
        val storeK = #storeK stateSpace
        val storeP = #storeP stateSpace
        val ldata_passed_to_unknown = #ldata_passed_to_unknown stateSpace
    in
        DumpAnalysisStateSpace.run
            (fn say => let
                 (* say configs in groups of 5 *)
                 fun sayConfigs configs =
                     case configs
                      of (xi1 :: xi2 :: xi3 :: xi4 :: xi5 :: rst) =>
                         (say [String.concatWithMap " " Config.toString [xi1, xi2, xi3, xi4, xi5], "\n"];
                          sayConfigs rst)
                       | lst => if List.null lst then () else say [String.concatWithMap " " Config.toString lst, "\n"];
                 (* say each binding on its own line *)
                 fun sayStore store = Store.appi (fn (a, d) => say [Addr.toString a, " -> ", Value.toString d, "\n"]) store
                 (* say each binding on its own line *)
                 fun sayStoreK storeK = StoreK.appi (fn (aK, dK) => say [AddrK.toString aK, " -> ", ValueK.toString dK, "\n"]) storeK
                 (* say each binding on its own line *)
                 fun sayStoreP storeP = StoreProxy.appi (fn (aP, dP) => say [AddrProxy.toString aP, " -> ", ValueProxy.toString dP, "\n"]) storeP
                 fun sayPassedToUnknown ldata_passed_to_unknown = say [String.concatWithMap " " Label.toString (LS.listItems ldata_passed_to_unknown), "\n"]
             in
                 say [msg, "\n"];
                 say ["--- Configs ---", "\n"];
                 sayConfigs (Config.Set.listItems configs);
                 say ["--- Store ---", "\n"];
                 sayStore store;
                 say ["--- StoreK ---", "\n"];
                 sayStoreK storeK;
                 say ["--- StoreP ---", "\n"];
                 sayStoreP storeP;
                 say ["--- Passed to Unknown ---", "\n"];
                 sayPassedToUnknown ldata_passed_to_unknown;
                 ()
             end)
    end

  fun extentMaps (pinfo, ainfo) = let
      fun crit_intersect (crit1, crit2, lst, empty, insert, lookup) = let
          fun add_element (x, acc) =
              insert (acc, x, LS.intersection (lookup (crit1, x), lookup (crit2, x)))
      in List.foldl add_element empty lst end

      val lab0 = PInfo.lam_lab0 pinfo

      val lvars = PInfo.lvars pinfo
      val ldata = PInfo.ldata pinfo

      val (lvarUniquenessCrit, ldataUniquenessCrit) =
          (AInfo.lvarUniquenessCrit ainfo, AInfo.ldataUniquenessCrit ainfo)
      val (crit_birth_lv, crit_birth_ld) =
          (AInfo.crit_birth_lv ainfo, AInfo.crit_birth_ld ainfo)
      val (crit_death_lv, crit_death_ld) =
          (AInfo.crit_death_lv ainfo, AInfo.crit_death_ld ainfo)

      val lvarExtentCrit =
          crit_intersect (crit_birth_lv, crit_death_lv, lvars,
                          LVM.empty, LVM.insert, LVM.lookup)
      val ldataExtentCrit =
          crit_intersect (crit_birth_ld, crit_death_ld, ldata,
                          LM.empty, LM.insert, LM.lookup)
                         (*
      val lvarRelativeExtent =
          crit_intersect (lvarUniquenessCrit, lvarExtentCrit, lvars,
                          LVM.empty, LVM.insert, LVM.lookup)
      val ldataRelativeExtent =
          crit_intersect (ldataUniquenessCrit, ldataExtentCrit, ldata,
                          LM.empty, LM.insert, LM.lookup)
                           *)            
      fun can_do_S b = if b then ES.HS else ES.H
      fun can_do_R b = if b then ES.HR else ES.H
      fun lvar_extent (x, acc) = let
          val lab_loc = PInfo.immediate_alloc_loc_lv pinfo x
          val ex_S = can_do_S (LS.member (LVM.lookup (lvarExtentCrit, x), lab_loc))
          val ex_R = can_do_R (LS.member (LVM.lookup (lvarUniquenessCrit, x), lab0))
      in LVM.insert (acc, x, ES.join (ex_S, ex_R)) end
      val lvarExtents = List.foldl lvar_extent LVM.empty lvars
      fun ldata_extent (ld, acc) = let
          val lab_loc = PInfo.immediate_alloc_loc_ld pinfo ld
          val ex_S = can_do_S (LS.member (LM.lookup (ldataExtentCrit, ld), lab_loc))
          val ex_R = can_do_R (LS.member (LM.lookup (ldataUniquenessCrit, ld), lab0))
      in LM.insert (acc, ld, ES.join (ex_S, ex_R)) end
      val ldataExtents = List.foldl ldata_extent LM.empty ldata
  in (lvarExtents, ldataExtents) end

  (* dump the syntactic and analysis extent info if
     Ctl.dumpExtentSummary is enabled *)
    fun dumpExtents (pinfo, ainfoSyntax, ainfo) =
          DumpExtents.run
            (fn say =>
                let
                 val lvarExtentsSyntax = AInfo.lvarExtents ainfoSyntax
                 (* val cvarExtents = AInfo.cvarExtents ainfo *)
                 val (lvarExtents, _) = extentMaps (pinfo, ainfo)
                 (* val cvarExtents' = AInfo.cvarExtents ainfo' *)
                 fun lpairPrevToString (x, ex, prev) = String.concat[
                         LV.toString x, " => ", ES.toString ex,
                         " (syn ", ES.toString prev, ")"
                     ]
                (*
                    fun cpairPrevToString (k, ex, prev) = String.concat[
                            CV.toString k, " => ", ES.toString ex,
                            " (syn ", ES.toString prev, ")"
                        ]
                *)
                in
                    say ["--- info ----\n"];
                    LV.Map.appi
                        (fn (x, ex) =>
                            say [lpairPrevToString(x, ex, Option.valOf(LV.Map.find(lvarExtentsSyntax, x))), "\n"])
                        lvarExtents
                (*  CV.Map.appi
                    (fn (k, ex) => say[cpairPrevToString(k, ex, Option.valOf(CV.Map.find(cvarExtents, k))), "\n"])
                    cvarExtents'
                 *)
                end)

  (* dump a summary of the extent promotions that occurred if
     Ctl.dumpExtentSummary is enabled *)
    fun dumpExtentSummary (pinfo, ainfoSyntax, ainfo) = let
    in 
          DumpExtentSummary.run
            (fn say => let
                 val lvarExtentsSyntax = AInfo.lvarExtents ainfoSyntax
                 val (lvarExtents, _) = extentMaps (pinfo, ainfo)
                 (* emulate stats counters with color *)
                  fun tick (name, cnt) = (cnt := (! cnt) + 1)
                  fun promoteCntr x1 x2 = (concat[x1, " -> ", x2], ref 0)
                  val H_str = ES.toString ES.H
                  val HS_str = ES.toString ES.HS
                  val HR_str = ES.toString ES.HR
                  val HSR_str = ES.toString ES.HSR
                  val cntHtoH = promoteCntr H_str H_str
                  val cntHtoS = promoteCntr H_str HS_str
                  val cntHtoR = promoteCntr H_str HR_str
                  val cntHtoSR = promoteCntr H_str HSR_str
                  val cntStoH = promoteCntr HS_str H_str
                  val cntStoS = promoteCntr HS_str HS_str
                  val cntStoR = promoteCntr HS_str HR_str
                  val cntStoSR = promoteCntr HS_str HSR_str
                  val cntRtoH = promoteCntr HR_str H_str
                  val cntRtoS = promoteCntr HR_str HS_str
                  val cntRtoR = promoteCntr HR_str HR_str
                  val cntRtoSR = promoteCntr HR_str HSR_str
                  val cntSRtoH = promoteCntr HSR_str H_str
                  val cntSRtoS = promoteCntr HSR_str HS_str
                  val cntSRtoR = promoteCntr HSR_str HR_str
                  val cntSRtoSR = promoteCntr HSR_str HSR_str
                  fun perform_counting () = 
                      LV.Map.appi
                          (fn (x, ex_ana) => 
                              (case LV.Map.find (lvarExtentsSyntax, x)
                                of SOME ex_syn => 
                                   (case (ex_syn, ex_ana)
                                     of (ES.H, ES.H) => tick cntHtoH
                                      | (ES.H, ES.HS) => tick cntHtoS
                                      | (ES.H, ES.HR) => tick cntHtoR
                                      | (ES.H, ES.HSR) => tick cntHtoSR
                                      | (ES.HS, ES.H) => tick cntStoH
                                      | (ES.HS, ES.HS) => tick cntStoS
                                      | (ES.HS, ES.HR) => tick cntStoR
                                      | (ES.HS, ES.HSR) => tick cntStoSR
                                      | (ES.HR, ES.H) => tick cntRtoH
                                      | (ES.HR, ES.HS) => tick cntRtoS
                                      | (ES.HR, ES.HR) => tick cntRtoR
                                      | (ES.HR, ES.HSR) => tick cntRtoSR
                                      | (ES.HSR, ES.H) => tick cntSRtoH
                                      | (ES.HSR, ES.HS) => tick cntSRtoS
                                      | (ES.HSR, ES.HR) => tick cntSRtoR
                                      | (ES.HSR, ES.HSR) => tick cntSRtoSR
                                      (* | _ => () (* raise Fail "bad" *) *)
                                   (* end case *))
                                 | NONE => raise Fail "bad"
                          (* end case *)))
                          lvarExtents
                  fun say_cnt (msg, cnt) =
                      if (! cnt) <> 0
                      then (* pad to 7 digits *)
                          say [StringCvt.padRight #" " 7 (Int.toString (! cnt)), msg, "\n"]
                      else ()
             in
                 perform_counting ();
                 say ["Promotions LVar", "\n"];
                 say_cnt cntHtoH;
                 say_cnt cntHtoS;
                 say_cnt cntHtoR;
                 say_cnt cntHtoSR; 
                 say_cnt cntStoH;
                 say_cnt cntStoS;
                 say_cnt cntStoSR;
                 say_cnt cntRtoH;
                 say_cnt cntRtoS;
                 say_cnt cntRtoR;
                 say_cnt cntRtoSR;
                 say_cnt cntSRtoH;
                 say_cnt cntSRtoS;
                 say_cnt cntSRtoR;
                 say_cnt cntSRtoSR;
                 ()
             end);
          DumpExtentSummary.run
            (fn say => let
                 val ldataExtentsSyntax = AInfo.ldataExtents ainfoSyntax
                 val (_, ldataExtents) = extentMaps (pinfo, ainfo)
                 (* emulate stats counters with color *)
                  fun tick (name, cnt) = (cnt := (! cnt) + 1)
                  fun promoteCntr x1 x2 = (concat[x1, " -> ", x2], ref 0)
                  val H_str = ES.toString ES.H
                  val HS_str = ES.toString ES.HS
                  val HR_str = ES.toString ES.HR
                  val HSR_str = ES.toString ES.HSR
                  val cntHtoH = promoteCntr H_str H_str
                  val cntHtoS = promoteCntr H_str HS_str
                  val cntHtoR = promoteCntr H_str HR_str
                  val cntHtoSR = promoteCntr H_str HSR_str
                  val cntStoS = promoteCntr HS_str HS_str
                  val cntStoSR = promoteCntr HS_str HSR_str
                  val cntRtoR = promoteCntr HR_str HR_str
                  val cntRtoSR = promoteCntr HR_str HSR_str
                  val cntSRtoSR = promoteCntr HSR_str HSR_str
                  fun perform_counting () = 
                      LM.appi
                          (fn (x, ex_ana) => 
                              (case LM.find (ldataExtentsSyntax, x)
                                of SOME ex_syn => 
                                   (case (ex_syn, ex_ana)
                                     of (ES.H, ES.H) => tick cntHtoH
                                      | (ES.H, ES.HS) => tick cntHtoS
                                      | (ES.H, ES.HR) => tick cntHtoR
                                      | (ES.H, ES.HSR) => tick cntHtoSR
                                      | (ES.HS, ES.HS) => tick cntStoS
                                      | (ES.HS, ES.HSR) => tick cntStoSR
                                      | (ES.HR, ES.HR) => tick cntRtoR
                                      | (ES.HR, ES.HSR) => tick cntRtoSR
                                      | (ES.HSR, ES.HSR) => tick cntSRtoSR
                                      | _ => () (* raise Fail "bad" *)
                                   (* end case *))
                                 | NONE => raise Fail "bad"
                          (* end case *)))
                          ldataExtents
                  fun say_cnt (msg, cnt) =
                      if (! cnt) <> 0
                      then (* pad to 7 digits *)
                          say [StringCvt.padRight #" " 7 (Int.toString (! cnt)), msg, "\n"]
                      else ()
             in
                 perform_counting ();
                 say ["Promotions LData", "\n"];
                 say_cnt cntHtoH;
                 say_cnt cntHtoS;
                 say_cnt cntHtoR;
                 say_cnt cntHtoSR; 
                 say_cnt cntStoS;
                 say_cnt cntStoSR;
                 say_cnt cntRtoR;
                 say_cnt cntRtoSR;
                 say_cnt cntSRtoSR;
                 ()
             end)
    end 

  (* dump a summary of the effect of extent promotions (determined by the interpreter) 
     that occurred if Ctl.dumpExtentSummary is enabled *)
    fun dumpInterpreterExtentSummary (pinfo, ainfoSyntax, ainfo, count_lvar_alloc, count_lam_alloc) = let
        fun colorStr color msg = ANSIText.fmt ({fg=SOME color, bg=NONE, bf=true, ul=false}, msg)
        fun getPercentString (n1, n2) =
            if n2 = 0 (* don't want to divide by 0 *)
            then "-"
            else let
                val percent = Real.floor (100.0 * (real n1) / (real n2))
                val color =
                    if percent >= 90
                    then ANSIText.green
                    else if percent >= 70
                    then ANSIText.yellow
                    else ANSIText.red
            in colorStr color (Int.toString percent) end
        fun say_nums say ((msg, n1), (_, n2)) =
            say [StringCvt.padRight #" " 30 msg, ": ",
                 StringCvt.padLeft #" " 4 (Int.toString (!n1)),
                 " / ",
                 StringCvt.padLeft #" " 4 (Int.toString (!n2)),
                 "   ", getPercentString (!n1, !n2), "%", "\n"];
    in 
          DumpAllocationSummary.run
            (fn say => let
                 val lvarExtentsSyntax = AInfo.lvarExtents ainfoSyntax
                 val (lvarExtents, _) = extentMaps (pinfo, ainfo)
                 (* emulate stats counters with color *)
                  fun tick x (name, cnt) = (cnt := (! cnt) + (LVar.Tbl.lookup count_lvar_alloc x))
                  fun promoteCntr x1 x2 = (concat[x1, " -> ", x2], ref 0)
                  val H_str = ES.toString ES.H
                  val HS_str = ES.toString ES.HS
                  val HR_str = ES.toString ES.HR
                  val HSR_str = ES.toString ES.HSR

                  val cntHtoH = promoteCntr H_str H_str
                  val cntHtoS = promoteCntr H_str HS_str
                  val cntHtoR = promoteCntr H_str HR_str
                  val cntHtoSR = promoteCntr H_str HSR_str
                  val cntStoS = promoteCntr HS_str HS_str
                  val cntStoSR = promoteCntr HS_str HSR_str
                  val cntRtoR = promoteCntr HR_str HR_str
                  val cntRtoSR = promoteCntr HR_str HSR_str
                  val cntSRtoSR = promoteCntr HSR_str HSR_str
                  fun perform_counting () = 
                      LV.Map.appi
                          (fn (x, ex_ana) => 
                              (case LV.Map.find (lvarExtentsSyntax, x)
                                of SOME ex_syn => 
                                   (case (ex_syn, ex_ana)
                                     of (ES.H, ES.H) => tick x cntHtoH
                                      | (ES.H, ES.HS) => tick x cntHtoS
                                      | (ES.H, ES.HR) => tick x cntHtoR
                                      | (ES.H, ES.HSR) => tick x cntHtoSR
                                      | (ES.HS, ES.HS) => tick x cntStoS
                                      | (ES.HS, ES.HSR) => tick x cntStoSR
                                      | (ES.HR, ES.HR) => tick x cntRtoR
                                      | (ES.HR, ES.HSR) => tick x cntRtoSR
                                      | (ES.HSR, ES.HSR) => tick x cntSRtoSR
                                      | _ => () (* raise Fail "bad" *)
                                   (* end case *))
                                 | NONE => raise Fail "bad"
                          (* end case *)))
                          lvarExtents
                  fun say_cnt (msg, cnt) =
                      if (! cnt) <> 0
                      then (* pad to 7 digits *)
                          say [StringCvt.padRight #" " 7 (Int.toString (! cnt)), msg, "\n"]
                      else ()
             in
                 perform_counting ();
                 say ["Allocations LVar", "\n"];
                 say_cnt cntHtoH;
                 say_cnt cntHtoS;
                 say_cnt cntHtoR;
                 say_cnt cntHtoSR; 
                 say_cnt cntStoS;
                 say_cnt cntStoSR;
                 say_cnt cntRtoR;
                 say_cnt cntRtoSR;
                 say_cnt cntSRtoSR;
                 ()
             end);
          DumpAllocationSummary.run
            (fn say => let
                 val ldataExtentsSyntax = AInfo.ldataExtents ainfoSyntax
                 val (_, ldataExtents) = extentMaps (pinfo, ainfo)
                 (* emulate stats counters with color *)
                  fun tick x (name, cnt) = (cnt := (! cnt) + (Label.Tbl.lookup count_lam_alloc x))
                  fun promoteCntr x1 x2 = (concat[x1, " -> ", x2], ref 0)
                  val H_str = ES.toString ES.H
                  val HS_str = ES.toString ES.HS
                  val HR_str = ES.toString ES.HR
                  val HSR_str = ES.toString ES.HSR

                  val cntHtoH = promoteCntr H_str H_str
                  val cntHtoS = promoteCntr H_str HS_str
                  val cntHtoR = promoteCntr H_str HR_str
                  val cntHtoSR = promoteCntr H_str HSR_str
                  val cntStoS = promoteCntr HS_str HS_str
                  val cntStoSR = promoteCntr HS_str HSR_str
                  val cntRtoR = promoteCntr HR_str HR_str
                  val cntRtoSR = promoteCntr HR_str HSR_str
                  val cntSRtoSR = promoteCntr HSR_str HSR_str
                  fun perform_counting () = 
                      LM.appi
                          (fn (x, ex_ana) => 
                              (case LM.find (ldataExtentsSyntax, x)
                                of SOME ex_syn => 
                                   (case (ex_syn, ex_ana)
                                     of (ES.H, ES.H) => tick x cntHtoH
                                      | (ES.H, ES.HS) => tick x cntHtoS
                                      | (ES.H, ES.HR) => tick x cntHtoR
                                      | (ES.H, ES.HSR) => tick x cntHtoSR
                                      | (ES.HS, ES.HS) => tick x cntStoS
                                      | (ES.HS, ES.HSR) => tick x cntStoSR
                                      | (ES.HR, ES.HR) => tick x cntRtoR
                                      | (ES.HR, ES.HSR) => tick x cntRtoSR
                                      | (ES.HSR, ES.HSR) => tick x cntSRtoSR
                                      | _ => () (* raise Fail "bad" *)
                                   (* end case *))
                                 | NONE => raise Fail "bad"
                          (* end case *)))
                          ldataExtents
                  fun say_cnt (msg, cnt) =
                      if (! cnt) <> 0
                      then (* pad to 7 digits *)
                          say [StringCvt.padRight #" " 7 (Int.toString (! cnt)), msg, "\n"]
                      else ()
             in
                 perform_counting ();
                 say ["Allocations LData", "\n"];
                 say_cnt cntHtoH;
                 say_cnt cntHtoS;
                 say_cnt cntHtoR;
                 say_cnt cntHtoSR; 
                 say_cnt cntStoS;
                 say_cnt cntRtoR;
                 say_cnt cntRtoSR;
                 say_cnt cntSRtoSR;
                 ()
             end)
    end 
  end





