(* cps-interpreter.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The top level of the interpreter.
 *)


structure CPSInterpreter : sig

    val enabled : unit -> bool

  (* interprets the given computational unit, and checks that the
     information determined by the analyses are correct *)
    val interpretAndCheck : CPSInformation.t * CPS.comp_unit * AnalysisInformation.t * AnalysisInformation.t -> unit

    type var_info = {stk : int, reg : int}
    type extents = {
      (* the lvars that we are interested in obtaining extent
       * information for currently all lvars in the program
       *)
        totalLVars : int,
        syntacticLVars : var_info,
        analysisLVars : var_info,
        trueLVars : var_info,
      (* the ldata that we are interested in obtaining extent
       * information for; currently all ldata in the program
       *)
        totalLData : int,
        syntacticLData : var_info,
        analysisLData : var_info,
        trueLData : var_info
      }

    val getResults : unit -> extents * (int, int) ComparisonResults.criteria_t

    val getPromotionResults : unit -> {lvar : PromotionDump.t, ldata : PromotionDump.t}

end = struct

  fun enabled () = ((* Controls.get Ctl.dumpAnalysisResults orelse *)
                    Controls.get Ctl.checkAnalysisResults)

  structure C = CPS
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map
  structure ST = Stats

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  structure ES = ExtentSet

  val lvarPromotionResults = ref PromotionDump.empty
  val ldataPromotionResults = ref PromotionDump.empty
  fun getPromotionResults () = {lvar = !lvarPromotionResults, ldata = !ldataPromotionResults}

  type var_info = int ComparisonResults.var_info
  type extents = (int, int) ComparisonResults.extents

  val extentResults : extents ref = let
        val zero = {reg = 0, stk = 0}
        in
          ref {
              totalLVars = 0,
              syntacticLVars = zero,
              analysisLVars = zero,
              trueLVars = zero,
              totalLData = 0,
              syntacticLData = zero,
              analysisLData = zero,
              trueLData = zero
            }
        end

  val criteriaResults = ref {
          total_criteria_lvar_pairs=0,
          analysis_rel_ext_lvar_pairs=0,
          analysis_uniq_crit_lvar_pairs=0,
          analysis_ext_crit_lvar_pairs=0,
          true_rel_ext_lvar_pairs=0,
          true_uniq_crit_lvar_pairs=0,
          true_ext_crit_lvar_pairs=0,

          total_criteria_ldata_pairs=0,
          analysis_rel_ext_ldata_pairs=0,
          analysis_uniq_crit_ldata_pairs=0,
          analysis_ext_crit_ldata_pairs=0,
          true_rel_ext_ldata_pairs=0,
          true_uniq_crit_ldata_pairs=0,
          true_ext_crit_ldata_pairs=0
        }

  (* counters to track how many / what kind of updates are going on *)
  local
      val grp = ST.Group.newWithPri ST.Group.root ("analysis-check", [2, 1])
      val newCntr = ST.Counter.new grp
  in
  val total_counter = newCntr ("steps")
  val a_frame_merges_counter = newCntr ("analysis frame merges")
  val c_frame_merges_counter = newCntr ("concrete frame merges")
  val concrete_states_counter = newCntr ("concrete states")
  end

  (* util functions *)
  fun colorStr color msg = ANSIText.fmt ({fg=SOME color, bg=NONE, bf=true, ul=false}, msg)
  val say = CheckAnalysisResults.say
  fun say_list (color, msg, lst, f) =
      if List.null lst then ()
      else say [colorStr color (String.concat [msg, ": ", String.concatWithMap " " f lst, "\n"])]
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
  fun lvar_label_toString (x, l) = "(" ^ (LVar.toString x) ^ " " ^ (Label.toString l) ^ ")"
  fun label_label_toString (l, l') = "(" ^ (Label.toString l) ^ " " ^ (Label.toString l') ^ ")"
  fun ldata_label_toString (ld, l) = label_label_toString (ld, l)
  val WARN = ANSIText.yellow
  val ERROR = ANSIText.red
  fun difference same (l1, l2) =
      List.filter (fn e1 => not (List.exists (fn e2 => same (e1, e2)) l2)) l1


  fun dumpCallWebs (pinfo, ainfo, iinfo) = let
      val a_callWebs = AInfo.callWebs ainfo
      val c_callWebs = AInfo.callWebs iinfo
      val a_callWebsK = AInfo.callWebsK ainfo
      val c_callWebsK = AInfo.callWebsK iinfo
      val a_callWebs_map = CallWebs.create_map a_callWebs
      val c_callWebs_map = CallWebs.create_map a_callWebs
      val a_callWebsK_map = CallWebs.create_map a_callWebsK
      val c_callWebsK_map = CallWebs.create_map c_callWebsK
      (* only count the webs that we can make progress on; i.e. that don't have an unknown *)
      fun filter_count (web : CallWebs.web) =
          true (* not (#unknown_call web orelse #unknown_lam web orelse LS.isEmpty (#lams web) orelse LS.isEmpty (#calls web)) *)
      val a_num_webs = List.length (List.filter filter_count (CallWebs.all a_callWebs))
      val c_num_webs = List.length (List.filter filter_count (CallWebs.all c_callWebs))
      val a_num_websK = List.length (List.filter filter_count (CallWebs.all a_callWebsK))
      val c_num_websK = List.length (List.filter filter_count (CallWebs.all c_callWebsK))
      fun web_diff (web1 : CallWebs.web, web2 : CallWebs.web) =
          {calls=LS.difference (#calls web1, #calls web2),
           lams=LS.difference (#lams web1, #lams web2),
           unknown_call=if #unknown_call web1 then not (#unknown_call web2) else false,
           unknown_lam=if #unknown_lam web1 then not (#unknown_lam web2) else false}
      fun web_isEmpty (web : CallWebs.web) =
          LS.isEmpty (#calls web)
          andalso LS.isEmpty (#lams web)
          andalso not (#unknown_call web)
          andalso not (#unknown_lam web)
      fun convert_to_list map =
          LM.foldli (fn (l, web, acc) =>
                        if web_isEmpty web
                        then acc
                        else (l, web) :: acc)
                    [] map
      fun compute_diff (callWebs_map1, callWebs_map2) =
          convert_to_list (LM.intersectWith web_diff (callWebs_map1, callWebs_map2))
      val callWebs_bad = compute_diff (c_callWebs_map, a_callWebs_map)
      val callWebs_missed = compute_diff (a_callWebs_map, c_callWebs_map)
      val callWebsK_bad = compute_diff (c_callWebsK_map, a_callWebsK_map)
      val callWebsK_missed = compute_diff (a_callWebsK_map, c_callWebsK_map)
      fun L_list_toString ls =  "{" ^ (String.concatWith ", " (List.map Label.toString ls)) ^ "}"
      fun LS_toString ls = L_list_toString (LS.listItems ls)
      fun pair_toString (l, web : CallWebs.web) = let
          val web_entries =
              (if LS.isEmpty (#calls web) then [] else ["calls: " ^ (LS_toString (#calls web))]) @
              (if LS.isEmpty (#lams web) then [] else ["lams: " ^ (LS_toString (#lams web))]) @
              (if (#unknown_call web) then ["unknown_call: true"] else []) @
              (if (#unknown_lam web) then ["unknown_lam: true"] else [])
      in
          "(" ^ Label.toString l ^ " {" ^ (String.concatWith "; " web_entries) ^ "}" ^ ")"
      end
      fun web_toString ({lams, calls, ...} : CallWebs.web) =
          String.concat ["{",
                         "lams: ", String.concatWithMap " " Label.toString (LS.listItems lams), " ",
                         "calls: ", String.concatWithMap " " Label.toString (LS.listItems calls), "}"]
      fun web_filter ({lams, calls, unknown_call, unknown_lam} : CallWebs.web) =
          not (unknown_call orelse unknown_lam orelse LS.isEmpty calls orelse LS.isEmpty lams)
  in
      
      say_nums ("found call webs",
                a_num_webs, c_num_webs);
      say_nums ("found call websK",
                a_num_websK, c_num_websK);
      (*
      say_list (WARN, "missed call webs",
                callWebs_missed, pair_toString);
      say_list (WARN, "missed call websK",
                callWebsK_missed, pair_toString);
      *)
      say_list (ERROR, "bad call webs",
                callWebs_bad, pair_toString);
      say_list (ERROR, "bad call websK",
                callWebsK_bad, pair_toString);
      (*
      Debug.say [String.concatWithMap "\n" web_toString (List.filter web_filter (CallWebs.all a_callWebs)), "\n"];
      Debug.say [String.concatWithMap "\n" web_toString (List.filter web_filter (CallWebs.all c_callWebs)), "\n"];
      Debug.say [String.concatWithMap "\n" web_toString (List.filter web_filter (CallWebs.all a_callWebsK)), "\n"];
      Debug.say [String.concatWithMap "\n" web_toString (List.filter web_filter (CallWebs.all c_callWebsK)), "\n"];
      *)
      ()
  end

  (* Dump relativePop and continuationOrder information *)
  fun dumpContInfo (pinfo, ainfo, iinfo) = let
      (*
      val a_relativePop = AInfo.relativePop ainfo
      val c_relativePop = AInfo.relativePop iinfo
      val missed_relativePop =
          LS.listItems (LS.difference (c_relativePop, a_relativePop))
      val bad_relativePop =
          LS.listItems (LS.difference (a_relativePop, c_relativePop))
      val num_a_relativePop = LS.numItems a_relativePop
      val num_c_relativePop = LS.numItems c_relativePop
      *)
      val a_continuationOrder = AInfo.continuationOrder ainfo
      val c_continuationOrder = AInfo.continuationOrder iinfo
      fun diff_with map' (k, cvs, acc) = let
          val cvs' = CVM.lookup (map', k)
          val diff_cvs = CVS.difference (cvs, cvs')
          val acc = CVS.foldl (fn (k', acc) => (k, k') :: acc) acc diff_cvs
      in acc end
      val missed_continuationOrder =
          CVM.foldli (diff_with a_continuationOrder) [] c_continuationOrder
      val bad_continuationOrder =
          CVM.foldli (diff_with c_continuationOrder) [] a_continuationOrder
      fun countAndAdd (k, cvs, acc) = (CVS.numItems (CVS.subtract (cvs, k))) + acc
      val num_a_continuationOrder =
          CVM.foldli countAndAdd 0 a_continuationOrder
      val num_c_continuationOrder =
          CVM.foldli countAndAdd 0 c_continuationOrder
                    (*
      val a_contOrder_list =
          CVM.foldli (fn (k, ks, acc) =>
                         CVS.foldl (fn (k', acc) =>
                                       if CVar.same (k, k') then acc else (k, k') :: acc) acc ks)
                     [] a_continuationOrder
      val c_contOrder_list =
          CVM.foldli (fn (k, ks, acc) =>
                         CVS.foldl (fn (k', acc) =>
                                       if CVar.same (k, k') then acc else (k, k') :: acc) acc ks)
                     [] c_continuationOrder
                     *)
      fun cvar_cvar_toString (k, k') =
          "(" ^ (CVar.toString k) ^ " <= " ^ (CVar.toString k') ^ ")"
  in
      (*
      say_list (WARN, "missed relative pop",
                missed_relativePop, Label.toString);
      *)
      (*
      say_list (ERROR, "bad relative pop",
                bad_relativePop, Label.toString);
      say_nums ("found relative pop",
                num_a_relativePop, num_c_relativePop);
      *)
      (*
      say_list (WARN, "missed continuation order",
                missed_continuationOrder, cvar_cvar_toString);
      *)
      (*
      say_list (WARN, "a cont order", a_contOrder_list, cvar_cvar_toString);
      say_list (WARN, "c cont order", c_contOrder_list, cvar_cvar_toString);
      *)
      say_list (ERROR, "bad continuation order",
                bad_continuationOrder, cvar_cvar_toString);
      say_nums ("found continuation order",
                num_a_continuationOrder, num_c_continuationOrder);
      ()
  end

  (* Dump information related to the number and kind of display passes. *)
  fun dumpDisplayPass (pinfo, cu as C.CU(_, lab0, _, _, _), ainfo_syntax, ainfo, iinfo) =
      let
      val a_displayPass = AInfo.displayPass ainfo
      val c_displayPass = AInfo.displayPass iinfo
      fun add_callSites (callSite, _, callSites) =
          LS.add (callSites, callSite)
      val callSites = LM.foldli add_callSites LS.empty c_displayPass
      fun add_dsp l (dsp, acc) = (l, dsp) :: acc
      fun collectMissed (l, acc) = let
          val c_dsp = LM.lookup (c_displayPass, l)
          val a_dsp = LM.lookup (a_displayPass, l)
          val dsp_diff = (LS.listItems (LS.difference (c_dsp, a_dsp)))
      in List.foldl (add_dsp l) acc dsp_diff end
      val missed = LS.foldl collectMissed [] callSites
      fun collectBad (l, acc) = let
          val c_dsp = LM.lookup (c_displayPass, l)
          val a_dsp = LM.lookup (a_displayPass, l)
          val dsp_diff = (LS.listItems (LS.difference (a_dsp, c_dsp)))
      in List.foldl (add_dsp l) acc dsp_diff end
      val bad = LS.foldl collectBad [] callSites
      fun count_dsp displayPass (l, acc) =
          acc + (LS.numItems (LM.lookup (displayPass, l)))
      val num_c_displayPass =
          LS.foldl (count_dsp c_displayPass) 0 callSites
      val num_a_displayPass =
          LS.foldl (count_dsp a_displayPass) 0 callSites
  in
      say_nums ("found display pass", num_a_displayPass, num_c_displayPass);
      (* this is verbose on the large examples *)
      (* say_list (WARN, "display pass not found", missed, label_label_toString); *)
      say_list (ERROR, "bad display pass", bad, label_label_toString);
      ()
  end

  (*
  (* Dump information related to the number and kind of frame merges. *)
  fun dumpFrameMerges (pinfo, C.CU (_, (lab0, _, _, _)),
                       a_lvarRelativeExtent, a_ldataRelativeExtent,
                       c_lvarRelativeExtent, c_ldataRelativeExtent) = let
      fun frame_merges (pinfo, lab0, ldataRelativeExtent, lvarRelativeExtent) = let
          fun do_ (l, acc) =
              if not (Label.same (l, lab0))
              then let
                  val l_up = PInfo.immediate_alloc_loc_ld pinfo l
                  fun ld_good ld =
                      if LS.member (LM.lookup (ldataRelativeExtent, ld), l)
                      then LS.member (LM.lookup (ldataRelativeExtent, ld), l_up)
                      else true
                  fun lv_good x =
                      if LS.member (LVM.lookup (lvarRelativeExtent, x), l)
                      then LS.member (LVM.lookup (lvarRelativeExtent, x), l_up)
                      else true
              in if LS.all ld_good (PInfo.immediate_alloc_loc_ld pinfo l) andalso
                    LVS.all lv_good (PInfo.immediate_alloc_loc_ld pinfo l)
                 then l :: acc
                 else acc end
              else acc
      in List.foldl do_ [] (PInfo.lams pinfo) end
      val a_frame_merges =
          frame_merges (pinfo, lab0,
                        a_ldataRelativeExtent, a_lvarRelativeExtent)
      val num_a_frame_merges = List.length a_frame_merges
      val c_frame_merges =
          frame_merges (pinfo, lab0,
                        c_ldataRelativeExtent, c_lvarRelativeExtent)
      val num_c_frame_merges = List.length c_frame_merges
  in
      ST.Counter.bump (a_frame_merges_counter, num_a_frame_merges);
      ST.Counter.bump (c_frame_merges_counter, num_c_frame_merges);
      ()
  end
  *)

  (* Dump information related to the RSH extents of lvars and ldata. *)
  fun dumpExtents (
        lvars, ldata,
        s_lvarExtents, s_ldataExtents,
        a_lvarExtents, a_ldataExtents,
        c_lvarExtents, c_ldataExtents
      ) = let
      val res = ComparisonResults.createExtents
                  (fn x => x) (fn x => x)
                  (false, lvars, ldata,
                   s_lvarExtents, s_ldataExtents,
                   a_lvarExtents, a_ldataExtents,
                   c_lvarExtents, c_ldataExtents)
      val _ = extentResults :=
                ComparisonResults.createExtents
                  List.length List.length
                  (true, lvars, ldata,
                   s_lvarExtents, s_ldataExtents,
                   a_lvarExtents, a_ldataExtents,
                   c_lvarExtents, c_ldataExtents)
      val diff = difference LVar.same
      val missed_lv_S = diff (#stk(#trueLVars res), #stk(#analysisLVars res))
      val missed_lv_R = diff (#reg(#trueLVars res), #reg(#analysisLVars res))
      val bad_lv_S = diff (#stk(#analysisLVars res), #stk(#trueLVars res))
      val bad_lv_R = diff (#reg(#analysisLVars res), #reg(#trueLVars res))
      val bad_lv_S_syn = diff (#stk(#syntacticLVars res), #stk(#trueLVars res))
      val bad_lv_R_syn = diff (#reg(#syntacticLVars res), #reg(#trueLVars res))

      val diff = difference Label.same
      val missed_ld_S = diff (#stk(#trueLData res), #stk(#analysisLData res))
      val missed_ld_R = diff (#reg(#trueLData res), #reg(#analysisLData res))
      val bad_ld_S = diff (#stk(#analysisLData res), #stk(#trueLData res))
      val bad_ld_R = diff (#reg(#analysisLData res), #reg(#trueLData res))
      val bad_ld_S_syn = diff (#stk(#syntacticLData res), #stk(#trueLData res))
      val bad_ld_R_syn = diff (#reg(#syntacticLData res), #reg(#trueLData res))

      val num_a_lv_S = List.length (#stk(#analysisLVars res))
      val num_a_ld_S = List.length (#stk(#analysisLData res))
      val num_c_lv_S = List.length (#stk(#trueLVars res))
      val num_c_ld_S = List.length (#stk(#trueLData res))
      val num_a_lv_R = List.length (#reg(#analysisLVars res))
      val num_a_ld_R = List.length (#reg(#analysisLData res))
      val num_c_lv_R = List.length (#reg(#trueLVars res))
      val num_c_ld_R = List.length (#reg(#trueLData res))

      fun tick (name, cnt) = (cnt := (! cnt) + 1)
      fun tick_case (H_cntr, S_cntr, R_cntr, SR_cntr) ex =
          (case ex
            of ES.H => tick H_cntr
             | ES.HS => tick S_cntr
             | ES.HR => tick R_cntr
             | ES.HSR => tick SR_cntr
          (* end case *))
      fun tick_extent_counters (counters, map, app) = app (tick_case counters) map
      val (H_str, HS_str, HR_str, HSR_str) =
          (ES.toString ES.H, ES.toString ES.HS, ES.toString ES.HR, ES.toString ES.HSR)
      fun create_extent_counters (pre, post) = let
          fun c e = (pre ^ " " ^ e ^ " " ^ post, ref 0)
      in (c H_str, c HS_str, c HR_str, c HSR_str) end
      val s_lv_extent_counters =
          create_extent_counters ("LVar", "syntactic")
      val s_ld_extent_counters =
          create_extent_counters ("LData", "syntactic")
      val a_lv_extent_counters =
          create_extent_counters ("LVar", "analysis")
      val a_ld_extent_counters =
          create_extent_counters ("LData", "analysis")
      val c_lv_extent_counters =
          create_extent_counters ("LVar", "concrete")
      val c_ld_extent_counters =
          create_extent_counters ("LData", "concrete")
      fun say_cnt (msg, cnt) =
          if (! cnt) <> 0
          then (* pad to 7 digits *)
              say [StringCvt.padRight #" " 7 (Int.toString (! cnt)), msg, "\n"]
          else ()
      fun say_cnts (H_cntr, HS_cntr, HR_cntr, HSR_cntr) =
          (say_cnt H_cntr;
           say_cnt HS_cntr;
           say_cnt HR_cntr;
           say_cnt HSR_cntr;
           ())
  in
      tick_extent_counters (s_lv_extent_counters,
                            s_lvarExtents, LVM.app);
      tick_extent_counters (s_ld_extent_counters,
                            s_ldataExtents, LM.app);
      tick_extent_counters (a_lv_extent_counters,
                            a_lvarExtents, LVM.app);
      tick_extent_counters (a_ld_extent_counters,
                            a_ldataExtents, LM.app);
      tick_extent_counters (c_lv_extent_counters,
                            c_lvarExtents, LVM.app);
      tick_extent_counters (c_ld_extent_counters,
                            c_ldataExtents, LM.app);
      (*
      say_cnts s_lv_extent_counters;
      say ["----", "\n"];
      say_cnts a_lv_extent_counters;
      say ["----", "\n"];
      say_cnts c_lv_extent_counters;
      say ["===========================", "\n"];
      say_cnts s_ld_extent_counters;
      say ["----", "\n"];
      say_cnts a_ld_extent_counters;
      say ["----", "\n"];
      say_cnts c_ld_extent_counters;
      *)
      (*
      say_list (WARN, "lvars did not get extent " ^ Extent.suffix Extent.STK,
      lvarMissedStack, LVar.toString);
      say_list (WARN, "lvars did not get extent " ^ Extent.suffix Extent.REG,
      lvarMissedReg, LVar.toString);
      say_list (WARN, "ldatas did not get extent " ^ Extent.suffix Extent.STK,
      ldataMissedStack, Label.toString);
      say_list (WARN, "ldatas did not get extent " ^ Extent.suffix Extent.REG,
      ldataMissedReg, Label.toString);
      *)
      say_list (ERROR, "lvars got bad extent " ^ Extent.suffix Extent.STK,
                bad_lv_S, LVar.toString);
      say_list (ERROR, "lvars got bad extent " ^ Extent.suffix Extent.REG,
                bad_lv_R, LVar.toString);
      say_list (ERROR, "ldatas got bad extent " ^ Extent.suffix Extent.STK,
                bad_ld_S, Label.toString);
      say_list (ERROR, "ldatas got bad extent " ^ Extent.suffix Extent.REG,
                bad_ld_R, Label.toString);

      say_list (ERROR, "syn lvars got bad extent " ^ Extent.suffix Extent.STK,
                bad_lv_S_syn, LVar.toString);
      say_list (ERROR, "syn lvars got bad extent " ^ Extent.suffix Extent.REG,
                bad_lv_R_syn, LVar.toString);
      say_list (ERROR, "syn ldatas got bad extent " ^ Extent.suffix Extent.STK,
                bad_ld_S_syn, Label.toString);
      say_list (ERROR, "syn ldatas got bad extent " ^ Extent.suffix Extent.REG,
                bad_ld_R_syn, Label.toString);

      say_nums ("found lvar S",
                num_a_lv_S, num_c_lv_S);
      say_nums ("found ldata S",
                num_a_ld_S, num_c_ld_S);
      say_nums ("found lvar R",
                num_a_lv_R, num_c_lv_R);
      say_nums ("found ldata R",
                num_a_ld_R, num_c_ld_R);
      ()
  end

  (* Dump information related to the criteria for relative extent of lvars and ldata. *)
  fun dumpCriteria (pinfo, lvars, ldata,
                    a_lv_RelExt, a_ld_RelExt,
                    c_lv_RelExt, c_ld_RelExt,
                    a_lv_UCrit, a_ld_UCrit,
                    c_lv_UCrit, c_ld_UCrit,
                    a_lv_ECrit, a_ld_ECrit,
                    c_lv_ECrit, c_ld_ECrit) = let
      val res = ComparisonResults.create_criteria_t
                    (fn x => x) (fn x => x)
                    (pinfo, lvars, ldata,
                     a_lv_RelExt, a_ld_RelExt,
                     c_lv_RelExt, c_ld_RelExt,
                     a_lv_UCrit, a_ld_UCrit,
                     c_lv_UCrit, c_ld_UCrit,
                     a_lv_ECrit, a_ld_ECrit,
                     c_lv_ECrit, c_ld_ECrit)
      val _ = criteriaResults :=
              ComparisonResults.create_criteria_t
                  List.length List.length
                  (pinfo, lvars, ldata,
                   a_lv_RelExt, a_ld_RelExt,
                   c_lv_RelExt, c_ld_RelExt,
                   a_lv_UCrit, a_ld_UCrit,
                   c_lv_UCrit, c_ld_UCrit,
                   a_lv_ECrit, a_ld_ECrit,
                   c_lv_ECrit, c_ld_ECrit)

      val num_a_lv_RelExt = List.length (#analysis_rel_ext_lvar_pairs res)
      val num_c_lv_RelExt = List.length (#true_rel_ext_lvar_pairs res)
      val num_a_ld_RelExt = List.length (#analysis_rel_ext_ldata_pairs res)
      val num_c_ld_RelExt = List.length (#true_rel_ext_ldata_pairs res)

      val num_a_lv_UCrit = List.length (#analysis_uniq_crit_lvar_pairs res)
      val num_c_lv_UCrit = List.length (#true_uniq_crit_lvar_pairs res)
      val num_a_ld_UCrit = List.length (#analysis_uniq_crit_ldata_pairs res)
      val num_c_ld_UCrit = List.length (#true_uniq_crit_ldata_pairs res)
      val num_a_lv_ECrit = List.length (#analysis_ext_crit_lvar_pairs res)
      val num_c_lv_ECrit = List.length (#true_ext_crit_lvar_pairs res)
      val num_a_ld_ECrit = List.length (#analysis_ext_crit_ldata_pairs res)
      val num_c_ld_ECrit = List.length (#true_ext_crit_ldata_pairs res)

      fun same ((x1, lam1), (x2, lam2)) =
          LVar.same (x1, x2) andalso Label.same (lam1, lam2)
      val diff = difference same
      val missed_lv_UCrit =
          diff (#true_uniq_crit_lvar_pairs res, #analysis_uniq_crit_lvar_pairs res)
      val bad_lv_UCrit =
          diff (#analysis_uniq_crit_lvar_pairs res, #true_uniq_crit_lvar_pairs res)
      val missed_lv_ECrit =
          diff (#true_ext_crit_lvar_pairs res, #analysis_ext_crit_lvar_pairs res)
      val bad_lv_ECrit =
          diff (#analysis_ext_crit_lvar_pairs res, #true_ext_crit_lvar_pairs res)

      fun same ((ld1, lam1), (ld2, lam2)) =
          Label.same (ld1, ld2) andalso Label.same (lam1, lam2)
      val diff = difference same
      val missed_ld_UCrit =
          diff (#true_uniq_crit_ldata_pairs res, #analysis_uniq_crit_ldata_pairs res)
      val bad_ld_UCrit =
          diff (#analysis_uniq_crit_ldata_pairs res, #true_uniq_crit_ldata_pairs res)
      val missed_ld_ECrit =
          diff (#true_ext_crit_ldata_pairs res, #analysis_ext_crit_ldata_pairs res)
      val bad_ld_ECrit =
          diff (#analysis_ext_crit_ldata_pairs res, #true_ext_crit_ldata_pairs res)
  in
      (* these are verbose on the large examples *)
      (*
           say_list (WARN, "lvars did not get uniqueness crit",
                     missed_lv_UCrit, LVar.toString);
           say_list (WARN, "ldatas did not get uniqueness crit",
                     missed_ld_UCrit, Label.toString);
           say_list (WARN, "lvars did not get extent crit",
                     missed_lv_ECrit, LVar.toString);
           say_list (WARN, "ldata did not get extent crit",
                     missed_ld_ECrit, Label.toString);
      *)
      say_list (ERROR, "lvars got bad uniqueness crit",
                bad_lv_UCrit, lvar_label_toString);
      say_list (ERROR, "ldatas got bad uniqueness crit",
                bad_ld_UCrit, ldata_label_toString);
      say_list (ERROR, "lvars got bad extent crit",
                bad_lv_ECrit, lvar_label_toString);
      say_list (ERROR, "ldata got bad extent crit",
                bad_ld_ECrit, ldata_label_toString);
      (*
      say_nums ("found lvar relative extent",
                num_a_lv_RelExt, num_c_lv_RelExt);
      say_nums ("found ldata relative extent",
                num_a_ld_RelExt, num_c_ld_RelExt);
      say_nums ("found lvar uniqueness crit",
                     num_a_lv_UCrit, num_c_lv_UCrit);
      say_nums ("found ldata uniqueness crit",
                     num_a_ld_UCrit, num_c_ld_UCrit);
      say_nums ("found lvar extent crit",
                num_a_lv_ECrit, num_c_lv_ECrit);
      say_nums ("found ldata extent crit",
                num_a_ld_ECrit, num_c_ld_ECrit);
      *)
      ()
  end

  fun dumpValueInfo (const_msg, deconst_msg, consts, deconsts,
                     c_constToDeconst, a_constToDeconst,
                     c_deconstToConst, a_deconstToConst) = let
      fun handle_const (const, acc) = let
          val (a_labs, a_unknown) = LM.lookup (a_constToDeconst, const)
          val (c_labs, c_unknown) = LM.lookup (c_constToDeconst, const)
      in if (c_unknown andalso not a_unknown) orelse not (LS.isSubset (c_labs, a_labs))
         then (const, LS.difference (c_labs, a_labs)) :: acc
         else acc
      end
      fun handle_deconst (deconst, acc) = let
          val (a_labs, a_unknown) = LM.lookup (a_deconstToConst, deconst)
          val (c_labs, c_unknown) = LM.lookup (c_deconstToConst, deconst)
      in if (c_unknown andalso not a_unknown) orelse not (LS.isSubset (c_labs, a_labs))
         then (deconst, LS.difference (c_labs, a_labs)) :: acc
         else acc
      end

      val badConstToDeconst = List.foldl handle_const [] consts
      val badDeconstToConst = List.foldl handle_deconst [] deconsts
      fun ind (l, bad) = "[" ^ Label.toString l ^ " " ^ (String.concatWithMap " " Label.toString (LS.toList bad)) ^ "]"
      val () = say_list (ERROR, "bad " ^ const_msg ^ " to " ^ deconst_msg,
                         badConstToDeconst, ind)
      val () = say_list (ERROR, "bad " ^ deconst_msg ^ " to " ^ const_msg,
                         badDeconstToConst, ind)
  in () end

  fun dumpValueInfos (pinfo, ainfo, iinfo) = let
      val {tupleToSelect=a_tupleToSelect, selectToTuple=a_selectToTuple} = AInfo.tupleInfo ainfo
      val {tupleToSelect=c_tupleToSelect, selectToTuple=c_selectToTuple} = AInfo.tupleInfo iinfo
      val () = dumpValueInfo ("tuple", "select", PInfo.tuples pinfo, PInfo.selects pinfo,
                              c_tupleToSelect, a_tupleToSelect,
                              c_selectToTuple, a_selectToTuple)

      val {dataToMatch=a_dataToMatch, matchToData=a_matchToData} = AInfo.dataInfo ainfo
      val {dataToMatch=c_dataToMatch, matchToData=c_matchToData} = AInfo.dataInfo iinfo
      val () = dumpValueInfo ("data", "match", PInfo.datas pinfo, PInfo.matches pinfo,
                              c_dataToMatch, a_dataToMatch,
                              c_matchToData, a_matchToData)

      val {lamToCall=a_lamToCall, callToLam=a_callToLam} = AInfo.funInfo ainfo
      val {lamToCall=c_lamToCall, callToLam=c_callToLam} = AInfo.funInfo iinfo
      val () = dumpValueInfo ("lam", "call", PInfo.lams pinfo, PInfo.call_sites pinfo,
                              c_lamToCall, a_lamToCall,
                              c_callToLam, a_callToLam)

      val {lamKToCallK=a_lamKToCallK, callKToLamK=a_callKToLamK} = AInfo.funKInfo ainfo
      val {lamKToCallK=c_lamKToCallK, callKToLamK=c_callKToLamK} = AInfo.funKInfo iinfo
      val () = dumpValueInfo ("lamK", "callK", PInfo.lamKs pinfo, PInfo.callK_sites pinfo,
                              c_lamKToCallK, a_lamKToCallK,
                              c_callKToLamK, a_callKToLamK)
  in () end                              

  fun dumpEnvMatch (pinfo, ainfo, iinfo) = let
      val lvars = PInfo.lvars pinfo
      val cvars = PInfo.cvars pinfo
      val a_lvarEnvMatch = AInfo.lvarEnvMatch ainfo
      val c_lvarEnvMatch = AInfo.lvarEnvMatch iinfo
      fun handle_lvar (x, acc) = let
          val a_ls = LVM.lookup (a_lvarEnvMatch, x) handle _ => raise Fail "a_ls"
          val c_ls = LVM.lookup (c_lvarEnvMatch, x) handle _ => raise Fail "c_ls"
      in if not (LS.isSubset (a_ls, c_ls))
         then (x, LS.difference (a_ls, c_ls)) :: acc
         else acc
      end
      val badLVarEnvMatch = List.foldl handle_lvar [] lvars
      fun ind_lvar (x, ls) = "[" ^ LVar.toString x ^ " " ^ (String.concatWithMap " " Label.toString (LS.toList ls)) ^ "]"
      val () = say_list (ERROR, "bad lvar env match", badLVarEnvMatch, ind_lvar)
      fun find_fun_lvar (l, acc) = let
          val C.EXP (_, C.APPLY (f, _, _, _)) = PInfo.exp pinfo l
      in LVS.add (acc, f) end
      val fun_lvars = LVS.listItems (List.foldl find_fun_lvar LVS.empty (PInfo.call_sites pinfo))
      fun count_lvar lvarEnvMatch (x, acc) = acc + LS.numItems (LVM.lookup (lvarEnvMatch, x))
      val a_lvarEnvMatchCount = List.foldl (count_lvar a_lvarEnvMatch) 0 fun_lvars
      val c_lvarEnvMatchCount = List.foldl (count_lvar c_lvarEnvMatch) 0 fun_lvars
      val () = say_nums ("found lvar env match", a_lvarEnvMatchCount, c_lvarEnvMatchCount);

      val a_cvarEnvMatch = AInfo.cvarEnvMatch ainfo
      val c_cvarEnvMatch = AInfo.cvarEnvMatch iinfo
      fun handle_cvar (k, acc) = let
          val a_ls = CVM.lookup (a_cvarEnvMatch, k)
          val c_ls = CVM.lookup (c_cvarEnvMatch, k)
      in if not (LS.isSubset (a_ls, c_ls))
         then (k, LS.difference (a_ls, c_ls)) :: acc
         else acc
      end
      val badCVarEnvMatch = List.foldl handle_cvar [] cvars
      fun ind_cvar (k, ls) = "[" ^ CVar.toString k ^ " " ^ (String.concatWithMap " " Label.toString (LS.toList ls)) ^ "]"
      val () = say_list (ERROR, "bad cvar env match", badCVarEnvMatch, ind_cvar)
      val lamKs = PInfo.lamKs pinfo
      val funK_cvars = List.map (fn l => let val (k, _, _, _) = PInfo.lamK pinfo l in k end) lamKs
      fun count_cvar cvarEnvMatch (x, acc) = acc + LS.numItems (CVM.lookup (cvarEnvMatch, x))
      val a_cvarEnvMatchCount = List.foldl (count_cvar a_cvarEnvMatch) 0 funK_cvars
      val c_cvarEnvMatchCount = List.foldl (count_cvar c_cvarEnvMatch) 0 funK_cvars
      val () = say_nums ("found cvar env match", a_cvarEnvMatchCount, c_cvarEnvMatchCount);
  in () end


  (* Dump the comparisons between the analysis's and the interpreter's informations. *)
  fun dumpChecks (pinfo, cu as C.CU(_, lab0, _, _, _), ainfo_syntax, ainfo, iinfo) = let
      fun isSynH x = ExtentSet.extentOfLVar x = ExtentSet.H
      val lvarsToCheck = (* List.filter isSynH *) (PInfo.lvars pinfo)
      (* we may only want to look at variables that are bound...
         LVS.listItems (AInfo.lvarsBound iinfo) *)
      val ldataToCheck = PInfo.ldata pinfo
      val (s_lvarExtents, s_ldataExtents) =
          (AInfo.lvarExtents ainfo_syntax, AInfo.ldataExtents ainfo_syntax)
      val (a_lvarExtents, a_ldataExtents) =
          (AInfo.lvarExtents ainfo, AInfo.ldataExtents ainfo)
      fun restrict_map filteri base same check_lst =
          filteri (fn (x, _) => List.exists (fn (y) => same (x, y)) check_lst) base
      val s_lvarExtents =
          restrict_map LVM.filteri s_lvarExtents LVar.same lvarsToCheck
      val s_ldataExtents =
          restrict_map LM.filteri s_ldataExtents Label.same ldataToCheck
      val (c_lvarUniquenessCrit, c_ldataUniquenessCrit) =
          (AInfo.lvarUniquenessCrit iinfo, AInfo.ldataUniquenessCrit iinfo)
      fun crit_intersect (crit1, crit2, lst, empty, insert, lookup) = let
          fun add_element (x, acc) =
              insert (acc, x, LS.intersection (lookup (crit1, x), lookup (crit2, x)))
      in List.foldl add_element empty lst end
      val (c_crit_birth_lv, c_crit_birth_ld) =
          (AInfo.crit_birth_lv iinfo, AInfo.crit_birth_ld iinfo)
      val (c_crit_death_lv, c_crit_death_ld) =
          (AInfo.crit_death_lv iinfo, AInfo.crit_death_ld iinfo)
      val c_lvarExtentCrit =
          crit_intersect (c_crit_birth_lv, c_crit_death_lv, lvarsToCheck,
                          LVM.empty, LVM.insert, LVM.lookup)
      val c_ldataExtentCrit =
          crit_intersect (c_crit_birth_ld, c_crit_death_ld, ldataToCheck,
                          LM.empty, LM.insert, LM.lookup)

      fun lvarRelativeExtent_fromCrit (lvarUniquenessCrit, lvarExtentCrit) =
          crit_intersect (lvarUniquenessCrit, lvarExtentCrit, lvarsToCheck,
                          LVM.empty, LVM.insert, LVM.lookup)
      fun ldataRelativeExtent_fromCrit (ldataUniquenessCrit, ldataExtentCrit) =
          crit_intersect (ldataUniquenessCrit, ldataExtentCrit, ldataToCheck,
                          LM.empty, LM.insert, LM.lookup)

      val c_lvarRelativeExtent =
          lvarRelativeExtent_fromCrit (c_lvarUniquenessCrit, c_lvarExtentCrit)
      val c_ldataRelativeExtent =
          ldataRelativeExtent_fromCrit (c_ldataUniquenessCrit, c_ldataExtentCrit)
      val (a_lvarUniquenessCrit, a_ldataUniquenessCrit) =
          (AInfo.lvarUniquenessCrit ainfo, AInfo.ldataUniquenessCrit ainfo)

      val (a_crit_birth_lv, a_crit_birth_ld) =
          (AInfo.crit_birth_lv ainfo, AInfo.crit_birth_ld ainfo)
      val (a_crit_death_lv, a_crit_death_ld) =
          (AInfo.crit_death_lv ainfo, AInfo.crit_death_ld ainfo)
      val a_lvarExtentCrit =
          crit_intersect (a_crit_birth_lv, a_crit_death_lv, lvarsToCheck,
                          LVM.empty, LVM.insert, LVM.lookup)
      val a_ldataExtentCrit =
          crit_intersect (a_crit_birth_ld, a_crit_death_ld, ldataToCheck,
                          LM.empty, LM.insert, LM.lookup)
      (*
      val (a_lvarExtentCrit, a_ldataExtentCrit) =
          (AInfo.lvarExtentCrit ainfo, AInfo.ldataExtentCrit ainfo)
      *)
      val a_lvarRelativeExtent =
          lvarRelativeExtent_fromCrit (a_lvarUniquenessCrit, a_lvarExtentCrit)
      val a_ldataRelativeExtent =
          ldataRelativeExtent_fromCrit (a_ldataUniquenessCrit, a_ldataExtentCrit)
      val (c_lvarExtents, c_ldataExtents) = (AInfo.lvarExtents iinfo, AInfo.ldataExtents iinfo)
      val (a_lvarExtents, a_ldataExtents) = (AInfo.lvarExtents ainfo, AInfo.ldataExtents ainfo)
  in
      (*
      dumpFrameMerges (pinfo, cu,
                       a_lvarRelativeExtent, a_ldataRelativeExtent,
                       c_lvarRelativeExtent, c_ldataRelativeExtent);
      *)
      if true (* Controls.get Ctl.checkAnalysisExtentResults *)
      then (
      dumpExtents (lvarsToCheck, ldataToCheck,
                   s_lvarExtents, s_ldataExtents,
                   a_lvarExtents, a_ldataExtents,
                   c_lvarExtents, c_ldataExtents);
      dumpCriteria (pinfo, lvarsToCheck, ldataToCheck,
                    a_lvarRelativeExtent, a_ldataRelativeExtent,
                    c_lvarRelativeExtent, c_ldataRelativeExtent,
                    a_lvarUniquenessCrit, a_ldataUniquenessCrit,
                    c_lvarUniquenessCrit, c_ldataUniquenessCrit,
                    a_lvarExtentCrit, a_ldataExtentCrit,
                    c_lvarExtentCrit, c_ldataExtentCrit)
      )
      else ();
      dumpContInfo (pinfo, ainfo, iinfo);
      dumpCallWebs (pinfo, ainfo, iinfo);
      dumpDisplayPass (pinfo, cu, ainfo, ainfo_syntax, iinfo);
      dumpValueInfos (pinfo, ainfo, iinfo);
      dumpEnvMatch (pinfo, ainfo, iinfo);
      ()
  end

  (* dumps various information about the interpreter run *)
  fun dumpInfo (pinfo, cu, ainfo_syntax, ainfo, iinfo, (ds, count, expsSeen, lvarsBound)) = let
      val _ = ST.Counter.bump (concrete_states_counter, count)
      val exps = LS.fromList (PInfo.exps pinfo)
      val missedExps = LS.difference (exps, expsSeen)
      val lvars = LVS.fromList (PInfo.lvars pinfo)
      val missedLVars = LVS.difference (lvars, lvarsBound)
      val _ =
          if LS.isEmpty missedExps
          then say ["all expressions visited", "\n"]
          else (* TODO: perhaps check what kind of expressions were missed? *)
              ((*say_list (ANSIText.blue, "expressions not visited",
                             LS.listItems missedExps, Label.toString);*)
              say_nums ("expressions visited",
                        (LS.numItems exps) - (LS.numItems missedExps),
                        LS.numItems exps))
      val _ =
          if LVS.isEmpty missedLVars
          then say ["all lvars bound", "\n"]
          else
              (*
                   say_list (ANSIText.blue, "lvars not bound",
                   LVS.listItems miss  edLVars, LVar.toString)
              *)
              say_nums ("lvars bound",
                        (LVS.numItems lvars) - (LVS.numItems missedLVars),
                        LVS.numItems lvars)
      (* val _ = DumpAnalysis.dumpInterpreterExtentSummary (pinfo, ainfo_syntax, ainfo, count_lvar_alloc, count_lam_alloc); *)
  in () end

  (* By default, analysis information must be correct, and so empty.
     However, we want to start with everything and gradually remove things,
     so we re-initialize the values here. *)
  fun initialize_iinfo cu pinfo iinfo = let
      fun initial_crit_lv pinfo = let
          fun add alloc_loc (x, acc) =
              LVM.insert (acc, x, LS.add (LVM.lookup (acc, x), alloc_loc))
          fun handle_alloc_loc (alloc_loc, acc) =
              List.foldl (add alloc_loc) acc (PInfo.alloc_loc_choices_lv pinfo alloc_loc)
          val crit =
              List.foldl (fn (x, acc) => LVM.insert (acc, x, LS.empty)) LVM.empty (PInfo.lvars pinfo)
          val crit =
              List.foldl handle_alloc_loc crit (PInfo.alloc_locs pinfo)
      in crit end

      fun initial_crit_ld pinfo = let
          fun add alloc_loc (x, acc) =
              LM.insert (acc, x, LS.add (LM.lookup (acc, x), alloc_loc))
          fun handle_alloc_loc (alloc_loc, acc) =
              List.foldl (add alloc_loc) acc (PInfo.alloc_loc_choices_ld pinfo alloc_loc)
          val crit =
              List.foldl (fn (x, acc) => LM.insert (acc, x, LS.empty)) LM.empty (PInfo.ldata pinfo)
          val crit =
              List.foldl handle_alloc_loc crit (PInfo.alloc_locs pinfo)
      in crit end

      fun initial_relativePop pinfo = let
          fun add_call_site (call_site, acc) = LS.add (acc, call_site)
          val relativePop = LS.empty
          val relativePop = List.foldl add_call_site relativePop (PInfo.call_sites pinfo)
          val relativePop = List.foldl add_call_site relativePop (PInfo.callK_sites pinfo)
      in relativePop end

      fun initial_continuationOrder pinfo = let
          fun add_k (k, acc) = let
              val acc = CVM.insert (acc, k, PInfo.possible_leq_ks pinfo k)
          in acc end
          val continuationOrder =
              List.foldl add_k CVM.empty (PInfo.cvars pinfo)
      in continuationOrder end

      fun initial_tupleInfo (tuples, selects) = let
          val tupleToSelect = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty tuples
          val selectToTuple = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty selects
      in {tupleToSelect=tupleToSelect,
          selectToTuple=selectToTuple}
      end

      fun initial_dataInfo (datas, matches) = let
          val dataToMatch = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty datas
          val matchToData = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty matches
      in {dataToMatch=dataToMatch,
          matchToData=matchToData}
      end

      fun initial_funInfo (lams, calls) = let
          val lamToCall = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lams
          val callToLam = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty calls
      in {lamToCall=lamToCall,
          callToLam=callToLam}
      end

      fun initial_funKInfo (lamKs, callKs) = let
          val lamKToCallK = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty lamKs
          val callKToLamK = List.foldl (fn (x, acc) => LM.insert (acc, x, (LS.empty, false))) LM.empty callKs
      in {lamKToCallK=lamKToCallK,
          callKToLamK=callKToLamK}
      end

      fun init_envMatch (C.CU lam0) = let
          val lvarEnvMatch = ref LVM.empty
          val cvarEnvMatch = ref CVM.empty
          fun init_lvar (x, ls) = (lvarEnvMatch := (LVM.insert (!lvarEnvMatch, x, ls)))
          fun init_cvar (k, ls) = (cvarEnvMatch := (CVM.insert (!cvarEnvMatch, k, ls)))
          fun handle_exp (exp as C.EXP (lab_e, e), ls) =
              case e
               of C.LETFUN (bindings, body) =>
                  (List.app (fn (f, _, _, _, _) => init_lvar (f, ls)) bindings;
                   List.app (fn lam => handle_lam (lam, ls)) bindings; 
                   handle_exp (body, ls); 
                   ())
                | C.LETCONT (bindingKs, body) =>
                  (List.app (fn (k, _, _, _) => init_cvar (k, ls)) bindingKs;
                   List.app (fn lamK => handle_lamK (lamK, ls)) bindingKs; 
                   handle_exp (body, ls); 
                   ())
                | C.IF (oper, args, thn, els) =>
                  (handle_exp (thn, ls); handle_exp (els, ls); ())
                | C.ATOM (arg, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())
                | C.PURE (oper, args, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())
                | C.ARITH (oper, args, x, e', e_exn) =>
                  (init_lvar (x, ls); handle_exp (e', ls); handle_exp (e_exn, ls); ())
                | C.GET (oper, args, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())
                | C.SET (oper, args, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())

                | C.TUPLE(args, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())
                | C.SELECT(offset, arg, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())

                | C.DCAPPLY(dcon, tys, arg, x, e') =>
                  (init_lvar (x, ls); handle_exp (e', ls); ())
                | C.SWITCH(arg, pats) =>
                  (List.app (fn (pat, e') =>
                                ((case pat
                                   of C.VPAT x => init_lvar (x, ls)
                                    | C.DCPAT (_, _, SOME x) => init_lvar (x, ls)
                                    | _ => ());
                                 handle_exp (e', ls)))
                            pats;
                   ())
                | C.APPLY(f, tys, args, argKs) => ()
                | C.THROW (k, args) => ()
          and handle_lamK ((_, lamK_lab, xs, body), ls) = let
              val ls = LS.add (ls, lamK_lab)
          in List.app (fn x => init_lvar (x, ls)) xs;
             handle_exp (body, ls);
             ()
          end
          and handle_lam ((_, lam_lab, xs, ks, body), ls) = let
              val ls = LS.add (ls, lam_lab)
          in List.app (fn x => init_lvar (x, ls)) xs;
             List.app (fn k => init_cvar (k, ls)) ks;
             handle_exp (body, ls);
             ()
          end
          val () = handle_lam (lam0, LS.empty)
      in (!lvarEnvMatch, !cvarEnvMatch) end

      val (lvarEnvMatch, cvarEnvMatch) = init_envMatch (cu)

      fun initial_lvarEnvMatch pinfo = let
          (* val lvarEnvMatch = List.foldl (fn (x, acc) => LVM.insert (acc, x, LS.add (PInfo.cn_lv_lam pinfo x, PInfo.lam_lab0 pinfo))) LVM.empty (PInfo.lvars pinfo) *)
      in lvarEnvMatch end

      fun initial_cvarEnvMatch pinfo = let
          (* val cvarEnvMatch = List.foldl (fn (k, acc) => CVM.insert (acc, k, PInfo.cn_cv_lam pinfo k)) CVM.empty (PInfo.cvars pinfo) *)
      in cvarEnvMatch end

      (*
      val initial_callWebs =
          CallWebs.initial {lams=PInfo.lams pinfo, calls=PInfo.call_sites pinfo}
      val initial_callWebsK =
          CallWebs.initial {lams=PInfo.lamKs pinfo, calls=PInfo.callK_sites pinfo}
      *)
      val {user=initial_callWebs, cont=initial_callWebsK} =
          DetermineSyntacticCallWebs.callWebs (cu, {add_unknown=false})
      val iinfo = AInfo.with_lvarUniquenessCrit (iinfo, initial_crit_lv pinfo)
      val iinfo = AInfo.with_ldataUniquenessCrit (iinfo, initial_crit_ld pinfo)
      val iinfo = AInfo.with_lvarExtentCrit (iinfo, initial_crit_lv pinfo)
      val iinfo = AInfo.with_ldataExtentCrit (iinfo, initial_crit_ld pinfo)
      val iinfo = AInfo.with_crit_birth_lv (iinfo, initial_crit_lv pinfo)
      val iinfo = AInfo.with_crit_birth_ld (iinfo, initial_crit_ld pinfo)
      val iinfo = AInfo.with_crit_death_lv (iinfo, initial_crit_lv pinfo)
      val iinfo = AInfo.with_crit_death_ld (iinfo, initial_crit_ld pinfo)
      val iinfo = AInfo.with_callWebs (iinfo, initial_callWebs)
      val iinfo = AInfo.with_callWebsK (iinfo, initial_callWebsK)
      val iinfo = AInfo.with_relativePop (iinfo, initial_relativePop pinfo)
      val iinfo = AInfo.with_continuationOrder (iinfo, initial_continuationOrder pinfo)
      val iinfo = AInfo.with_tupleInfo (iinfo, initial_tupleInfo (PInfo.tuples pinfo, PInfo.selects pinfo))
      val iinfo = AInfo.with_dataInfo (iinfo, initial_dataInfo (PInfo.datas pinfo, PInfo.matches pinfo))
      val iinfo = AInfo.with_funInfo (iinfo, initial_funInfo (PInfo.lams pinfo, PInfo.call_sites pinfo))
      val iinfo = AInfo.with_funKInfo (iinfo, initial_funKInfo (PInfo.lamKs pinfo, PInfo.callK_sites pinfo))
      val iinfo = AInfo.with_lvarEnvMatch (iinfo, initial_lvarEnvMatch pinfo)
      val iinfo = AInfo.with_cvarEnvMatch (iinfo, initial_cvarEnvMatch pinfo)
  in iinfo end

  (* Interprets the program and gives back the interpreter information,
     as well as some extra information about the interpretation.
     The extra information is the return values and the number of
     transitions. *)
  fun run pinfo cu = let
      val (mutable_state, state0) = CTransition.initialState pinfo cu
      val trans = CTransition.transAndObtain pinfo mutable_state
      fun loop (state, iinfo, count) =
          case trans (state, iinfo)
           of (CTransition.TRANS state', iinfo') =>
              (if count mod 10000 = 0
               then Verbose.say ["Number of transitions: ", Int.toString count, "\n"]
               else ();
               loop (state', iinfo', count+1))
            | (CTransition.HALT ds, iinfo') => let
                val extra = (ds,
                             count,
                             ! (#expsSeen mutable_state),
                             ! (#lvarsBound mutable_state))
            in (iinfo', extra) end
      val iinfo = (AInfo.info pinfo cu)
      val res = if enabled ()
                then loop (state0, initialize_iinfo cu pinfo iinfo, 1)
                else (iinfo, ([], 0, Label.Set.empty, LVar.Set.empty))
  in res end

  (* Interprets the given program and checks the computed information
     against the analysis information *)
  fun interpretAndCheck (pinfo, cu, ainfo_syntax, ainfo) = let
      val (iinfo, extra) = run pinfo cu
      val iinfo = AnalysisInformationUtil.computeExtentMaps (cu, pinfo, iinfo)
  in
      lvarPromotionResults :=
      (PromotionDump.get (PInfo.lvars pinfo,
                          fn x => LVar.Map.lookup (#lvarExtents ainfo, x),
                          fn x => LVar.Map.lookup (#lvarExtents iinfo, x),
                          fn x => 1));
      ldataPromotionResults :=
      (PromotionDump.get (PInfo.ldata pinfo,
                          fn x => Label.Map.lookup (#ldataExtents ainfo, x),
                          fn x => Label.Map.lookup (#ldataExtents iinfo, x),
                          fn x => 1));
      dumpInfo (pinfo, cu, ainfo_syntax, ainfo, iinfo, extra);
      dumpChecks (pinfo, cu, ainfo_syntax, ainfo, iinfo);
      ()
  end

  fun getResults () = (!extentResults, !criteriaResults)

end
