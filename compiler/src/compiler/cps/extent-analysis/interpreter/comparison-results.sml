(* comparison-results.sml
 *
 * Determines the differences between the analysis's results and the interpreter's
 *)

structure ComparisonResults =
  struct

    structure LS = Label.Set
    structure LVM = LVar.Map
    structure LM = Label.Map

    structure PInfo = CPSInformation

  (* LData is the data analogue of LVar
     At the moment this is synonymous with ULambda.
     In the future, tuples, data values, etc. may also be included. *)

    type 'a var_info = {
        stk : 'a,
        reg : 'a
      }

    type ('a, 'b) extents = {
      (* the lvars that we are interested in obtaining extent
       * information for currently all lvars in the program
       *)
        totalLVars : 'a,
        syntacticLVars : 'a var_info,
        analysisLVars : 'a var_info,
        trueLVars : 'a var_info,
      (* the ldata that we are interested in obtaining extent
       * information for; currently all ldata in the program
       *)
        totalLData : 'b,
        syntacticLData : 'b var_info,
        analysisLData : 'b var_info,
        trueLData : 'b var_info
      }

(*
    type ('a, 'b) extent_t = {
        (* the lvars that we are interested in obtaining extent information for.
           currently all lvars in the program *)
        total_lvars : 'a,
        syntactic_S_lvars : 'a,
        syntactic_R_lvars : 'a,
        analysis_S_lvars : 'a,
        analysis_R_lvars : 'a,
        true_S_lvars : 'a,
        true_R_lvars : 'a,

        (* the ldata that we are interested in obtaining extent information for.
           currently all ldata in the program *)
        total_ldata : 'b,
        syntactic_S_ldata : 'b,
        syntactic_R_ldata : 'b,
        analysis_S_ldata : 'b,
        analysis_R_ldata : 'b,
        true_S_ldata : 'b,
        true_R_ldata : 'b
      }
*)

    (* A criteria pair is a pair of an allocation (lvar binding or
       ldata) and a ulambda to allocate on *)
    type ('a, 'b) criteria_t = {
      (* all lvar * ulam pairs, where the lvar is lexically contained in the ulam *)
        total_criteria_lvar_pairs : 'a,
        analysis_rel_ext_lvar_pairs : 'a,
        analysis_uniq_crit_lvar_pairs : 'a,
        analysis_ext_crit_lvar_pairs : 'a,
        true_rel_ext_lvar_pairs : 'a,
        true_uniq_crit_lvar_pairs : 'a,
        true_ext_crit_lvar_pairs : 'a,
      (* all ldata * ulam pairs, where the ldata is lexically contained in the ulam *)
        total_criteria_ldata_pairs : 'b,
        analysis_rel_ext_ldata_pairs : 'b,
        analysis_uniq_crit_ldata_pairs : 'b,
        analysis_ext_crit_ldata_pairs : 'b,
        true_rel_ext_ldata_pairs : 'b,
        true_uniq_crit_ldata_pairs : 'b,
        true_ext_crit_ldata_pairs : 'b
      }

  (* creates the extents information *)
    fun createExtents
        (create_lv : LVar.t list -> 'a)
        (create_ld : Label.t list -> 'b)
        ( for_json, lvars, ldata,
          s_lvarExtents, s_ldataExtents, (* syntactic maps *)
          a_lvarExtents, a_ldataExtents, (* analysis maps *)
          c_lvarExtents, c_ldataExtents  (* "concrete" maps *)
        ) = let
          fun getSR (x, ex, (stk, reg)) = (case ex
               of ExtentSet.HR => (stk, x :: reg)
                | ExtentSet.HS => (x :: stk, reg)
                | ExtentSet.HSR => if for_json then (stk, x :: reg) else (x :: stk, x :: reg)
                | _ => (stk, reg))
          fun mk create (stk, reg) = {stk = create stk, reg = create reg}
          in {
            totalLVars = create_lv lvars,
            syntacticLVars = mk create_lv (LVM.foldli getSR ([], []) s_lvarExtents),
            analysisLVars = mk create_lv (LVM.foldli getSR ([], []) a_lvarExtents),
            trueLVars = mk create_lv (LVM.foldli getSR ([], []) c_lvarExtents),
            totalLData = create_ld ldata,
            syntacticLData = mk create_ld (LM.foldli getSR ([], []) s_ldataExtents),
            analysisLData = mk create_ld (LM.foldli getSR ([], []) a_ldataExtents),
            trueLData = mk create_ld (LM.foldli getSR ([], []) c_ldataExtents)
          } end

    fun create_criteria_t (create_lv : (LVar.t * Label.t) list -> 'a)
                          (create_ld : (Label.t * Label.t) list -> 'b)
                          (pinfo, lvars, ldata,
                           a_lv_RelExt, a_ld_RelExt,
                           c_lv_RelExt, c_ld_RelExt,
                           a_lv_UCrit, a_ld_UCrit,
                           c_lv_UCrit, c_ld_UCrit,
                           a_lv_ECrit, a_ld_ECrit,
                           c_lv_ECrit, c_ld_ECrit
        ) = let
          fun add lookup (x, acc) = let
                val lams = lookup x
                in
                  LS.foldl (fn (lam, acc) => (x, lam) :: acc) acc lams
                end
          fun create lookup base = List.foldl (add lookup) [] base

          val total_criteria_lvar_pairs = create (PInfo.cn_lv_lam pinfo) lvars
          val analysis_rel_ext_lvar_pairs = create (fn x => LVM.lookup (a_lv_RelExt, x)) lvars
          val analysis_uniq_crit_lvar_pairs = create (fn x => LVM.lookup (a_lv_UCrit, x)) lvars
          val analysis_ext_crit_lvar_pairs = create (fn x => LVM.lookup (a_lv_ECrit, x)) lvars
          val true_rel_ext_lvar_pairs = create (fn x => LVM.lookup (c_lv_RelExt, x)) lvars
          val true_uniq_crit_lvar_pairs = create (fn x => LVM.lookup (c_lv_UCrit, x)) lvars
          val true_ext_crit_lvar_pairs = create (fn x => LVM.lookup (c_lv_ECrit, x)) lvars

          val total_criteria_ldata_pairs = create (PInfo.cn_ld_lam pinfo) ldata
          val analysis_rel_ext_ldata_pairs = create (fn x => LM.lookup (a_ld_RelExt, x)) ldata
          val analysis_uniq_crit_ldata_pairs = create (fn x => LM.lookup (a_ld_UCrit, x)) ldata
          val analysis_ext_crit_ldata_pairs = create (fn x => LM.lookup (a_ld_ECrit, x)) ldata
          val true_rel_ext_ldata_pairs = create (fn x => LM.lookup (c_ld_RelExt, x)) ldata
          val true_uniq_crit_ldata_pairs = create (fn x => LM.lookup (c_ld_UCrit, x)) ldata
          val true_ext_crit_ldata_pairs = create (fn x => LM.lookup (c_ld_ECrit, x)) ldata
          in {
              total_criteria_lvar_pairs=create_lv total_criteria_lvar_pairs,
              analysis_rel_ext_lvar_pairs=create_lv analysis_rel_ext_lvar_pairs,
              analysis_uniq_crit_lvar_pairs=create_lv analysis_uniq_crit_lvar_pairs,
              analysis_ext_crit_lvar_pairs=create_lv analysis_ext_crit_lvar_pairs,
              true_rel_ext_lvar_pairs=create_lv true_rel_ext_lvar_pairs,
              true_uniq_crit_lvar_pairs=create_lv true_uniq_crit_lvar_pairs,
              true_ext_crit_lvar_pairs=create_lv true_ext_crit_lvar_pairs,

              total_criteria_ldata_pairs=create_ld total_criteria_ldata_pairs,
              analysis_rel_ext_ldata_pairs=create_ld analysis_rel_ext_ldata_pairs,
              analysis_uniq_crit_ldata_pairs=create_ld analysis_uniq_crit_ldata_pairs,
              analysis_ext_crit_ldata_pairs=create_ld analysis_ext_crit_ldata_pairs,
              true_rel_ext_ldata_pairs=create_ld true_rel_ext_ldata_pairs,
              true_uniq_crit_ldata_pairs=create_ld true_uniq_crit_ldata_pairs,
              true_ext_crit_ldata_pairs=create_ld true_ext_crit_ldata_pairs
          } end

  end
