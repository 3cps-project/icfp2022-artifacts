
structure CPSInformation : sig

  type t

  val info : CPS.comp_unit -> t

  val lam_lab0 : t -> Label.t
  val exps : t -> Label.t list
  val tuples : t -> Label.t list
  val selects : t -> Label.t list
  val datas : t -> Label.t list
  val matches : t -> Label.t list
  val lams : t -> Label.t list
  val call_sites : t -> Label.t list
  val lamKs : t -> Label.t list
  val callK_sites : t -> Label.t list
  val lvars : t -> LVar.t list
  val cvars : t -> CVar.t list
  val ldata : t -> Label.t list
  val cdata : t -> Label.t list
  val ld_is_lam : t -> Label.t -> bool
  val cd_is_lamK : t -> Label.t -> bool
  val fv_exp_lv : t -> Label.t -> LVar.Set.set
  val fv_exp_cv : t -> Label.t -> CVar.Set.set
  val fv_lam_lv : t -> Label.t -> LVar.Set.set
  val fv_lam_cv : t -> Label.t -> CVar.Set.set
  val fv_lamK_lv : t -> Label.t -> LVar.Set.set
  val fv_lamK_cv : t -> Label.t -> CVar.Set.set
  val cn_lam_lv : t -> Label.t -> LVar.Set.set
  val cn_lam_cv : t -> Label.t -> CVar.Set.set
  val cn_lam_ld : t -> Label.t -> Label.Set.set
  val cn_lv_lam : t -> LVar.t -> Label.Set.set
  val cn_cv_lam : t -> CVar.t -> Label.Set.set
  val cn_ld_lam : t -> Label.t -> Label.Set.set
  val icn_lam_lv : t -> Label.t -> LVar.Set.set
  val icn_lam_cv : t -> Label.t -> CVar.Set.set
  val icn_lam_ld : t -> Label.t -> Label.Set.set
  val icn_lam_cd : t -> Label.t -> Label.Set.set
  val icn_lv_lam : t -> LVar.t -> Label.t
  val icn_cv_lam : t -> CVar.t -> Label.t
  val icn_ld_lam : t -> Label.t -> Label.t
  val icn_cd_lam : t -> Label.t -> Label.t
  val exp_lam : t -> Label.t -> Label.t
  val exp : t -> Label.t -> CPS.exp
  val lam : t -> Label.t -> CPS.lambda
  val lamK : t -> Label.t -> CPS.clambda
  val side_effect_labels : t -> Label.t list
  val pop_cvars : t -> Label.t -> CVar.t list

  val alloc_locs : t -> Label.t list
  val is_alloc_loc : t -> Label.t -> bool
  val alloc_loc_choices_lv : t -> Label.t -> LVar.t list
  val alloc_loc_choices_ld : t -> Label.t -> Label.t list
  val local_pop : t -> Label.t -> Label.t list
  val pop_past : t -> Label.t -> Label.t list
  val immediate_alloc_loc_lv : t -> LVar.t -> Label.t
  val immediate_alloc_loc_ld : t -> Label.t -> Label.t
  val immediate_lam_lv : t -> LVar.t -> Label.t
  val immediate_lam_ld : t -> Label.t -> Label.t
  val is_local_k : t -> CVar.t -> bool
  val k_index : t -> CVar.t -> int

  val possible_leq_ks : t -> CVar.t -> CVar.Set.set
  val leq_lamKs : t -> Label.t -> Label.Set.set

end = struct

  structure C = CPS
  structure CVT = CVar.Tbl
  structure LT = Label.Tbl
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map

  (* Local timers for profiling *)
  fun doTimer timer f =
      PhaseTimer.withTimer timer f ()
  val timerUtil = PhaseTimer.newPhase (Timers.timePInfo, "util")
  val timerFV = PhaseTimer.newPhase (Timers.timePInfo, "free vars")
  val timerCN = PhaseTimer.newPhase (Timers.timePInfo, "contains")
  val timerProxy = PhaseTimer.newPhase (Timers.timePInfo, "proxy")
  val timerCont = PhaseTimer.newPhase (Timers.timePInfo, "cont")
  val timerFrame = PhaseTimer.newPhase (Timers.timePInfo, "frame")

  type t = {
      lam_lab0 : Label.t,
      exps : Label.t list,
      tuples : Label.t list,
      selects : Label.t list,
      datas : Label.t list,
      matches : Label.t list,
      lams : Label.t list,
      call_sites : Label.t list,
      lamKs : Label.t list,
      callK_sites : Label.t list,
      lvars : LVar.t list,
      cvars : CVar.t list,
      ldata : Label.t list,
      cdata : Label.t list,
      fv_exp_lv  : LVS.set LT.hash_table,
      fv_exp_cv  : CVS.set LT.hash_table,
      fv_lam_lv : LVS.set LT.hash_table,
      fv_lam_cv : CVS.set LT.hash_table,
      fv_lamK_lv : LVS.set LT.hash_table,
      fv_lamK_cv : CVS.set LT.hash_table,
      cn_lam_lv : LVS.set LT.hash_table,
      cn_lam_cv : CVS.set LT.hash_table,
      cn_lam_ld : LS.set LT.hash_table,
      cn_lv_lam : LS.set LVM.map,
      cn_cv_lam : LS.set CVM.map,
      cn_ld_lam : LS.set LM.map,
      icn_lam_lv : LVS.set LT.hash_table,
      icn_lam_cv : CVS.set LT.hash_table,
      icn_lam_ld : LS.set LT.hash_table,
      icn_lam_cd : LS.set LT.hash_table,
      icn_lv_lam : Label.t LVM.map,
      icn_cv_lam : Label.t CVM.map,
      icn_ld_lam : Label.t LM.map,
      icn_cd_lam : Label.t LM.map,
      exp_lam : Label.t LT.hash_table,
      exp : C.exp LT.hash_table,
      lam : C.lambda LT.hash_table,
      lamK : C.clambda LT.hash_table,
      side_effect_labels : Label.t list,
      pop_cvars : (CVar.t list) Label.Tbl.hash_table,
      pop_labels : Label.Set.set,
      alloc_locs : Label.t list,
      alloc_loc_choices_lv : (LVar.t list) Label.Tbl.hash_table,
      alloc_loc_choices_ld : (Label.t list) Label.Tbl.hash_table,
      local_pop : (Label.t list) Label.Tbl.hash_table,
      pop_past : (Label.t list) Label.Tbl.hash_table,
      immediate_alloc_loc_lv : Label.t LVM.map,
      immediate_alloc_loc_ld : Label.t LM.map,
      immediate_lam_lv : Label.t LVM.map,
      immediate_lam_ld : Label.t LM.map,
      local_k : CVS.set,
      k_index : int CVT.hash_table,
      possible_leq_ks : CVS.set CVT.hash_table,
      leq_lamKs : LS.set LT.hash_table
  }

  structure Dump = struct

  structure D = DumpCPSInformation

  fun dump {lam_lab0=lam_lab0,
            exps, 
            tuples, selects,
            datas, matches,
            lams, call_sites, 
            lamKs, callK_sites,
            lvars, cvars,
            ldata, cdata,
            fv_exp_lv, fv_exp_cv,
            fv_lam_lv, fv_lam_cv,
            fv_lamK_lv, fv_lamK_cv,
            cn_lam_lv, cn_lam_cv, cn_lam_ld,
            cn_lv_lam, cn_cv_lam, cn_ld_lam,
            icn_lam_lv, icn_lam_cv, icn_lam_ld, icn_lam_cd,
            icn_lv_lam, icn_cv_lam, icn_ld_lam, icn_cd_lam,
            exp_lam, exp, lam, lamK,
            side_effect_labels,
            pop_cvars, pop_labels,
            alloc_locs, alloc_loc_choices_lv, alloc_loc_choices_ld, local_pop, pop_past,
            immediate_alloc_loc_lv, immediate_alloc_loc_ld,
            immediate_lam_lv, immediate_lam_ld,
            local_k, k_index,
            possible_leq_ks, leq_lamKs} =
      D.run (fn say => let
                 fun LV_list_toString lvs = "{" ^ (String.concatWith ", " (List.map LVar.toString lvs)) ^ "}"
                 fun CV_list_toString cvs = "{" ^ (String.concatWith ", " (List.map CVar.toString cvs)) ^ "}"
                 fun L_list_toString ls =  "{" ^ (String.concatWith ", " (List.map Label.toString ls)) ^ "}"
                 fun LVS_toString lvs = LV_list_toString (LVS.listItems lvs)
                 fun LS_toString ls = L_list_toString (LS.listItems ls)
                 fun LT_toString lt toString =
                     "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (Label.toString x) ^ " -> " ^ (toString y))
                                                             (LT.foldi (fn (x, y, acc) => (x, y) :: acc) [] lt)))
                     ^ "]"
                 fun LVM_toString lvm toString =
                     "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (LVar.toString x) ^ " -> " ^ (toString y))
                                                             (LVM.foldli (fn (x, y, acc) => (x, y) :: acc) [] lvm)))
                     ^ "]"
                 fun LM_toString lm toString =
                     "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (Label.toString x) ^ " -> " ^ (toString y))
                                                             (LM.foldli (fn (x, y, acc) => (x, y) :: acc) [] lm)))
                     ^ "]"
                 fun LT_toString lt toString =
                     "[" ^ (String.concatWith ", " (List.map (fn (x, y) => (Label.toString x) ^ " -> " ^ (toString y))
                                                             (LT.foldi (fn (x, y, acc) => (x, y) :: acc) [] lt)))
                     ^ "]"
             in
                 say ["lvars: ", LV_list_toString lvars, "\n"];
                 say ["cvars: ", CV_list_toString cvars, "\n"];
                 say ["ldata: ", L_list_toString ldata, "\n"];
                 say ["cdata: ", L_list_toString cdata, "\n"];
                 say ["lams: ", L_list_toString lams, "\n"];
                 say ["lamKs: ", L_list_toString lamKs, "\n"];
                 (*
                 say ["icn_lv_lam: ", LVM_toString icn_lv_lam Label.toString];
                 say ["pop_cvars: ", LT_toString pop_cvars CV_list_toString, "\n"];
                 say ["pop_labels: ", LS_toString pop_labels, "\n"];
                 *)
                 say ["local_pop: ", LT_toString local_pop L_list_toString, "\n"];
                 say ["pop past: ", LT_toString pop_past L_list_toString, "\n"];
                 say ["choices_lv: ", LT_toString alloc_loc_choices_lv LV_list_toString, "\n"];
                 ()
             end)

  end

  fun info cu = let
      val C.CU(_, lam_lab0, _, _, _) = cu
      val {exps, 
           tuples, selects,
           datas, matches,
           lams, call_sites, 
           lamKs, callK_sites,
           lvars, cvars,
           ldata, cdata,
           exp_lam, exp,
           lam, lamK,
           side_effect_labels} =
          doTimer timerUtil (fn () => InfoUtil.info cu)
      val {fv_exp_lv, fv_exp_cv,
           fv_lam_lv, fv_lam_cv,
           fv_lamK_lv, fv_lamK_cv} =
          doTimer timerFV (fn () => FreeVars.freeVars cu)
      val {cn_lam_lv=cn_lam_lv, cn_lam_cv=cn_lam_cv, cn_lam_ld=cn_lam_ld,
           icn_lam_lv=icn_lam_lv, icn_lam_cv=icn_lam_cv,
           icn_lam_ld=icn_lam_ld, icn_lam_cd=icn_lam_cd} =
          doTimer timerCN (fn () => Contains.contains cu)
      val {pop_cvars=pop_cvars, pop_labels = pop_labels} = Pop.pop cu
      val {alloc_locs, alloc_loc_choices_lv, alloc_loc_choices_ld, local_pop, pop_past,
           immediate_alloc_loc_lv, immediate_alloc_loc_ld, 
           immediate_lam_lv, immediate_lam_ld} =
          doTimer timerFrame (fn () => FrameInfo.info cu)
      val {local_k, k_index} =
          doTimer timerProxy (fn () => ProxyInformation.proxy_info cu)
      val {possible_leq_ks, leq_lamKs} =
          doTimer timerCont (fn () => LocalLeqContInformation.info cu)
      val icn_lv_lam = List.foldl (fn (lam_lab, map) =>
                                       LVS.foldl (fn (x, map) => LVM.insert (map, x, lam_lab))
                                                 map (LT.lookup icn_lam_lv lam_lab))
                                   LVM.empty lams
      val icn_cv_lam = List.foldl (fn (lam_lab, map) =>
                                       CVS.foldl (fn (k, map) => CVM.insert (map, k, lam_lab))
                                                 map (LT.lookup icn_lam_cv lam_lab))
                                   CVM.empty lams
      val icn_ld_lam = List.foldl (fn (lam_lab, map) =>
                                       LS.foldl (fn (ld, map) => LM.insert (map, ld, lam_lab))
                                                map (LT.lookup icn_lam_ld lam_lab))
                                   LM.empty lams
      val icn_cd_lam = List.foldl (fn (lam_lab, map) =>
                                       LS.foldl (fn (cd, map) => LM.insert (map, cd, lam_lab))
                                                map (LT.lookup icn_lam_cd lam_lab))
                                   LM.empty lams
      val cn_lv_lam = List.foldl (fn (lam_lab, map) =>
                                      LVS.foldl (fn (x, map) => LVM.insert (map, x, LS.add (LVM.lookup (map, x), lam_lab)))
                                                map (LT.lookup cn_lam_lv lam_lab))
                                  (List.foldl (fn (x, map) => LVM.insert (map, x, LS.empty)) LVM.empty lvars)
                                  lams
      val cn_cv_lam = List.foldl (fn (lam_lab, map) =>
                                      CVS.foldl (fn (k, map) => CVM.insert (map, k, LS.add (CVM.lookup (map, k), lam_lab)))
                                                map (LT.lookup cn_lam_cv lam_lab))
                                  (List.foldl (fn (k, map) => CVM.insert (map, k, LS.empty)) CVM.empty cvars)
                                  lams
      val cn_ld_lam = List.foldl (fn (lam_lab, map) =>
                                      LS.foldl (fn (ld, map) => LM.insert (map, ld, LS.add (LM.lookup (map, ld), lam_lab)))
                                               map (LT.lookup cn_lam_ld lam_lab))
                                  (List.foldl (fn (ld, map) => LM.insert (map, ld, LS.empty)) LM.empty ldata)
                                  lams
      val t = {lam_lab0=lam_lab0,
               exps=exps, 
               tuples=tuples, selects=selects,
               datas=datas, matches=matches,
               lams=lams, call_sites=call_sites, 
               lamKs=lamKs, callK_sites=callK_sites,
               lvars=lvars, cvars=cvars,
               ldata=ldata, cdata=cdata,
               fv_exp_lv=fv_exp_lv, fv_exp_cv=fv_exp_cv,
               fv_lam_lv=fv_lam_lv, fv_lam_cv=fv_lam_cv,
               fv_lamK_lv=fv_lamK_lv, fv_lamK_cv=fv_lamK_cv,
               cn_lam_lv=cn_lam_lv, cn_lam_cv=cn_lam_cv, cn_lam_ld=cn_lam_ld,
               cn_lv_lam=cn_lv_lam, cn_cv_lam=cn_cv_lam, cn_ld_lam=cn_ld_lam,
               icn_lam_lv=icn_lam_lv, icn_lam_cv=icn_lam_cv, icn_lam_ld=icn_lam_ld, icn_lam_cd=icn_lam_cd,
               icn_lv_lam=icn_lv_lam, icn_cv_lam=icn_cv_lam, icn_ld_lam=icn_ld_lam, icn_cd_lam=icn_cd_lam,
               pop_cvars=pop_cvars, pop_labels=pop_labels,
               exp_lam=exp_lam, exp=exp, lam=lam, lamK=lamK,
               side_effect_labels=side_effect_labels,
               alloc_locs=alloc_locs, alloc_loc_choices_lv=alloc_loc_choices_lv,
               alloc_loc_choices_ld=alloc_loc_choices_ld, local_pop=local_pop, pop_past=pop_past,
               immediate_alloc_loc_lv=immediate_alloc_loc_lv,
               immediate_alloc_loc_ld=immediate_alloc_loc_ld,
               immediate_lam_lv=immediate_lam_lv,
               immediate_lam_ld=immediate_lam_ld,
               local_k=local_k, k_index=k_index,
               possible_leq_ks=possible_leq_ks, leq_lamKs=leq_lamKs}
      val _ = Dump.dump t
  in
      t
  end

  exception InformationFail of string

  fun lam_lab0 ({lam_lab0, ...} : t) = lam_lab0
  fun exps ({exps, ...} : t) = exps
  fun tuples ({tuples, ...} : t) = tuples
  fun selects ({selects, ...} : t) = selects
  fun datas ({datas, ...} : t) = datas
  fun matches ({matches, ...} : t) = matches
  fun lams ({lams, ...} : t) = lams
  fun call_sites ({call_sites, ...} : t) = call_sites
  fun lamKs ({lamKs, ...} : t) = lamKs
  fun callK_sites ({callK_sites, ...} : t) = callK_sites
  fun lvars ({lvars, ...} : t) = lvars
  fun cvars ({cvars, ...} : t) = cvars
  fun ldata ({ldata, ...} : t) = ldata
  fun cdata ({cdata, ...} : t) = cdata
  fun ld_is_lam ({lams, ...} : t) ld =
      List.exists (fn lam => Label.same (ld, lam)) lams
  fun cd_is_lamK ({lamKs, ...} : t) cd =
      List.exists (fn lamK => Label.same (cd, lamK)) lamKs

  fun option_fail (opt, msg) =
      case opt
       of SOME res => res
        | NONE => (Verbose.say ["Information fail: ", msg, "\n"];
                   raise InformationFail msg)

  fun fv_exp_lv ({fv_exp_lv, ...} : t) l =
      option_fail (LT.find fv_exp_lv l, "fv_exp_lv")

  fun fv_exp_cv ({fv_exp_cv, ...} : t) l =
      option_fail (LT.find fv_exp_cv l, "fv_exp_cv")

  fun fv_lam_lv ({fv_lam_lv, ...} : t) l =
      option_fail (LT.find fv_lam_lv l, "fv_lam_lv")

  fun fv_lamK_lv ({fv_lamK_lv, ...} : t) l =
      option_fail (LT.find fv_lamK_lv l, "fv_lamK_lab_lv")

  fun fv_lam_cv ({fv_lam_cv, ...} : t) l =
      option_fail (LT.find fv_lam_cv l, "fv_lam_cv")

  fun fv_lam_lab_cv ({fv_lam_cv, ...} : t) l =
      option_fail (LT.find fv_lam_cv l, "fv_lam_cv")

  fun fv_lamK_lv ({fv_lamK_lv, ...} : t) l =
      option_fail (LT.find fv_lamK_lv l, "fv_lamK_lv")

  fun fv_lamK_cv ({fv_lamK_cv, ...} : t) l =
      option_fail (LT.find fv_lamK_cv l, "fv_lamK_cv")

  fun cn_lam_lv ({cn_lam_lv, ...} : t) l =
      option_fail (LT.find cn_lam_lv l, "cn_lam_lv")

  fun cn_lam_cv ({cn_lam_cv, ...} : t) l =
      option_fail (LT.find cn_lam_cv l, "cn_lam_cv")

  fun cn_lam_ld ({cn_lam_ld, ...} : t) l =
      option_fail (LT.find cn_lam_ld l, "cn_lam_ld")

  fun cn_lv_lam ({cn_lv_lam, ...} : t) x =
      option_fail (LVM.find (cn_lv_lam, x), "cn_lv_lam")

  fun cn_cv_lam ({cn_cv_lam, ...} : t) k =
      option_fail (CVM.find (cn_cv_lam, k), "cn_cv_lam")

  fun cn_ld_lam ({cn_ld_lam, ...} : t) l =
      option_fail (LM.find (cn_ld_lam, l), "cn_ld_lam")

  fun icn_lam_lv ({icn_lam_lv, ...} : t) l =
      option_fail (LT.find icn_lam_lv l, "icn_lam_lv")

  fun icn_lam_cv ({icn_lam_cv, ...} : t) l =
      option_fail (LT.find icn_lam_cv l, "icn_lam_cv")

  fun icn_lam_ld ({icn_lam_ld, ...} : t) l =
      option_fail (LT.find icn_lam_ld l, "icn_lam_ld")

  fun icn_lam_cd ({icn_lam_cd, ...} : t) l =
      option_fail (LT.find icn_lam_cd l, "icn_lam_cd")

  fun icn_lv_lam ({icn_lv_lam, ...} : t) x =
      option_fail (LVM.find (icn_lv_lam, x), "icn_lv_lam")

  fun icn_cv_lam ({icn_cv_lam, ...} : t) k =
      option_fail (CVM.find (icn_cv_lam, k), "icn_lv_lam")

  fun icn_ld_lam ({icn_ld_lam, ...} : t) l =
      option_fail (LM.find (icn_ld_lam, l), "icn_ld_lam")

  fun icn_cd_lam ({icn_cd_lam, ...} : t) l =
      option_fail (LM.find (icn_cd_lam, l), "icn_cd_lam")

  fun pop_cvars ({pop_cvars, ...} : t) l =
      option_fail (LT.find pop_cvars l, "pop_cvars")

  fun exp_lam ({exp_lam, ...} : t) l =
      option_fail (LT.find exp_lam l, "exp_lam")

  fun exp ({exp, ...} : t) l =
      option_fail (LT.find exp l, "exp")

  fun lam ({lam, ...} : t) l =
      option_fail (LT.find lam l, "lam")

  fun lamK ({lamK, ...} : t) l =
      option_fail (LT.find lamK l, "lamK")

  fun side_effect_labels ({side_effect_labels, ...} : t) = side_effect_labels

  fun alloc_locs ({alloc_locs, ...} : t) = alloc_locs

  fun is_alloc_loc ({alloc_locs, ...} : t) lab =
      List.exists (fn lab' => Label.same (lab, lab')) alloc_locs

  fun alloc_loc_choices_lv ({alloc_loc_choices_lv, ...} : t) l =
      option_fail (LT.find alloc_loc_choices_lv l, "alloc_loc_choices_lv")

  fun alloc_loc_choices_ld ({alloc_loc_choices_ld, ...} : t) l =
      option_fail (LT.find alloc_loc_choices_ld l, "alloc_loc_choices_lv")

  fun local_pop ({local_pop, ...} : t) l =
      option_fail (LT.find local_pop l, "local_pop")

  fun pop_past ({pop_past, ...} : t) l =
      option_fail (LT.find pop_past l, "pop_past")

  fun immediate_alloc_loc_lv ({immediate_alloc_loc_lv, ...} : t) x =
      option_fail (LVM.find (immediate_alloc_loc_lv, x), "immediate_alloc_loc_lv")

  fun immediate_alloc_loc_ld ({immediate_alloc_loc_ld, ...} : t) l =
      option_fail (LM.find (immediate_alloc_loc_ld, l), "immediate_alloc_loc_ld")

  fun immediate_lam_lv ({immediate_lam_lv, ...} : t) x =
      option_fail (LVM.find (immediate_lam_lv, x), "immediate_lam_lv")

  fun immediate_lam_ld ({immediate_lam_ld, ...} : t) l =
      option_fail (LM.find (immediate_lam_ld, l), "immediate_lam_ld")

  fun is_local_k ({local_k, ...} : t) k =
      CVS.member (local_k, k)
  fun k_index ({k_index, ...} : t) k =
      option_fail (CVT.find k_index k, "k_index")

  fun possible_leq_ks ({possible_leq_ks, ...} : t) k =
      option_fail (CVT.find possible_leq_ks k, "possible_leq_ks")

  fun leq_lamKs ({leq_lamKs, ...} : t) lamK_lab =
      option_fail (LT.find leq_lamKs lamK_lab, "leq_lamKs")

end
