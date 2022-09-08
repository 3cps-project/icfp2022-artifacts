(* information.sml
 *
 * The data structure for mangaging information produced by the analysis.
 *)

structure AnalysisInformationUtil : sig
  
  (* Compute the LVar and LData extent maps from the criteria *)
  val computeExtentMaps : CPS.comp_unit * CPSInformation.t * AnalysisInformation.t -> AnalysisInformation.t

end = struct

  structure C = CPS
  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map
  structure ES = ExtentSet

  (* Produces RSH extent maps from the relative extent information *)
  fun extentMaps (lab0, pinfo, lvars, ldata,
                  lvarExtentCrit, lvarUniquenessCrit,
                  ldataExtentCrit, ldataUniquenessCrit) = let
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


  fun computeExtentMaps (cu as C.CU(_, lab0, _, _, _), pinfo, ainfo) = let
      val lvars = PInfo.lvars pinfo
      val ldata = PInfo.ldata pinfo

      val (lvarUniquenessCrit, ldataUniquenessCrit) =
          (AInfo.lvarUniquenessCrit ainfo, AInfo.ldataUniquenessCrit ainfo)
      fun crit_intersect (crit1, crit2, lst, empty, insert, lookup) = let
          fun add_element (x, acc) =
              insert (acc, x, LS.intersection (lookup (crit1, x), lookup (crit2, x)))
      in List.foldl add_element empty lst end
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

      val lvarExtentCrit =
          crit_intersect (crit_birth_lv, crit_death_lv, lvars,
                          LVM.empty, LVM.insert, LVM.lookup)
      val ldataExtentCrit =
          crit_intersect (crit_birth_ld, crit_death_ld, ldata,
                          LM.empty, LM.insert, LM.lookup)

      val (lvarExtents, ldataExtents) =
          extentMaps (lab0, pinfo,
                      lvars, ldata,
                      lvarExtentCrit, lvarUniquenessCrit,
                      ldataExtentCrit, ldataUniquenessCrit)
      val ainfo = AInfo.with_lvarExtents (ainfo, lvarExtents)
      val ainfo = AInfo.with_ldataExtents (ainfo, ldataExtents)
  in ainfo end


end
