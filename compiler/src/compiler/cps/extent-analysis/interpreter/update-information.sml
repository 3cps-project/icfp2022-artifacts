(* update-information.sml
 *
 * Updates the information the interpreter gathers.
 *)

structure UpdateInterpreterInformation : sig

  val update_lvarUniquenessCrit : (LVar.t list) * (CBinding.Set.set list) * (Frame.t list) * ((CBinding.t list) Frame.Tbl.hash_table) * (bool Frame.Tbl.hash_table) * AnalysisInformation.t -> AnalysisInformation.t 
  val update_ldataUniquenessCrit : (Label.t list) * (CValue.Set.set list) * (Frame.t list) * ((CValue.t list) Frame.Tbl.hash_table) * (bool Frame.Tbl.hash_table) * AnalysisInformation.t -> AnalysisInformation.t 
  val update_crit_death_lv : (CBinding.Set.set list) * (Frame.t list) * ((CBinding.t list) Frame.Tbl.hash_table) * AnalysisInformation.t -> AnalysisInformation.t 
  val update_crit_death_ld : (CValue.Set.set list) * (Frame.t list) * ((CValue.t list) Frame.Tbl.hash_table) * AnalysisInformation.t -> AnalysisInformation.t 

  val update_display_clo : CPSInformation.t -> (Label.t * (Frame.t list) * (Frame.t list) * AnalysisInformation.t) -> AnalysisInformation.t
  val update_display_cloK : CPSInformation.t -> (Label.t * (Frame.t list) * (Frame.t list) * AnalysisInformation.t) -> AnalysisInformation.t
  val update_display_halt : CPSInformation.t -> (Label.t * AnalysisInformation.t) -> AnalysisInformation.t
  val update_halt_values : CPSInformation.t -> (CBinding.Set.set list * CValue.Set.set list * AnalysisInformation.t) -> AnalysisInformation.t

  val update_relativePop : (Label.t * Frame.t list * AnalysisInformation.t) -> AnalysisInformation.t
  val update_continuationOrder : CPSInformation.t -> (CVar.t list * CEnvK.t * CStoreK.t * (Frame.t list) * AnalysisInformation.t) -> AnalysisInformation.t

  val update_tupleInfo : Label.t * CValue.t * AnalysisInformation.t -> AnalysisInformation.t
  val update_dataInfo : Label.t * CValue.t * AnalysisInformation.t -> AnalysisInformation.t
  val update_funInfo : Label.t * CValue.t * AnalysisInformation.t -> AnalysisInformation.t
  val update_funKInfo : Label.t * CValueK.t * AnalysisInformation.t -> AnalysisInformation.t
  val update_lvarEnvMatch : LVar.t * CValue.t * (Frame.t list) * AnalysisInformation.t -> AnalysisInformation.t
  val update_cvarEnvMatch : CVar.t * CValueK.t * (Frame.t list) * AnalysisInformation.t -> AnalysisInformation.t

end = struct

  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure CVM = CVar.Map
  structure LM = Label.Map

  structure AInfo = AnalysisInformation
  structure PInfo = CPSInformation
  structure U = CTransitionUtil

  structure BS = CBinding.Set
  structure VK = CValueK

  fun remove_crit_lv (crit_lv, x, alloc_loc) =
      LVM.insert (crit_lv, x, LS.subtract (LVM.lookup (crit_lv, x), alloc_loc))

  fun remove_crit_ld (crit_ld, ld, alloc_loc) =
      LM.insert (crit_ld, ld, LS.subtract (LM.lookup (crit_ld, ld), alloc_loc))

  fun update_lvarUniquenessCrit (xs, glb_lists, alloc_frms, frm_bindingAlloc, frm_live, iinfo) = 
      if not (Controls.get Ctl.checkAnalysisExtentResults)
      then iinfo
      else let
          val lvarUniquenessCrit = AInfo.lvarUniquenessCrit iinfo
          val crit_birth_lv = AInfo.crit_birth_lv iinfo
          fun handle_frm x (frm, (lvarUniquenessCrit, crit_birth_lv)) = let
              (* for each frame that is being allocated to *)
              val frm_lab = Frame.label frm
              val lvarUniquenessCrit = 
                  (* if (frm_lab, x) is a still good pair *)
                  if LS.member (LVM.lookup (lvarUniquenessCrit, x), frm_lab)
                  then
                      (* if there is a binding on frm over x that is still live, (frm_lab, x) is not a good pair *)
                      if (List.exists (fn (y, a) =>
                                          LVar.same (x, y) andalso
                                          List.exists (fn glb => BS.member (glb, (y, a))) glb_lists)
                                      (Frame.Tbl.lookup frm_bindingAlloc frm))
                      then remove_crit_lv (lvarUniquenessCrit, x, frm_lab)
                      else lvarUniquenessCrit
                  else lvarUniquenessCrit
              val crit_birth_lv = 
                  (* if (frm_lab, x) is a still good pair *)
                  if LS.member (LVM.lookup (crit_birth_lv, x), frm_lab)
                  then
                      (* if frm is not live, (frm_lab, x) is not a good pair *)
                      if not (Frame.Tbl.lookup frm_live frm)
                      then remove_crit_lv (crit_birth_lv, x, frm_lab)
                      else crit_birth_lv
                  else crit_birth_lv
          in (lvarUniquenessCrit, crit_birth_lv) end
          fun handle_lv (x, (lvarUniquenessCrit, crit_birth_lv)) =
              List.foldl (handle_frm x) (lvarUniquenessCrit, crit_birth_lv) alloc_frms
          val (lvarUniquenessCrit, crit_birth_lv) = 
              List.foldl handle_lv (lvarUniquenessCrit, crit_birth_lv) xs
          val iinfo = AInfo.with_lvarUniquenessCrit (iinfo, lvarUniquenessCrit)
          val iinfo = AInfo.with_crit_birth_lv (iinfo, crit_birth_lv)
      in iinfo end

  fun update_ldataUniquenessCrit (lds, gld_lists, alloc_frms, frm_ldataAlloc, frm_live, iinfo) = 
      if not (Controls.get Ctl.checkAnalysisExtentResults)
      then iinfo
      else let
          val ldataUniquenessCrit = AInfo.ldataUniquenessCrit iinfo
          val crit_birth_ld = AInfo.crit_birth_ld iinfo
          fun handle_frm ld (frm, (ldataUniquenessCrit, crit_birth_ld)) = let
              (* for each frame that is being allocated to *)
              val frm_lab = Frame.label frm
              val ldataUniquenessCrit =
                  (* if (frm_lab, ld) is a still good pair *)
                  if LS.member (LM.lookup (ldataUniquenessCrit, ld), frm_lab)
                  then
                      (* if there is a binding on frm over ld that is still live, (lab, ld) is not a good pair *)
                      if (List.exists (fn d' => CValue.hasLabel (d', ld) andalso
                                                List.exists (fn gld => CValue.Set.member (gld, d')) gld_lists)
                                      (Frame.Tbl.lookup frm_ldataAlloc frm))
                      then remove_crit_ld (ldataUniquenessCrit, ld, frm_lab) 
                      else ldataUniquenessCrit
                  else ldataUniquenessCrit
              val crit_birth_ld =
                  (* if (frm_lab, ld) is a still good pair *)
                  if LS.member (LM.lookup (crit_birth_ld, ld), frm_lab)
                  then
                      (* if frm is not live, (lab, ld) is not a good pair *)
                      if not (Frame.Tbl.lookup frm_live frm)
                      then remove_crit_ld (crit_birth_ld, ld, frm_lab) 
                      else crit_birth_ld
                  else crit_birth_ld
          in (ldataUniquenessCrit, crit_birth_ld) end
          fun handle_ld (ld, (ldataUniquenessCrit, crit_birth_ld)) =
              List.foldl (handle_frm ld) (ldataUniquenessCrit, crit_birth_ld) alloc_frms
          val (ldataUniquenessCrit, crit_birth_ld) = 
              List.foldl handle_ld (ldataUniquenessCrit, crit_birth_ld) lds
          val iinfo = AInfo.with_ldataUniquenessCrit (iinfo, ldataUniquenessCrit)
          val iinfo = AInfo.with_crit_birth_ld (iinfo, crit_birth_ld)
      in iinfo end

  fun update_crit_death_lv (glb_lists, popped_frms, frm_bindingAlloc, iinfo) = 
      if not (Controls.get Ctl.checkAnalysisExtentResults)
      then iinfo
      else let
          val crit_death_lv = AInfo.crit_death_lv iinfo
          (* val _ = Debug.say ["Popped frames: ", String.concatWithMap " " Frame.toString popped_frms, "\n"] *)
          fun handle_frm (frm, crit_death_lv) = let
              (* for each frame that is being popped *)
              val frm_lab = Frame.label frm
              val allocated = Frame.Tbl.lookup frm_bindingAlloc frm
              fun handle_bind ((x, a), crit_death_lv) =
                  ((* Debug.say ["Checking: ", CBinding.toString (x, a), " ", Frame.toString frm, "\n"];
                   let val glbs = (List.foldl (fn (glb, acc) => BS.listItems glb @ acc) [] glb_lists)
                   in Debug.say [String.concatWith " " (List.map CBinding.toString glbs), "\n"] end;
                   Debug.say [if List.exists (fn glb => BS.member (glb, (x, a))) glb_lists then "kill" else "no kill", "\n"]; *)
                   (* For each var such that (frm_lab, x) is still a good pair *)
                   (* if (frm_lab, x) is still a good pair and it is still live *)
                   if LS.member (LVM.lookup (crit_death_lv, x), frm_lab)
                      andalso
                      List.exists (fn glb => BS.member (glb, (x, a))) glb_lists
                   then ((* Debug.say ["Killing: ", LVar.toString x, "\n"]; *)
                         remove_crit_lv (crit_death_lv, x, frm_lab) )
                   else crit_death_lv)
              val crit_death_lv = List.foldl handle_bind crit_death_lv allocated
          in crit_death_lv end
          val crit_death_lv = List.foldl handle_frm crit_death_lv popped_frms
          val iinfo = AInfo.with_crit_death_lv (iinfo, crit_death_lv)
      in iinfo end
               
  fun update_crit_death_ld (gld_lists, popped_frms, frm_ldataAlloc, iinfo) = 
      if not (Controls.get Ctl.checkAnalysisExtentResults)
      then iinfo
      else let
          val crit_death_ld = AInfo.crit_death_ld iinfo
          fun handle_frm (frm, crit_death_ld) = let
              (* for each frm that is being popped *)
              val frm_lab = Frame.label frm
              val allocated = Frame.Tbl.lookup frm_ldataAlloc frm
              fun handle_value (d, crit_death_ld) =
                  (* For each value d such that (frm_lab, lab(d)) is still a good pair *)
                  case CValue.label d
                   of SOME ld =>
                      (* if (frm_lab, x) is still a good pair and it is still live *)
                      if LS.member (LM.lookup (crit_death_ld, ld), frm_lab)
                         andalso
                         List.exists (fn gld => CValue.Set.member (gld, d)) gld_lists
                      then remove_crit_ld (crit_death_ld, ld, frm_lab) 
                      else crit_death_ld
                    | NONE => crit_death_ld
              val crit_death_ld = List.foldl handle_value crit_death_ld allocated
          in crit_death_ld end
          val crit_death_ld = List.foldl handle_frm crit_death_ld popped_frms
          val iinfo = AInfo.with_crit_death_ld (iinfo, crit_death_ld)
      in iinfo end

  fun update_display_clo pinfo (call_lab, lexFrms_caller, lexFrms_callee, iinfo) = let
      val displayPass = AInfo.displayPass iinfo
      fun handle_frm (frm_caller, displayPass) =
          (* if frm_caller (available at the call site) is the same as 
             one for the callee, then do nothing, as it can be passed. 
             Otherwise, remove frm_caller's label from the call site *)
          if List.exists (fn frm_callee => Frame.same (frm_caller, frm_callee)) lexFrms_callee
          then displayPass
          else LM.insert (displayPass, call_lab, LS.subtract (LM.lookup (displayPass, call_lab), Frame.label frm_caller))
      (* NOTE: folding over lexFrms_callee is not the same for this check! *)
      val displayPass' = List.foldl handle_frm displayPass lexFrms_caller
      val iinfo = AInfo.with_displayPass (iinfo, displayPass')
  in iinfo end
                                                                                       
  fun update_display_cloK pinfo (throw_lab, lexFrms_caller, lexFrms_callee, iinfo) = let
      val displayPass = AInfo.displayPass iinfo
      fun handle_frm (frm_caller, displayPass) =
          (* if frm_caller (available at the call site) is the same as 
             one for the callee, then do nothing, as it can be passed. 
             Otherwise, remove frm_caller's label from the call site *)
          if List.exists (fn frm_callee => Frame.same (frm_caller, frm_callee)) lexFrms_callee
          then displayPass
          else LM.insert (displayPass, throw_lab, LS.subtract (LM.lookup (displayPass, throw_lab), Frame.label frm_caller))
      (* NOTE: folding over lexFrms_callee is not the same for this check! *)
      val displayPass' = List.foldl handle_frm displayPass lexFrms_caller
      val iinfo = AInfo.with_displayPass (iinfo, displayPass') 
  in iinfo end

  fun update_display_halt pinfo (throw_lab, iinfo) = let
      val displayPass = AInfo.displayPass iinfo
      val displayPass' = LM.insert (displayPass, throw_lab, LS.empty)
  in AInfo.with_displayPass (iinfo, displayPass') end

  fun update_halt_values pinfo (glb_list, gld_list, iinfo) = let
      (* remove every allocation contained in the lam from
         the lam as well as all frames contained in the lam *)
      fun killLam (lam_lab, crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) = let
          val cn_lv = PInfo.cn_lam_lv pinfo lam_lab
          val cn_ld = PInfo.cn_lam_ld pinfo lam_lab
          val to_remove = PInfo.cn_ld_lam pinfo lam_lab
          fun remove_from labs =
              LS.difference (labs, to_remove)
          fun killLV (x, crit_lv) =
              LVM.insert (crit_lv, x, remove_from (LVM.lookup (crit_lv, x)))
          fun killLD (ld, crit_ld) =
              LM.insert (crit_ld, ld, remove_from (LM.lookup (crit_ld, ld)))
          val crit_birth_lv = LVS.foldl killLV crit_birth_lv cn_lv
          val crit_birth_ld = LS.foldl killLD crit_birth_ld cn_ld
          val crit_death_lv = LVS.foldl killLV crit_death_lv cn_lv
          val crit_death_ld = LS.foldl killLD crit_death_ld cn_ld
      in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end

      fun killLVar (x, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) = let
          val crit_birth_lv = LVM.insert (crit_birth_lv, x, LS.empty)
          val crit_death_lv = LVM.insert (crit_death_lv, x, LS.empty)
      in (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) end

      fun killLData (ld, (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)) = let
          val crit_birth_ld = LM.insert (crit_birth_ld, ld, LS.empty)
          val crit_death_ld = LM.insert (crit_death_ld, ld, LS.empty)
      in if PInfo.ld_is_lam pinfo ld
         then killLam (ld, crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
         else (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld)
      end

      val acc = (AInfo.crit_birth_lv iinfo, AInfo.crit_birth_ld iinfo, AInfo.crit_death_lv iinfo, AInfo.crit_death_ld iinfo)
      val acc = List.foldl (fn (glb, acc) =>
                             BS.foldl (fn ((x, a), acc) => 
                                          killLVar (x, acc))
                                      acc glb)
                           acc glb_list
      val acc = List.foldl (fn (gld, acc) =>
                               CValue.Set.foldl (fn (d, acc) =>
                                                    case CValue.label d of
                                                        SOME ld => killLData (ld, acc)
                                                      | NONE => acc)
                                                acc gld)
                           acc gld_list
      val (crit_birth_lv, crit_birth_ld, crit_death_lv, crit_death_ld) = acc
      val iinfo = AInfo.with_crit_birth_lv (iinfo, crit_birth_lv)
      val iinfo = AInfo.with_crit_birth_ld (iinfo, crit_birth_ld)
      val iinfo = AInfo.with_crit_death_lv (iinfo, crit_death_lv)
      val iinfo = AInfo.with_crit_death_ld (iinfo, crit_death_ld)
  in iinfo end

  fun update_relativePop (call_site, poppedFrms, iinfo) = let
          fun remove () = let
              val relativePop = AInfo.relativePop iinfo
              val relativePop = LS.subtract (relativePop, call_site)
              val iinfo = AInfo.with_relativePop (iinfo, relativePop)
          in iinfo end
      in 
          if List.length poppedFrms = 1
          then iinfo
          else remove ()
      end

  fun update_continuationOrder pinfo (ks, envK, storeK, stack, iinfo) = let
          fun remove (map, k, k') =
              CVM.insert (map, k, CVS.subtract (CVM.lookup (map, k), k'))
          fun handle_cvars k (k', acc) = let
              val cont = U.evalCVar (k, envK, storeK)
              val cont' = U.evalCVar (k', envK, storeK)
              val (poppedFrms, stack_popped) = U.popFrms (CValueK.frms_lex cont, stack)
              val (poppedFrms', _) = U.popFrms (CValueK.frms_lex cont', stack)
              val acc =
                  (* should just be able to compute the number of popped frames *)
                  if (List.length poppedFrms) > (List.length poppedFrms')
                  then (* if k pops more than k', then k </= k' *)
                      remove (acc, k, k')
                  else acc
              val acc =
                  if List.length stack_popped = 0 (* unknown *)
                  then CVM.insert (acc, k, CVS.singleton k)
                  else acc
          in acc end
          val contOrder = AInfo.continuationOrder iinfo
          val contOrder = List.foldl (fn (k, acc) => List.foldl (handle_cvars k) acc ks)
                                     contOrder ks
          val iinfo = AInfo.with_continuationOrder (iinfo, contOrder)
      in iinfo end

  fun lm_add (lm, x, l) = let
      val (prev, unknown) = LM.lookup (lm, x)
      val lm = LM.insert (lm, x, (LS.add (prev, l), unknown))
  in lm end

  fun lm_add_unknown (lm, x) = let
      val (prev, unknown) = LM.lookup (lm, x)
      val lm = LM.insert (lm, x, (prev, true))
  in lm end

  fun update_tupleInfo (lab_select, d, iinfo) = let
      val lab_tuple = Option.valOf (CValue.label d) handle _ => raise Fail "tuple"
      val {tupleToSelect, selectToTuple} = AInfo.tupleInfo iinfo
      val tupleToSelect = lm_add (tupleToSelect, lab_tuple, lab_select)
      val selectToTuple = lm_add (selectToTuple, lab_select, lab_tuple)
      val iinfo = AInfo.with_tupleInfo (iinfo, {tupleToSelect=tupleToSelect, selectToTuple=selectToTuple})
  in iinfo end

  fun update_dataInfo (lab_match, d, iinfo) =
      (* we call this whenever we are in a match, and sometimes we match on literals *)
      case CValue.label d
       of SOME lab_data => let
           val {dataToMatch, matchToData} = AInfo.dataInfo iinfo
           val dataToMatch = lm_add (dataToMatch, lab_data, lab_match)
           val matchToData = lm_add (matchToData, lab_match, lab_data)
           val iinfo = AInfo.with_dataInfo (iinfo, {dataToMatch=dataToMatch, matchToData=matchToData})
       in iinfo end
        | NONE => iinfo

  fun update_funInfo (lab_call, d, iinfo) = let
      val lab_lam = Option.valOf (CValue.label d) handle _ => raise Fail "fun"
      val {lamToCall, callToLam} = AInfo.funInfo iinfo
      val lamToCall = lm_add (lamToCall, lab_lam, lab_call)
      val callToLam = lm_add (callToLam, lab_call, lab_lam)
      val iinfo = AInfo.with_funInfo (iinfo, {lamToCall=lamToCall, callToLam=callToLam})
  in iinfo end

  fun update_funKInfo (lab_callK, dK, iinfo) = let
      val {lamKToCallK, callKToLamK} = AInfo.funKInfo iinfo
  in
      case CValueK.label dK
       of NONE => let
           val callKToLamK = lm_add_unknown (callKToLamK, lab_callK)
           val iinfo = AInfo.with_funKInfo (iinfo, {lamKToCallK=lamKToCallK, callKToLamK=callKToLamK})
       in iinfo end
        | SOME lab_lamK => let
            val lamKToCallK = lm_add (lamKToCallK, lab_lamK, lab_callK)
            val callKToLamK = lm_add (callKToLamK, lab_callK, lab_lamK)
            val iinfo = AInfo.with_funKInfo (iinfo, {lamKToCallK=lamKToCallK, callKToLamK=callKToLamK})
        in iinfo end
  end

  fun update_lvarEnvMatch (x, d, lexFrms, iinfo) = let
      val lvarEnvMatch = #lvarEnvMatch iinfo
      val prev = LVM.lookup (lvarEnvMatch, x)
      val frms = Frame.Set.fromList lexFrms
      val frms_d = CValue.frms d
      val inter = Frame.Set.intersection (frms, frms_d)
      val ls = Frame.Set.foldl (fn (f, acc) => LS.add (acc, Frame.label f)) LS.empty inter
      (* val () = Verbose.say [LVar.toString x, " ", String.concatWithMap " " Label.toString (LS.listItems ls), "\n"]
      val () = Verbose.say [LVar.toString x, " ", String.concatWithMap " " Label.toString (LS.listItems prev), "\n"] *)
      val ls = LS.intersection (prev, ls)
      val lvarEnvMatch = LVM.insert (lvarEnvMatch, x, ls)
      val iinfo = AInfo.with_lvarEnvMatch (iinfo, lvarEnvMatch)
  in iinfo end

  fun update_cvarEnvMatch (k, dK, lexFrms, iinfo) = let
      val cvarEnvMatch = #cvarEnvMatch iinfo
      val prev = CVM.lookup (cvarEnvMatch, k)
      val frms = Frame.Set.fromList lexFrms
      val frms_d = CValueK.frms dK
      val inter = Frame.Set.intersection (frms, frms_d)
      val ls = Frame.Set.foldl (fn (f, acc) => LS.add (acc, Frame.label f)) LS.empty inter
      val ls = LS.intersection (prev, ls)
      val cvarEnvMatch = CVM.insert (cvarEnvMatch, k, ls)
      val iinfo = AInfo.with_cvarEnvMatch (iinfo, cvarEnvMatch)
  in iinfo end


end
