(* cps-interpreter.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The 3cps interpreter.
 *)



structure ThreeCPSInterpreter : sig

    val enabled : unit -> bool

    (* Interpret the program with respect to the given annotations
       and dump the results *)
    val interpret : CPSInformation.t * CPS.comp_unit * AnalysisInformation.t * AnalysisInformation.t -> unit

    val getAllocationResults : unit -> {lvar : PromotionDump.t, ldata : PromotionDump.t}

end = struct

  fun enabled () = (Controls.get Ctl.dumpAllocationSummary) orelse
                   (Controls.get Ctl.dumpCPSCoverage)

  structure C = CPS
  structure LVS = LVar.Set
  structure CVS = CVar.Set
  structure LS = Label.Set
  structure LVM = LVar.Map
  structure LVT = LVar.Tbl
  structure CVM = CVar.Map
  structure LM = Label.Map
  structure LT = Label.Tbl
  structure ST = Stats

  val lvarAllocationResults = ref PromotionDump.empty
  val ldataAllocationResults = ref PromotionDump.empty

  fun getAllocationResults () = {lvar = !lvarAllocationResults,
                                 ldata = !ldataAllocationResults}

  (* counters to track how many / what kind of updates are going on *)
  local
      val grp = ST.Group.newWithPri ST.Group.root ("analysis-check", [2, 1])
      val newCntr = ST.Counter.new grp
  in
  val interpreter_states_counter = newCntr ("interpreter states")
  end

  structure PInfo = CPSInformation
  structure AInfo = AnalysisInformation

  fun colorStr color msg = ANSIText.fmt ({fg=SOME color, bg=NONE, bf=true, ul=false}, msg)
  val say = DumpInterpreterSummary.say
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

  (* dumps various information about the interpreter run *)
  fun dumpInfo (pinfo, cu, ainfo_syntax, ainfo, (ds, count, heapSize, stackSize, stackKSize, expsSeen, lvarsBound, count_lvar_alloc, count_lam_alloc)) = let
      val _ = ST.Counter.bump (interpreter_states_counter, count)
      val exps = LS.fromList (PInfo.exps pinfo)
      val missedExps = LS.difference (exps, expsSeen)
      val lvars = LVS.fromList (PInfo.lvars pinfo)
      val missedLVars = LVS.difference (lvars, lvarsBound)
      val _ =
          if LS.isEmpty missedExps
          then say ["all expressions visited", "\n"]
          else (* TODO: perhaps check what kind of expressions were missed? *)
              ((* say_list (ANSIText.blue, "expressions not visited",
                         LS.listItems missedExps, Label.toString); *)
               let val format = {fg=SOME ANSIText.yellow, bg=NONE, bf=true, ul=false}
               in if Controls.get Ctl.dumpCPSCoverage
                  then (* LS.app (fn l => PrintCPS.formatLabel (l, format)) missedExps *) ()
                  else ()
               end;
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
      val () = say ["Transitions: ", Int.toString count, "\n"]
      val () = say ["Heap size: ", Int.toString heapSize, "\n"]
      val () = say ["Stack size: <= ", Int.toString stackSize, "\n"]
      val () = say ["StackK size: <= ", Int.toString stackKSize, "\n"]
      val _ = DumpAnalysis.dumpInterpreterExtentSummary (pinfo, ainfo_syntax, ainfo, count_lvar_alloc, count_lam_alloc);
      val () = lvarAllocationResults :=
               (PromotionDump.get (PInfo.lvars pinfo,
                                    fn x => LVM.lookup (#lvarExtents ainfo_syntax, x),
                                    fn x => LVM.lookup (#lvarExtents ainfo, x),
                                    LVT.lookup count_lvar_alloc))
      val () = ldataAllocationResults :=
               (PromotionDump.get (PInfo.ldata pinfo,
                                    fn x => LM.lookup (#ldataExtents ainfo_syntax, x),
                                    fn x => LM.lookup (#ldataExtents ainfo, x),
                                    LT.lookup count_lam_alloc))
  in () end

exception Bug of string

  (* Interprets the program and gives back the interpreter information,
     as well as some extra information about the interpretation.
     The extra information is the return values and the number of
     transitions. *)
  fun run pinfo cu ainfo = let
      val extents = AInfo.lvarExtents ainfo
      fun mark x = case LVM.find (extents, x)
                    of NONE => Extent.HEAP
                     | SOME ExtentSet.H => Extent.HEAP
                     | SOME ExtentSet.HS => Extent.STK
                     | SOME ExtentSet.HR => Extent.REG
                     | SOME ExtentSet.HSR => Extent.REG
                     (* | _ => Extent.HEAP *)
      val (mutable_state, state0) = ThreeCPSTransition.initialState pinfo mark cu
      val trans = ThreeCPSTransition.transAndObtain pinfo mark mutable_state
      fun loop (state, count, max_stack_pointer, max_stackK_pointer) =
          (case trans state
            of ThreeCPSTransition.TRANS state' =>
               (if count mod 10000 = 0
                then let
                    val heapSize = ! (#heap_pointer mutable_state) (* UnboundedArray.size (#heap mutable_state) *)
                    val stackSize = UnboundedArray.size (#stack mutable_state)
                    val stackKSize = UnboundedArray.size (#stackK mutable_state)
                in Verbose.say ["Number of transitions: ", Int.toString count, " ",
                                "Heap size: ", Int.toString heapSize, " ",
                                "Stack size: ", Int.toString (!(#stack_pointer mutable_state)), " <= ", Int.toString max_stack_pointer, " ",
                                "StackK size: ", Int.toString (!(#stackK_pointer mutable_state)), " <= ", Int.toString max_stackK_pointer, "\n"] end
                else ();
                let val lab_e = Label.toString (case #1 state of CPS.EXP (l, _) => l) in
                if List.exists (fn lab => lab_e = lab)
                               (["LF606", "LF2D1", "LF2C9", "LF2C4", "LF2C0"] @
                                ["L17424", "L175C1", "L175BE", "L175C6", "L175BC"])
                then Verbose.say ["In ", lab_e, " with ", Int.toString count, "\n"]
                else () end;
                loop (state', 
                      count+1,
                      Int.max (max_stack_pointer,
                               ! (#stack_pointer mutable_state)),
                      Int.max (max_stackK_pointer,
                               ! (#stackK_pointer mutable_state))))
             | ThreeCPSTransition.HALT ds => let
                 val _ = Verbose.say ["halt exp: ", Label.toString (case #1 state of CPS.EXP (l, _) => l), "\n"]
                 val _ = Verbose.say (["halt values: "] @ (List.map ThreeCPSValue.toString ds) @ ["\n"])
                 val extra = (ds,
                              count,
                              ! (#heap_pointer mutable_state), (* UnboundedArray.size (#heap mutable_state), *)
                              max_stack_pointer, (* UnboundedArray.size (#stack mutable_state), *)
                              max_stackK_pointer, (* UnboundedArray.size (#stackK mutable_state), *)
                              ! (#expsSeen mutable_state),
                              ! (#lvarsBound mutable_state),
                              (#count_lvar_alloc mutable_state),
                              (#count_lam_alloc mutable_state))
             in extra end)
          (* handle Fail (msg : string) => let
              val (exp as C.EXP (lab_e,e), env, envK, tenv) = state
              val stack_pointer = #stack_pointer mutable_state
              val heap_pointer = #heap_pointer mutable_state
              val registers = #registers mutable_state
              val stack = #stack mutable_state
              val heap = #heap mutable_state
              val stackK_pointer = #stackK_pointer mutable_state
              val stackK = #stackK mutable_state
              val lvarsBound = #lvarsBound mutable_state
              val expsSeen = #expsSeen mutable_state
              val () = expsSeen := LS.add (!expsSeen, lab_e)

              val current_stack_pointer = !stack_pointer
              val current_stackK_pointer = !stackK_pointer

              fun verbose_loop (array, max, index) =
                  if index < max
                  then (Verbose.say [Int.toString index, " ", ThreeCPSValue.toString (UnboundedArray.load (array, index)), "\n"];
                        verbose_loop (array, max, index+1))
                  else ()
              val () = Verbose.say ["------ iter ", Int.toString count, " ------------", "\n"]
              val () = Verbose.say [Label.toString lab_e, "\n"]
              val () = Verbose.say ["Heap", " ", Int.toString (!heap_pointer), "\n"]
              val () = verbose_loop (heap, !heap_pointer, 0)
              val () = CheckAnalysisResults.say ["Stack", "\n"]
              val () = verbose_loop (stack, current_stack_pointer, 0)
          in raise Bug (str #" ") end *)
      val res = if enabled ()
                then loop (state0, 1, 0, 0)
                else ([], 0, 0, 0, 0,
                      Label.Set.empty, LVar.Set.empty,
                      LVar.Tbl.mkTable(1, Fail "empty count_lvar_alloc"),
                      Label.Tbl.mkTable(1, Fail "empty count_lam_alloc"))
  in res end

  (* Interprets the given program and checks the computed information
     against the analysis information *)
  fun interpret (pinfo, cu, ainfo_syntax, ainfo) = let
      val extra = run pinfo cu ainfo
  in
      dumpInfo (pinfo, cu, ainfo_syntax, ainfo, extra)
  end


end
