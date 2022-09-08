(* cps-invariants.sml
 *
 * Checks the CPS IR for various invariants 
 *)

structure CPSInvariants : sig

  val check : CPS.comp_unit * CPSInformation.t -> unit

end = struct

  structure C = CPS
  structure PInfo = CPSInformation
  structure CVS = CVar.Set

  (* messages in verbose mode *)
    fun verbosePrint msg = if Controls.get Ctl.verbose
          then TextIO.output(TextIO.stdErr, concat msg)
          else ()

  fun lams_do_not_close_over_conts pinfo = let
      fun CVS_toString lvs = "{" ^ (String.concatWith ", " (List.map CVar.toString (CVS.listItems lvs))) ^ "}"
  in
      CheckCPS.run
          (fn say => 
              List.app
                  (fn l => let
                       val cvars = (PInfo.fv_lam_cv pinfo l)
                   in if CVar.Set.isEmpty cvars
                      then ()
                      else say ["lambda ", Label.toString l,
                                " closes over continuation variables: ", CVS_toString cvars, "\n"]
                   end)
                  (PInfo.lams pinfo))
  end

  fun check (cu, pinfo) = 
      (verbosePrint ["  Checking CPS Invariants ... "];
       lams_do_not_close_over_conts pinfo;
       verbosePrint ["done\n"])

end
