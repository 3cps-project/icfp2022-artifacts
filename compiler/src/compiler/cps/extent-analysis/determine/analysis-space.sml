(* analysis-space.sml
 *
 * Contains a type definition for determinations.
 *)

structure AnalysisSpace =
struct

  type t = {utilAddrs : Transition.util_addrs,
            pinfo : CPSInformation.t,
            cu : CPS.comp_unit,
            liveMemo : Live.t,
            state_space : StateSpace.t}

end
