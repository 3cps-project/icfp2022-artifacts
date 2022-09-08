(* determine.sig
 *
 * The signature for a information determination module.
 *)

signature DETERMINE_INFO = sig

    val determine : AnalysisSpace.t * AnalysisInformation.t -> AnalysisInformation.t

  end
