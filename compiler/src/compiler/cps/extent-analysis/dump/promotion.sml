
structure PromotionDump : sig
   
  type t = {HtoH : int,
            HtoS : int,
            HtoR : int,
            HtoSR : int,
            StoH : int,
            StoS : int,
            StoR : int,
            StoSR : int,
            RtoH : int,
            RtoS : int,
            RtoR : int,
            RtoSR : int,
            SRtoH : int,
            SRtoS : int,
            SRtoR : int,
            SRtoSR : int}
  
  val empty : t
  
  val get : ('a list) * ('a -> ExtentSet.t) * ('a -> ExtentSet.t) * ('a -> int) -> t
                 
end = struct

  structure E = ExtentSet
  
  type t = {HtoH : int,
            HtoS : int,
            HtoR : int,
            HtoSR : int,
            StoH : int,
            StoS : int,
            StoR : int,
            StoSR : int,
            RtoH : int,
            RtoS : int,
            RtoR : int,
            RtoSR : int,
            SRtoH : int,
            SRtoS : int,
            SRtoR : int,
            SRtoSR : int}
  
  val empty = {HtoH = 0,
               HtoS = 0,
               HtoR = 0,
               HtoSR = 0,
               StoH = 0,
               StoS = 0,
               StoR = 0,
               StoSR = 0,
               RtoH = 0,
               RtoS = 0,
               RtoR = 0,
               RtoSR = 0,
               SRtoH = 0,
               SRtoS = 0,
               SRtoR = 0,
               SRtoSR = 0}
  
  fun get (items, mark1, mark2, count) = let
      val HtoH = ref 0
      val HtoS = ref 0
      val HtoR = ref 0
      val HtoSR = ref 0
      val StoH = ref 0
      val StoS = ref 0
      val StoR = ref 0
      val StoSR = ref 0
      val RtoH = ref 0
      val RtoS = ref 0
      val RtoR = ref 0
      val RtoSR = ref 0
      val SRtoH = ref 0
      val SRtoS = ref 0
      val SRtoR = ref 0
      val SRtoSR = ref 0
      fun handleLVar x = let
          val cntr = (case (mark1 x, mark2 x)
                       of (E.H, E.H) => HtoH
                        | (E.H, E.HS) => HtoS
                        | (E.H, E.HR) => HtoR
                        | (E.H, E.HSR) => HtoSR
                        | (E.HS, E.H) => StoH
                        | (E.HS, E.HS) => StoS
                        | (E.HS, E.HR) => StoR
                        | (E.HS, E.HSR) => StoSR
                        | (E.HR, E.H) => RtoH
                        | (E.HR, E.HS) => RtoS
                        | (E.HR, E.HR) => RtoR
                        | (E.HR, E.HSR) => RtoSR
                        | (E.HSR, E.H) => SRtoH
                        | (E.HSR, E.HS) => SRtoS
                        | (E.HSR, E.HR) => SRtoR
                        | (E.HSR, E.HSR) => SRtoSR)
          fun incr cntr = (cntr := (!cntr + (count x)))
      in incr cntr end
  in List.app handleLVar items;
     {HtoH = !HtoH,
      HtoS = !HtoS,
      HtoR = !HtoR,
      HtoSR = !HtoSR,
      StoH = !StoH,
      StoS = !StoS,
      StoR = !StoR,
      StoSR = !StoSR,
      RtoH = !RtoH,
      RtoS = !RtoS,
      RtoR = !RtoR,
      RtoSR = !RtoSR,
      SRtoH = !SRtoH,
      SRtoS = !SRtoS,
      SRtoR = !SRtoR,
      SRtoSR = !SRtoSR}
  end

end
