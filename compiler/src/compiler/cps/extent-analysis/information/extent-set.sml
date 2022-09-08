(* extent-set.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Representation of the lattice of extents: {H} U Fin({S,R})
 *)

structure ExtentSet : sig

    datatype t = H | HS | HR | HSR

    val fromExtent : Extent.t -> t

    val fmt : {color : bool} -> t -> string
    val toString : t -> string

  (* returns suffix for variable (i.e., "^H", "^S", "^R", or "^SR") *)
    val suffix : t -> string

    val join : t * t -> t

  (* return the "best" (i.e., lowest cost) extent from the set; H < S < R *)
    val best : t -> Extent.t

    val compare : t * t -> order

    val setAndJoinLVarExtent : LVar.t * t -> unit
    val extentOfLVar : LVar.t -> t
    val setAndJoinCVarExtent : CVar.t * t -> unit
    val extentOfCVar : CVar.t -> t

  end = struct

    datatype t = H | HS | HR | HSR

    fun fromExtent Extent.HEAP = H
      | fromExtent Extent.STK = HS
      | fromExtent Extent.REG = HR

    fun fmt {color} e = let
        (* Note that if color is disabled then ANSIText.fmt will not give back color *)
          fun wrap s c = if color
                then ANSIText.fmt ({fg=SOME c, bg=NONE, bf=true, ul=false}, s)
                else s
          val Hstr = wrap "H" ANSIText.green
          val Sstr = wrap "S" ANSIText.blue
          val Rstr = wrap "R" ANSIText.red
          val lst = (case e
                 of H => [Hstr]
                  | HS => [Hstr, Sstr]
                  | HR => [Hstr, Rstr]
                  | HSR => [Hstr, Sstr, Rstr]
                (* end case *))
          in
            concat ["{", String.concatWith "," lst, "}"]
          end

    val toString = fmt {color = true}

    fun suffix H = "^H"
      | suffix HS = "^S"
      | suffix HR = "^R"
      | suffix HSR = "^SR"

    fun join (H, x) = x
      | join (x, H) = x
      | join (x, y) = if (x = y) then x else HSR

    fun best H = Extent.HEAP
      | best HS = Extent.STK
      | best HR = Extent.REG
      | best HSR = Extent.REG

    fun compare (H, H) = EQUAL
      | compare (H, _) = LESS
      | compare (_, H) = GREATER
      | compare (HS, HS) = EQUAL
      | compare (HS, _) = LESS
      | compare (_, HS) = GREATER
      | compare (HR, HR) = EQUAL
      | compare (HR, _) = LESS
      | compare (_, HR) = GREATER
      | compare (HSR, HSR) = EQUAL

    (* lambda variable property to track extent sets *)
    local
        val {getFn, setFn, ...} = LVar.newProp (fn x => fromExtent(LVar.extentOf x))
    in
    fun setAndJoinLVarExtent (x, ex) = setFn(x, join(ex, getFn x))
    val extentOfLVar = getFn
    end

    (* continuation variable property to track extent sets *)
    local
        val {getFn, setFn, ...} = CVar.newProp (fn x => fromExtent(CVar.extentOf x))
    in
    fun setAndJoinCVarExtent (x, ex) = setFn(x, join(ex, getFn x))
    val extentOfCVar = getFn
    end

  end
