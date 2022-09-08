(* cf-nfa.sml
 *
 * NFA control flow
 *)

structure CF_NFA :> ADDR
    where type var = CVar.t
    where type info = Env.t
  = struct

    type var = CVar.t

    type t = CVar.t

    type info = Env.t

    fun alloc (k : CVar.t, _) = k

    fun toString k = let
          val i = Word.toIntX (CVar.hash k)
          val bg = 4
          val fg = i mod 7
          val fg = if fg >= bg then fg+1 else fg
          in
            ANSIText.fmt ({fg=SOME fg, bg=SOME bg, bf=true, ul=true}, (CVar.toString k))
          end

    val same = CVar.same
    val compare = CVar.compare
    val hash = CVar.hash

    structure Map = CVar.Map
    structure Set = CVar.Set
    structure Tbl = CVar.Tbl

  end
