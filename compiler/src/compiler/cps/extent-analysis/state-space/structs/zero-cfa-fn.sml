(* zero-cfa-fn.sml
 *
 * A 0-CFA address allocator.
 *)

functor ZeroCFAFn (
    structure Var : CPS_VAR
    structure Ignore : sig
        type t
    end
  ) :> ADDR
       where type var = Var.t
       where type info = Ignore.t
  = struct

    type var = Var.t

    type t = Var.t

    type info = Ignore.t

    fun alloc (x : Var.t, _) = x

    fun index _ = raise Fail "AddrProxy.index"
    fun fromIndex _ = raise Fail "AddrProxy.fromIndex"

    fun toString x = let
          val i = Word.toIntX (Var.hash x)
          val bg = 4
          val fg = i mod 7
          val fg = if fg >= bg then fg+1 else fg
          in
            ANSIText.fmt ({fg=SOME fg, bg=SOME bg, bf=true, ul=true}, (Var.toString x))
          end

    val same = Var.same
    val compare = Var.compare
    val hash = Var.hash

    structure Map = Var.Map
    structure Set = Var.Set
    structure Tbl = Var.Tbl

  end
