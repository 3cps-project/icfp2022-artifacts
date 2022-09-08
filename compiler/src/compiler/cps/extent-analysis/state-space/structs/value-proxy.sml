(* value-proxy.sml
 *
 * TODO *)

structure ValueProxy (* : VALUE_BASE with type t = Proxy.Set.set *) = 
struct

    structure PS = Proxy.Set

    type t = PS.set * bool

    fun empty () = (PS.empty, false)
    val unknown = (PS.empty, true)
    fun from_proxy (proxy) = (PS.singleton proxy, true)

    fun isEmpty (ps, un) = PS.isEmpty ps andalso not un

    fun join ((ps1, un1), (ps2, un2)) = (PS.union (ps1, ps2), un1 orelse un2)

    fun difference ((ps1, un1), (ps2, un2)) = (PS.difference (ps1, ps2), un1 andalso not un2)

    fun isUnknown ((_, un) : t) = un

    fun fold_proxy f base (ps, un) =
        Proxy.Set.foldl f base ps

    fun any_unknown (ps, un) = un

    fun fold f_proxy f_unknown base (ps, un) = let
        val base = if un then f_unknown base else base
        val base = Proxy.Set.foldl f_proxy base ps
    in base end

    fun compare ((ps1, un1), (ps2, un2)) =
        case (un1, un2)
         of (false, false) => PS.compare (ps1, ps2)
          | (true, true) => PS.compare (ps1, ps2)
          | (true, false) => GREATER
          | (false, true) => LESS

    fun toString (ps, un) =
        "[" ^ (String.concatWithMap " " Proxy.toString (PS.listItems ps)) ^ (if un then " unknown" else "") ^ "]"

    structure Key = struct type ord_key = t val compare = compare end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)

end
