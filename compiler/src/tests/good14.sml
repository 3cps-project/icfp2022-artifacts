type z = int * int;

type quad = int * int * int;

datatype order = Less | Equal | Greater;

fun compare (n, n') =
     (if n < n' then Less
      else if n = n' then Equal
      else Greater);

fun sqr n = n*n;
fun abs n = if n < 0 then ~n else n;

fun intSqrt n = (* FIXME lame implementation *) n div 2;

fun disc (a,b,c) = sqr b - 4 * a * c;

(* solve : quad -> z list *)
fun solve (a,b,c) =
    let val disc = disc (a,b,c)
        val denom = 2 * a
        val rad = intSqrt (abs disc)
    in
      case compare (disc, 0)
        of Less =>
             let val re = ~b div denom
                 val im = rad div denom
             in
                 (re, im) :: (re, ~im) :: nil
             end
         | Equal   => (~b div denom, 0) :: nil
         | Greater => ((~b + rad) div denom, 0) ::
                      ((~b - rad) div denom, 0) ::
                      nil
    end;

val _ = solve (2, ~1, ~28)
