type point = int * int;

datatype seg = Seg of point * point;

fun sqr x = x * x;

fun abs i = if (i < 0) then ~i else i;

fun closerSqr (n, a, b) =
    if abs (sqr a - n) < abs (sqr b - n) then a
    else b;

fun intsqrt n =
    let fun s (lo, hi) =
            let val guess = (lo + hi) div 2
            in
                if sqr guess = n then
                    guess
                else if hi - lo = 1 then
                     closerSqr (n, lo, hi)
                else if sqr guess < n then
                    s (guess, hi)
                else
                    s (lo, guess)
            end
    in
        s (0, n div 2)
    end;

fun len s =
    case s
       of Seg (p1, p2) =>
          let val (x1, y1) = p1
              val (x2, y2) = p2
              val dx = x2 - x1
              val dy = y2 - y1
          in
              intsqrt (sqr dx + sqr dy)
          end;

val _ = len (Seg ((0,0), (3,4)))
