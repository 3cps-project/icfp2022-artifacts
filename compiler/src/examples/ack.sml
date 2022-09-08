(*
   A version of Ackermann function from Larcenry benchmarks: http://www.larcenists.org/benchmarksAboutR6.html
*)

fun ack (m,n) =
    if m = 0 then
        n+1
    else if n = 0 then
        ack (m - 1, 1)
    else
        ack(m - 1, ack (m, n - 1))

(*
val result = ack (3, 11)
*)
val result = ack (2, 5)

