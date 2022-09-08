(* classic nqueens *)

structure List = struct

    fun length xs = let
          fun lp (xs, n) = (case xs of [] => n | (_::r) => lp(r, n+1))
          in
            lp (xs, 0)
          end

    fun revAppend (xs, ys) = (case xs of [] => ys | x::xr => revAppend (xr, x::ys))

    fun rev xs = revAppend (xs, [])

    fun append (xs, ys) = (case (xs, ys)
           of ([], _) => ys
            | (_, []) => xs
            | _ => revAppend (rev xs, ys)
          (* end case *))

  end;

structure Queens= struct

    fun nsoln nq = let
          fun safe (x, d, qs) = (case qs
                 of [] => true
                  | q::l => x <> q andalso x <> (q+d) andalso x <> (q-d) andalso safe (x, d+1, l)
                (* end case *))
          fun gen n = if n = 0
              then [[]]
              else let
                val bs = gen (n-1)
                fun enumerate (q, acc) = if (q = 0)
                      then acc
                      else let
                        fun check (bs, acc) = (case bs
                               of [] => acc
                                | b::bs => if safe (q, 1, b)
                                    then check (bs, (q::b)::acc)
                                    else check (bs, acc)
                              (* end case *))
                        val res = check(bs, nil)
                        in
                          enumerate(q-1, List.append(res, acc))
                        end
                  in
                    enumerate (nq, nil)
                  end
          in
            List.length (gen nq)
          end

  end; (* end struct *)

val check = (Queens.nsoln 5 = 10);
