fun partition (pivot, xs) = let
      fun lp (xs, lte, gt) = (case xs
             of [] => (lte, gt)
              | x::xr => if (x <= pivot)
                  then lp (xr, x::lte, gt)
                  else lp (xr, lte, x::gt)
            (* end case *))
      in
        lp (xs, [], [])
      end;

(* NOTE: this is NOT tail recursive! *)
fun append (xs, ys) = (case xs
       of [] => ys
        | x::xr => x :: append(xr, ys)
      (* end case *));

fun qs xs = (case xs
       of [] => []
        | [x] => [x]
        | x::xr => let
            val (lte, gt) = partition (x, xr)
            in
              append (qs lte, x :: qs gt)
            end
      (* end case *));

(* A list of 100 random integers bewtween [1, 100] *)
val unsorted = [63,56,19,73,8,
                60,27,21,89,18,
                96,9,14,57,33,
                90,53,90,97,73,
                62,58,60,2,50,
                1,76,44,75,5,
                60,17,7,96,29,
                61,71,88,55,22,
                100,10,45,76,89,
                81,98,6,60,31,
                45,78,99,98,9,
                8,68,49,78,13,
                19,64,77,7,21,
                21,43,86,2,59,
                7,59,88,38,24,
                86,59,38,54,36,
                4,66,44,66,60,
                98,14,10,25,73,
                87,41,4,9,13,
                96,39,43,15,46]

val sorted = qs (unsorted)
