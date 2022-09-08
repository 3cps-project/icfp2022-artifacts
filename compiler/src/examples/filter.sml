    fun revAppend (xs, ys) = (case xs of [] => ys | x::xr => revAppend (xr, x::ys))

    fun rev xs = revAppend (xs, [])

    fun filter f xs = let
          fun lp (xs, ys) = (case xs
                 of [] => rev ys
                  | x::xr => if f x then lp (xr, x::ys) else lp (xr, ys)
                (* end case *))
          in
            lp (xs, [])
          end;

    val x = filter (fn x => x) [true, false, true, true, false, false];
