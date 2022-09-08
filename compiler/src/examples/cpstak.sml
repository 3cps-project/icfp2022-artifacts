(* adapted from the Larceny benchmark suite *)

fun cpstak (x, y, z) =
  let fun tak (x, y, z, k) =
        if (y >= x)
          then k z
          else tak (x - 1,
                    y,
                    z,
                    fn (v1) =>
                      tak (y - 1,
                           z,
                           x,
                           fn (v2) =>
                             tak (z - 1,
                                  x,
                                  y,
                                  fn (v3) =>
                                    tak (v1, v2, v3, k))))
  in
    tak (x, y, z, fn a => a)
  end;

(*
val result = cpstak (40, 20, 11);
*)
val result = cpstak (10, 5, 11);
