structure List =
  struct

    fun map f xs = let
          fun mapf xs = (case xs of [] => [] | (x::xr) => f x :: mapf xr)
          in
            mapf xs
          end

  end

structure A =
  struct

    val map = List.map

    val xs = let
          fun f x = (x, x)
          in
            (map f [1, 2, 3], map f [false, true])
          end

  end
