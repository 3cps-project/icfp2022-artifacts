(* SML implementation of Conway's Game of Life *)

structure List =
  struct

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

    fun map f xs = let
          fun mapf xs = (case xs of [] => [] | (x::xr) => f x :: mapf xr)
          in
            mapf xs
          end

    fun exists f xs = let
          fun existsf xs = (case xs
                 of [] => false
                  | (x::xr) => f x orelse existsf xr
                (* end case *))
          in
            existsf xs
          end

    fun filter f xs = let
          fun lp (xs, ys) = (case xs
                 of [] => rev ys
                  | x::xr => if f x then lp (xr, x::ys) else lp (xr, ys)
                (* end case *))
          in
            lp (xs, [])
          end

  end

structure Life = struct

    fun cons a x = a::x
    val map = List.map
    val rev = List.rev
    fun not b = if b then false else true
    fun compose f g x = f (g x)
    val exists = List.exists
    val filter = List.filter
    val length = List.length

    fun accumulate f = let
          fun foldf a xs = (case xs
                 of nil => a
                  | (b::x) => foldf (f a b) x
                (* end case *))
          in
            foldf
          end

    fun equal a b = (a = b)

    fun member x a = exists (equal a) x

    fun C f x y = f y x

    fun revonto x = accumulate (C cons) x

    local
      fun lexordset xs = (case xs
             of nil => nil
              | (a::x) => List.append(
                lexordset (filter (lexless a) x),
                a :: lexordset (filter (lexgreater a) x))
            (* end case *))
      and lexless (a1, b1) (a2, b2) =
            if a2<a1 then true else if a2=a1 then b2<b1 else false
      and lexgreater pr1 pr2 = lexless pr2 pr1
      fun collect f list = let
            fun accumf sofar xs = (case xs
                   of nil => sofar
                    | (a::x) => accumf (revonto sofar (f a)) x
                  (* end case *))
            in
              accumf nil list
            end
      fun occurs3 x = let
          (* finds coords which occur exactly 3 times in coordlist x *)
            fun f xover x3 x2 x1 xs = (case xs
                     of nil => diff x3 xover
                      | (a::x) =>
                          if member xover a then f xover x3 x2 x1 x
                          else if member x3 a then f (a::xover) x3 x2 x1 x
                          else if member x2 a then f xover (a::x3) x2 x1 x
                          else if member x1 a then f xover x3 (a::x2) x1 x
                          else f xover x3 x2 (a::x1) x
                    (* end case *))
            and diff x y = filter (compose not (member y)) x
            in
              f nil nil nil nil x
            end
    in

    datatype generation = GEN of (int*int) list

    fun alive (GEN livecoords) = livecoords
    fun mkgen coordlist = GEN (lexordset coordlist)
    fun mk_nextgen_fn neighbours gen = let
          val living = alive gen
          val isalive = member living
          val liveneighbours = compose length (compose (filter isalive) neighbours)
          fun twoorthree n = (n=2 orelse n=3)
          val survivors = filter (compose twoorthree liveneighbours) living
          val newnbrlist = collect (compose (filter (compose not isalive)) neighbours) living
          val newborn = occurs3 newnbrlist
          in
            mkgen (List.append (survivors, newborn))
          end

    end

    fun neighbours (i, j) = (i-1,j-1)::(i-1,j)::(i-1,j+1)::
          (i,j-1)::(i,j+1)::
          (i+1,j-1)::(i+1,j)::(i+1,j+1)::nil

    fun nthgen (g, i) = (case i
           of 0 => g
            | i => nthgen (mk_nextgen_fn neighbours g, i-1)
          (* end case *))

    val gun = mkgen [
            (2,20),(3,19),(3,21),(4,18),(4,22),(4,23),(4,32),(5,7),(5,8),(5,18),
            (5,22),(5,23),(5,29),(5,30),(5,31),(5,32),(5,36),(6,7),(6,8),(6,18),
            (6,22),(6,23),(6,28),(6,29),(6,30),(6,31),(6,36),(7,19),(7,21),(7,28),
            (7,31),(7,40),(7,41),(8,20),(8,28),(8,29),(8,30),(8,31),(8,40),(8,41),
            (9,29),(9,30),(9,31),(9,32)
          ]

    fun goGun n = (fn _ => ()) (nthgen(gun, n))

    val result = goGun 3

  end
