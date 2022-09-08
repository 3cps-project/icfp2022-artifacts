(* tsp.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Travelling Salesman benchmark from SML/NJ benchmarks (originally from
 * the "Olden" benchmarks).
 *)

structure Math =
  struct
    val sqrt = sqrt
    val ln = ln
  end

(***** rand.sml *****)
structure Rand =
  struct

    val a = 48271
    val m = 2147483647  (* 2^31 - 1 *)
    val m_1 = m - 1
    val q = m div a
    val r = m mod a

    val randMin = 1
    val randMax = m_1

    fun chk seed = if (seed <= 0) then 1
          else if (seed > m_1) then m_1
          else seed

    fun random' seed = let
          val hi = seed div q
          val lo = seed mod q
          val test = a * lo - r * hi
          in
            if test > 0 then test else test + m
          end

    fun mkRandom seed = let
          val seed = ref (chk seed)
          in
            fn () => (seed := random' (!seed); !seed)
          end

    val scale = 1.0 / 2147483647.0
    fun norm s = scale * real s

  end (* Rand *)

(***** tree.sml *****)
structure Tree =
  struct

    datatype tree
      = NULL
      | ND of tree * tree * real * real * int * tree ref * tree ref
        (* ND(left, right, x, y, sz, rev, next) *)

    fun mkNode (l, r, x, y, sz) = ND(l, r, x, y, sz, ref NULL, ref NULL)

  end;

(***** build.sml *****)
structure BuildTree =
  struct

    local
      structure T = Tree

      val m_e   = 2.7182818284590452354
      val m_e2  = 7.3890560989306502274
      val m_e3  = 20.08553692318766774179
      val m_e6  = 403.42879349273512264299
      val m_e12 = 162754.79141900392083592475

    in

    datatype axis = X_AXIS | Y_AXIS

  (* builds a 2D tree of n nodes in specified range with dir as primary axis *)
    fun buildTree arg = let
          val rand = Rand.mkRandom 314
          fun drand48 () = Rand.norm (rand ())
          fun median (min, max, n) = let
                val t = drand48(); (* in [0.0..1.0) *)
                val retval = if (t > 0.5)
                      then Math.ln(1.0-(2.0*(m_e12-1.0)*(t-0.5)/m_e12))/12.0
                      else ~(Math.ln(1.0-(2.0*(m_e12-1.0)*t/m_e12))/12.0)
                in
                  min + ((retval + 1.0) * (max - min)/2.0)
                end
          fun uniform (min, max) = min + (drand48() * (max - min))
          fun build (0, _, _, _, _, _) = T.NULL
            | build (n, X_AXIS, min_x, min_y, max_x, max_y) = let
                val med = median(min_y, max_y, n)
                fun mkTree (min, max) = build(n div 2, Y_AXIS, min_x, max_x, min, max)
                in
                  T.mkNode(
                    mkTree(min_y, med), mkTree(med, max_y),
                    uniform(min_x, max_x), med, n)
                end
            | build (n, Y_AXIS, min_x, min_y, max_x, max_y) = let
                val med = median(min_x, max_x, n)
                fun mkTree (min, max) = build(n div 2, X_AXIS, min, max, min_y, max_y)
                in
                  T.mkNode(
                    mkTree(min_x, med), mkTree(med, max_x),
                    med, uniform(min_y, max_y), n)
                end
          in
            build arg
          end

    end (* local *)

  end; (* Build *)

(***** tsp.sml *****)
structure TSP =
  struct

    local
      structure T = Tree

      fun setPrev (T.ND(_, _, _, _, _, prev, _), x) = prev := x
      fun setNext (T.ND(_, _, _, _, _, _, next), x) = next := x
      fun link (a as T.ND(_, _, _, _, _, _, next), b as T.ND(_, _, _, _, _, prev, _)) = (
            next := b; prev := a)

      fun sameNd (T.ND(_, _, _, _, _, _, next), T.ND(_, _, _, _, _, _, next')) = (next = next')
        | sameNd (T.NULL, T.NULL) = true
        | sameNd _ = false

    (* Find Euclidean distance from a to b *)
      fun distance (T.ND(_, _, ax, ay, _, _, _), T.ND(_, _, bx, by, _, _, _)) =
            Math.sqrt(((ax-bx)*(ax-bx)+(ay-by)*(ay-by)))
        | distance _ = raise Fail "distance"

    (* sling tree nodes into a list -- requires root to be tail of list, and
     * only fills in next field, not prev.
     *)
      fun makeList T.NULL = T.NULL
        | makeList (t as T.ND(left, right, _, _, _, _, t_next)) = let
            val retVal = (case (makeList left, makeList right)
                   of (T.NULL, T.NULL) => t
                    | (l as T.ND _, T.NULL) => (setNext(left, t); l)
                    | (T.NULL, r as T.ND _) => (setNext(right, t); r)
                    | (l as T.ND _, r as T.ND _) => (
                        setNext(right, t); setNext(left, r); l)
                  (* end case *))
            in
              t_next := T.NULL;
              retVal
            end

    (* reverse orientation of list *)
      fun reverse T.NULL = ()
        | reverse (t as T.ND(_, _, _, _, _, prev, next)) = let
            fun rev (_, T.NULL) = ()
              | rev (back, tmp as T.ND(_, _, _, _, _, prev, next)) = let
                  val tmp' = !next
                  in
                    next := back;  setPrev(back, tmp);
                    rev (tmp, tmp')
                  end
            in
              setNext (!prev, T.NULL);
              prev := T.NULL;
              rev (t, !next)
            end

    (* Use closest-point heuristic from Cormen Leiserson and Rivest *)
      fun conquer (T.NULL) = T.NULL
        | conquer t = let
            val (cycle as T.ND(_, _, _, _, _, cycle_prev, cycle_next)) = makeList t
            fun loop (T.NULL) = ()
              | loop (t as T.ND(_, _, _, _, _, prev, doNext')) = let
                  val doNext = !doNext'
                  fun findMinDist (min, minDist, tmp as T.ND(_, _, _, _, _, _, next)) =
                        if (sameNd(cycle, tmp))
                          then min
                          else let
                            val test = distance(t, tmp)
                            in
                              if (test < minDist)
                                then findMinDist (tmp, test, !next)
                                else findMinDist (min, minDist, !next)
                            end
                  val (min as T.ND(_, _, _, _, _, min_prev', min_next')) =
                        findMinDist (cycle, distance(t, cycle), !cycle_next)
                  val min_prev = !min_prev'
                  val min_next = !min_next'
                  val minToNext = distance(min, min_next)
                  val minToPrev = distance(min, min_prev)
                  val tToNext = distance(t, min_next)
                  val tToPrev = distance(t, min_prev)
                  in
                    if ((tToPrev - minToPrev) < (tToNext - minToNext))
                      then ( (* insert between min and min_prev *)
                        link (min_prev, t);
                        link (t, min))
                      else (
                        link (min, t);
                        link (t, min_next));
                    loop doNext
                  end
            val t' = !cycle_next
            in
            (* Create initial cycle *)
              cycle_next := cycle;  cycle_prev := cycle;
              loop t';
              cycle
            end

    (* Merge two cycles as per Karp *)
      fun merge (a as T.ND(_, _, _, _, _, _, next), b, t) = let
            fun locateCycle (start as T.ND(_, _, _, _, _, _, next)) = let
                  fun findMin (min, minDist, tmp as T.ND(_, _, _, _, _, _, next)) =
                        if (sameNd(start, tmp))
                          then (min, minDist)
                          else let val test = distance(t, tmp)
                            in
                              if (test < minDist)
                                then findMin (tmp, test, !next)
                                else findMin (min, minDist, !next)
                            end
                  val (min as T.ND(_, _, _, _, _, prev', next'), minDist) =
                          findMin (start, distance(t, start), !next)
                  val prev' = !prev'
                  val next' = !next'
                  val minToNext = distance(min, next')
                  val minToPrev = distance(min, prev')
                  val tToNext = distance(t, next')
                  val tToPrev = distance(t, prev')
                  in
                    if ((tToPrev - minToPrev) < (tToNext - minToNext))
                    (* would insert between min and prev *)
                      then (prev', tToPrev, min, minDist)
                    (* would insert between min and next *)
                      else (min, minDist, next', tToNext)
                  end
          (* Compute location for first cycle *)
            val (p1, tToP1, n1, tToN1) = locateCycle a
          (* compute location for second cycle *)
            val (p2, tToP2, n2, tToN2) = locateCycle b
          (* Now we have 4 choices to complete:
           *   1:t,p1 t,p2 n1,n2
           *   2:t,p1 t,n2 n1,p2
           *   3:t,n1 t,p2 p1,n2
           *   4:t,n1 t,n2 p1,p2
           *)
            val n1ToN2 = distance(n1, n2)
            val n1ToP2 = distance(n1, p2)
            val p1ToN2 = distance(p1, n2)
            val p1ToP2 = distance(p1, p2)
            fun choose (testChoice, test, choice, minDist) =
                  if (test < minDist) then (testChoice, test) else (choice, minDist)
            val (choice, minDist) = (1, tToP1+tToP2+n1ToN2)
            val (choice, minDist) = choose(2, tToP1+tToN2+n1ToP2, choice, minDist)
            val (choice, minDist) = choose(3, tToN1+tToP2+p1ToN2, choice, minDist)
            val (choice, minDist) = choose(4, tToN1+tToN2+p1ToP2, choice, minDist)
            in
              case choice
               of 1 => (        (* 1:p1,t t,p2 n2,n1 -- reverse 2! *)
                    reverse n2;
                    link (p1, t);
                    link (t, p2);
                    link (n2, n1))
                | 2 => (        (* 2:p1,t t,n2 p2,n1 -- OK *)
                    link (p1, t);
                    link (t, n2);
                    link (p2, n1))
                | 3 => (        (* 3:p2,t t,n1 p1,n2 -- OK *)
                    link (p2, t);
                    link (t, n1);
                    link (p1, n2))
                | _ => (        (* 4:n1,t t,n2 p2,p1 -- reverse 1! *)
                    reverse n1;
                    link (n1, t);
                    link (t, n2);
                    link (p2, p1))
              (* end case *);
              t
            end (* merge *)

    in

  (* Compute TSP for the tree t -- use conquer for problems <= sz * *)
    fun tsp (t as T.ND(left, right, _, _, sz', _, _), sz) =
          if (sz' <= sz)
            then conquer t
            else merge (tsp(left, sz), tsp(right, sz), t)
      | tsp (T.NULL, _) = T.NULL

    end (* local *)

  end;

(***** main.sml *****)
structure Main =
  struct

    val divideSz = ref 150

    fun mkTree n = BuildTree.buildTree (n, BuildTree.X_AXIS, 0.0, 1.0, 0.0, 1.0)

    fun doit n = TSP.tsp (mkTree n, !divideSz)

  end;

(*
val result = Main.doit 32767
val result = Main.doit 511
*)
val result = Main.doit 255
