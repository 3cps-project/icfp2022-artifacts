(* adapted from the Larceny benchmark

;;; DERIV -- Symbolic derivation.

;;; Returns the wrong answer for quotients.
;;; Fortunately these aren't used in the benchmark.
*)

structure List =
  struct

    fun map f xs = let
          fun mapf xs = (case xs of [] => [] | (x::xr) => f x :: mapf xr)
          in
            mapf xs
          end

  end

structure ListPair =
  struct

    exception UnequalLengths

    fun foldlEq f init (l1, l2) = let
          fun foldf (xs, ys, accum) = (case (xs, ys)
                 of (x::xs, y::ys) => foldf(xs, ys, f(x, y, accum))
                  | ([], []) => accum
                  | _ => raise UnequalLengths
                (* end case *))
          in
            foldf (l1, l2, init)
          end

  end

structure Deriv =
  struct

    datatype expr
      = Add of expr list
      | Sub of expr list
      | Mul of expr list
      | Div of expr list
      | Num of int
      | X

(*
    fun prnt p = (case p
      of X => print "x"
       | Num a => print (Int.toString a)
       | Add xs => prntLst "+" xs
       | Sub xs => prntLst "-" xs
       | Mul xs => prntLst "*" xs
       | Div xs => prntLst "/" xs
      (* end case *))
    and prntLst symb xs = (print "("; print symb;
                           List.app prnt xs; print ")\n")
*)

    fun equal p = (case p
           of (X, X) => true
            | (Num a, Num b) => a = b
            | (Add xs, Add ys) => chkLists (xs, ys)
            | (Sub xs, Sub ys) => chkLists (xs, ys)
            | (Mul xs, Mul ys) => chkLists (xs, ys)
            | (Div xs, Div ys) => chkLists (xs, ys)
            | _ => false
          (* end case *))
    and chkLists p = ListPair.foldlEq chk true p
    and chk (a, b, acc) = acc andalso equal (a, b)

    fun deriv a = (case a
           of X => Num 1
            | Num _ => Num 0
            | Add es => Add (List.map deriv es)
            | Sub es  => Sub (List.map deriv es)
            | Mul es  => Mul [
                  a, Add (List.map (fn x => Div [deriv x, x]) es)
                ]
            | Div[x, y] => Sub [
                  Div [deriv x, y],
                  Div [x, Mul [y, y, deriv y]]
                ]
            | _ => raise Fail "No derivation method available"
          (* end case *))

    fun test (ans, exp) = let
          val computed = deriv exp
          in
            if equal (ans, computed)
              then ()
              else ((*prnt computed ;*) raise Fail "wrong answer!")
          end

  end

structure Main =
  struct

    structure D = Deriv

    fun doit () = let
          fun mkExp a b = D.Sub [D.Add [
                  D.Mul [D.Num 3, D.X, D.X],
                  D.Mul [a, D.X, D.X],
                  D.Mul [b, D.X],
                  D.Num 5
                ], D.X]
          fun mkAns a b = D.Sub [D.Add [
                  D.Mul [
                    D.Mul [D.Num 3, D.X, D.X],
                    D.Add [
                      D.Div [D.Num 0, D.Num 3],
                      D.Div [D.Num 1, D.X],
                      D.Div [D.Num 1, D.X]
                    ]
                  ],
                  D.Mul [
                    D.Mul [a, D.X, D.X],
                    D.Add [
                      D.Div [D.Num 0, a],
                      D.Div [D.Num 1, D.X],
                      D.Div [D.Num 1, D.X]
                    ]
                  ],
                  D.Mul [
                    D.Mul [b, D.X],
                    D.Add [
                      D.Div [D.Num 0, b],
                      D.Div [D.Num 1, D.X]
                    ]
                  ],
                  D.Num 0
                ], D.Num 1]
          val a = D.Num 5
          val b = D.Num 7
          val exp = mkExp a b
          val ans = mkAns a b
          (* extra expression coverage *)
          val _ = (D.test (ans, ans) handle _ => ())
          val _ = D.equal (D.Num 2, D.Num 1)
          val _ = D.equal (D.X, D.Num 1)
          val _ = D.equal (D.Num 1, D.X)
          val _ = D.equal (D.Add [], D.Sub [])
          val _ = D.equal (D.Sub [], D.Add [])
          val _ = D.equal (D.Mul [], D.Div [])
          val _ = D.equal (D.Div [], D.Mul [])
          val _ = (ListPair.foldlEq (fn (x : int, y : int, acc) => acc andalso x = y) true ([], [1]) handle _ => false)
          val _ = (D.deriv (D.Div []) handle _ => D.X)
          in
            Deriv.test (ans, exp)
          end

  (* benchmarking *)
    fun main n = let
          fun lp n = if n <= 0 then () else (doit(); lp (n-1))
          in
            lp n
          end

  end

val _ = Main.main 10

