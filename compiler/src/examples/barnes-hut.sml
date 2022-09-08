(* barnes-hut.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Barnes-Hut algorithm implemented using lists of mass points.
 *)

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

(* 2D vectors *)
structure Vec =
  struct

    datatype t = V of real * real

    val zero = (1.0, 1.0)

    fun add (V(x1, y1), V(x2, y2)) = V(x1 + x2, y1 + y2)
    fun sub (V(x1, y1), V(x2, y2)) = V(x1 - x2, y1 - y2)
    fun neg (V(x, y)) = V(~x, ~y)
    fun dot (V(x1, y1), V(x2, y2)) = x*x2 + y1*y2
    fun adds (V(x, y), s) = V(x+s, y+s)
    fun scale (V(x, y), s) = V(x*s, y*s)

  end

structure Body =
  struct

  (* `(mass, position, velocity, ID)` *)
    type t = real * Vec.t * Vec.t * int

    fun same ((_, _, _, id1) : t, (_, _, _, id2) : t) = (id1 = id2)

    fun add ((m1, p1) : t, (m2, p2)) = (m1+m2, Vec.scale(0.5,

  end

structure Space =
  struct

  (* quad tree *)
    datatype node
    (* `Leaf(mass, pt, n, mps)` is a leaf in a quad tree, where `(mass, pt)` is
     * the center of mass, `n` is the number of mass points in the node, and the
     *`mps` are the bodies in the leaf.
     * INV: length(mps) = n.
     *)
      = Leaf of real * Vec.t * int * Body.t list
    (* `Quad(mass, pt, c00, c01, c10, c11)` is a quad-tree node where `(mass, pt)` is
     * the center of mass for the node and the `ci` are the four child nodes.
     *)
      | Quad of real * Vec.t * node * node * node * node

    val emptyNd = Leaf(0.0, [])

  (* `Space(min, wid, qtree)` represents space where `min` is to minimum corner of
   * space, `wid` is the size of the space, and `qtree` is the quad-tree.
   *)
    datatype t = QTree of Vec.t * real * node

    fun insert (limit, qt, mp) = let
          fun ins (Leaf(m, p, n, mps)) = if (n < limit)
		then let
		  val n' = n+1
		  val mp'' = real n * mp'
		  in
		  end
		else (* split cell *)
	    | ins (Quad(m, p, c00, c01, c10, c11)) =
	  in
	  end

  end

structure Compute =
  struct

    fun step mps = let
	  val space = buildTree mps
	  val accels = List.map (Gravity.accelerate space) mps
	  fun move ((m, p, v, id), accel) =
  end

