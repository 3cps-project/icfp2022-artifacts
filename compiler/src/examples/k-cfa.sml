(* k-CFA.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * A simple implementation of k-CFA ported from a Scheme/Racket
 * implementation by Matthew Might (http://matt.might.net).
 * The main difference is that we use finite sets and maps
 * from the SML/NJ Library instead of lists to represent
 * some of the domains.
 *
 * The following description is from Might's source code:
 *
 * ========================================
 *
 * k-CFA is a well-known hierarchy of increasingly precise
 * control-flow analyses that approximate the solution to the
 * control-flow problem.
 *
 * This program is a simple implementation of an
 * abstract-interpretion-based k-CFA for continuation-
 * passing-style lambda calculus (CPS).
 *
 * Contrary to what one might expect, it does not use
 * constraint-solving.  Rather, k-CFA is implemented
 * as a small-step abstract interpreter.  In fact, it looks
 * suspiciously like an ordinary (if non-deterministic)
 * Scheme interpreter.
 *
 * The analysis consists of exploring the reachable
 * parts of a graph of abstract machine states.
 *
 * Once constructed, a composite store mapping addresses
 * to values is synthesized.
 *
 * After that, the composite store is further summarized to
 * produce a mapping from variables to simple lambda terms.
 *
 *
 * The language over which the abstract interpreter operates is the
 * continuation-passing style lambda calculus (CPS):
 *
 * exp  ::= (ref    <label> <var>)
 *       |  (lambda <label> (<var1> ... <varN>) <call>)
 * call ::= (call   <label> <exp0> <exp1> ... <expN>)
 *
 * label = integer
 *
 * CPS is a popular intermediate form for functional compilation.
 * Its simplicity also means that it takes less code to construct
 * the abstract interpreter.
 *
 * ========================================
 *)

(* SML Basis *)

datatype order = LESS | EQUAL | GREATER

structure Int =
  struct

    fun compare (s1 : int, s2) =
	  if (s1 < s2) then LESS
	  else if (s2 < s1) then GREATER
	  else EQUAL

  end

structure String =
  struct

    fun compare (s1 : string, s2) =
	  if (s1 < s2) then LESS
	  else if (s2 < s1) then GREATER
	  else EQUAL

  end

structure List =
  struct

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

    fun foldl f init xs = let
          fun foldf ([], acc) = acc
            | foldf (x::xr, acc) = foldf (xr, f(x, acc))
          in
            foldf (xs, init)
          end

    fun exists f xs = let
          fun existsf xs = (case xs
                 of [] => false
                  | (x::xr) => f x orelse existsf xr
                (* end case *))
          in
            existsf xs
          end

    fun collate cmp ([], []) = EQUAL
      | collate cmp ([], _) = LESS
      | collate cmp (_, []) = GREATER
      | collate cmp (x::xs, y::ys) = (case cmp (x, y)
	   of EQUAL => collate cmp (xs, ys)
	    | order => order
	  (* end case *))

  end

val op @ = List.append

structure ListPair =
  struct

    fun foldl f init (l1, l2) = let
          fun foldf (xs, ys, accum) = (case (xs, ys)
                 of (x::xs, y::ys) => foldf(xs, ys, f(x, y, accum))
                  | _ => accum
                (* end case *))
          in
            foldf (l1, l2, init)
          end

    fun allEq _ ([], []) = true
      | allEq pred (x::xs, y::ys) = pred(x, y) andalso allEq pred (xs, ys)
      | allEq _ _ = false

  end

(* Syntax *)

structure Label =
  struct
    type t = int

    val compare = Int.compare
    fun same (l1 : t, l2 : t) = (l1 = l2)
  end

structure Var =
  struct
    type t = string

    val compare = String.compare

  (* an abbreviated version of the RedBlackMapFn functor from the SML/NJ Library *)
    structure Map =
      struct

	datatype color = R | B

	datatype 'a tree
	  = E
	  | T of (color * 'a tree * t * 'a * 'a tree)

	datatype 'a map = MAP of (int * 'a tree)

        fun empty () = MAP(0, E)

	fun insert (MAP(nItems, m), xk, x) = let
	      val nItems' = ref nItems
	      fun ins E = (nItems' := nItems+1; T(R, E, xk, x, E))
		| ins (s as T(color, a, yk, y, b)) = (case compare(xk, yk)
		     of LESS => (case a
			   of T(R, c, zk, z, d) => (case compare(xk, zk)
				 of LESS => (case ins c
				       of T(R, e, wk, w, f) =>
					    T(R, T(B,e,wk, w,f), zk, z, T(B,d,yk,y,b))
					| c => T(B, T(R,c,zk,z,d), yk, y, b)
				      (* end case *))
				  | EQUAL => T(color, T(R, c, xk, x, d), yk, y, b)
				  | GREATER => (case ins d
				       of T(R, e, wk, w, f) =>
					    T(R, T(B,c,zk,z,e), wk, w, T(B,f,yk,y,b))
					| d => T(B, T(R,c,zk,z,d), yk, y, b)
				      (* end case *))
				(* end case *))
			    | _ => T(B, ins a, yk, y, b)
			  (* end case *))
		      | EQUAL => T(color, a, xk, x, b)
		      | GREATER => (case b
			   of T(R, c, zk, z, d) => (case compare(xk, zk)
				 of LESS => (case ins c
				       of T(R, e, wk, w, f) =>
					    T(R, T(B,a,yk,y,e), wk, w, T(B,f,zk,z,d))
					| c => T(B, a, yk, y, T(R,c,zk,z,d))
				      (* end case *))
				  | EQUAL => T(color, a, yk, y, T(R, c, xk, x, d))
				  | GREATER => (case ins d
				       of T(R, e, wk, w, f) =>
					    T(R, T(B,a,yk,y,c), zk, z, T(B,e,wk,w,f))
					| d => T(B, a, yk, y, T(R,c,zk,z,d))
				      (* end case *))
				(* end case *))
			    | _ => T(B, a, yk, y, ins b)
			  (* end case *))
		    (* end case *))
	      val T(_, a, yk, y, b) = ins m
	      in
		MAP(!nItems', T(B, a, yk, y, b))
	      end

	fun find (MAP(_, t), k) = let
	      fun find' E = NONE
		| find' (T(_, a, yk, y, b)) = (case compare(k, yk)
		     of LESS => find' a
		      | EQUAL => SOME y
		      | GREATER => find' b
		    (* end case *))
	      in
		find' t
	      end

	fun next ((t as T(_, _, _, _, b))::rest) = (t, left(b, rest))
	  | next _ = (E, [])
	and left (E, rest) = rest
	  | left (t as T(_, a, _, _, _), rest) = left(a, t::rest)
	fun start m = left(m, [])

	fun collate cmpRng = let
	      fun cmp (t1, t2) = (case (next t1, next t2)
		     of ((E, _), (E, _)) => EQUAL
		      | ((E, _), _) => LESS
		      | (_, (E, _)) => GREATER
		      | ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
			  case compare(xk, yk)
			   of EQUAL => (case cmpRng(x, y)
				 of EQUAL => cmp (r1, r2)
				  | order => order
				(* end case *))
			    | order => order
			  (* end case *))
		    (* end case *))
	      in
		fn (MAP(_, m1), MAP(_, m2)) => cmp (start m1, start m2)
	      end

      end (* Map *)

  end

structure Syntax =
  struct

    type label = Label.t

    type var = Var.t

    datatype exp
      = VAR of label * var
      | LAMBDA of label * var list * call (* lambda *)

    and call
      = CALL of label * exp * exp list
      | RET of label * var

(*
    withtype lambda = label * var list * call
*)
    type lambda = label * var list * call

    fun compareLambda ((lab1, _, _):lambda, (lab2, _, _):lambda) =
	  Label.compare(lab1, lab2)

    fun compareExp (VAR(_, x), VAR(_, y)) = String.compare(x, y)
      | compareExp (VAR _, _) = LESS
      | compareExp (_, VAR _) = GREATER
      | compareExp (LAMBDA lam1, LAMBDA lam2) = compareLambda(lam1, lam2)

    fun sameCall (CALL(l1, _, _), CALL(l2, _, _)) = (l1 = l2)
      | sameCall (RET(l1, _), RET(l2, _)) = (l1 = l2)
      | sameCall _ = false

  end

(* time = lab^k
;; In k-CFA, time is a bounded memory of program history.
;; In particular, it is the last k call sites through which
;; the program has traversed.
*)
structure Time =
  struct

    type t = Syntax.label list

    val compare = List.collate Label.compare
    val same = ListPair.allEq Label.same

    val zero = []

  end

structure Bind =
  struct

  (* A binding is minted each time a variable gets bound to a value. *)
    datatype t = Bnd of Var.t * Time.t

    fun compare (Bnd(x, t1), Bnd(y, t2)) = (case Var.compare(x, y)
	   of EQUAL => Time.compare(t1, t2)
	    | order => order
	  (* end case *))

  end (* Addr *)

(* Addresses can point to values in the store.
 * In pure CPS, the only kind of addresses are bindings.
 *)
structure Addr =
  struct

    type t = Bind.t

    val new = Bind.Bnd

    val compare = Bind.compare

  end (* Addr *)

structure BEnv =
  struct

    local
      structure Map = Var.Map
    in
    type t = Addr.t Map.map
    val empty : t = Map.empty()
    val compare = Map.collate Addr.compare
    fun lookup (benv, x) = (case Map.find(benv, x)
	   of SOME adr => adr
	    | NONE => raise Fail "lookup"
	  (* end case *))
    val extend = Map.insert
    fun extend' (benv, xs, adrs) = ListPair.foldl
	  (fn (x, adr, benv) => Map.insert(benv, x, adr))
	    benv (xs, adrs)
    end (* local *)

  end (* BEnv *)

(* Closures pair a lambda term with a binding environment that
 * determinse the value of its free variables.
 *)
structure Closure =
  struct
    datatype t = Clos of Syntax.lambda * BEnv.t

    fun lambdaOf (Clos(lam, _)) = Syntax.LAMBDA lam
    fun benvOf (Clos(_, benv)) = benv

    fun compare (Clos(lam1, benv1), Clos(lam2, benv2)) = (
	  case Syntax.compareLambda (lam1, lam2)
	   of EQUAL => BEnv.compare (benv1, benv2)
	    | order => order
	  (* end case *))

  end (* Closure *)

(* For pure CPS, closures are the only kind of value. *)
structure Value =
  struct

    type t = Closure.t

    val compare = Closure.compare

  end (* Value *)

(* An abstract denotable value is a set of possible values. *)
structure D =
  struct
    local
    (* an abbreviated version of the RedBlackSetFn functor from the SML/NJ Library *)
      structure Set =
	struct

	  type item = Value.t

	  datatype color = R | B

	  datatype tree
	    = E
	    | T of (color * tree * item * tree)

	  datatype set = SET of (int * tree)

	  fun singleton x = SET(1, T(B, E, x, E))

	(* functions for walking the tree while keeping a stack of parents
	 * to be visited.
	 *)
	  fun next ((t as T(_, _, _, b))::rest) = (t, left(b, rest))
	    | next _ = (E, [])
	  and left (E, rest) = rest
	    | left (t as T(_, a, _, _), rest) = left(a, t::rest)
	  fun start m = left(m, [])

	(* Return the lexical order of two sets *)
	  fun compare (SET(_, s1), SET(_, s2)) = let
		fun cmp (t1, t2) = (case (next t1, next t2)
		       of ((E, _), (E, _)) => EQUAL
			| ((E, _), _) => LESS
			| (_, (E, _)) => GREATER
			| ((T(_, _, x, _), r1), (T(_, _, y, _), r2)) => (
			    case Value.compare(x, y)
			     of EQUAL => cmp (r1, r2)
			      | order => order
			    (* end case *))
		      (* end case *))
		in
		  cmp (start s1, start s2)
		end

	(* support for constructing red-black trees in linear time from increasing
	 * ordered sequences (based on a description by R. Hinze).  Note that the
	 * elements in the digits are ordered with the largest on the left, whereas
	 * the elements of the trees are ordered with the largest on the right.
	 *)
	  datatype digit
	    = ZERO
	    | ONE of (item * tree * digit)
	    | TWO of (item * tree * item * tree * digit)
	(* add an item that is guaranteed to be larger than any in l *)
	  fun addItem (a, l) = let
		fun incr (a, t, ZERO) = ONE(a, t, ZERO)
		  | incr (a1, t1, ONE(a2, t2, r)) = TWO(a1, t1, a2, t2, r)
		  | incr (a1, t1, TWO(a2, t2, a3, t3, r)) =
		      ONE(a1, t1, incr(a2, T(B, t3, a3, t2), r))
		in
		  incr(a, E, l)
		end
	(* link the digits into a tree *)
	  fun linkAll t = let
		fun link (t, ZERO) = t
		  | link (t1, ONE(a, t2, r)) = link(T(B, t2, a, t1), r)
		  | link (t, TWO(a1, t1, a2, t2, r)) =
		      link(T(B, T(R, t2, a2, t1), a1, t), r)
		in
		  link (E, t)
		end

	(* return the union of the two sets *)
	  fun union (SET(_, s1), SET(_, s2)) = let
		fun ins ((E, _), n, result) = (n, result)
		  | ins ((T(_, _, x, _), r), n, result) =
		      ins(next r, n+1, addItem(x, result))
		fun union' (t1, t2, n, result) = (case (next t1, next t2)
		       of ((E, _), (E, _)) => (n, result)
			| ((E, _), t2) => ins(t2, n, result)
			| (t1, (E, _)) => ins(t1, n, result)
			| ((T(_, _, x, _), r1), (T(_, _, y, _), r2)) => (
			    case Value.compare(x, y)
			     of LESS => union' (r1, t2, n+1, addItem(x, result))
			      | EQUAL => union' (r1, r2, n+1, addItem(x, result))
			      | GREATER => union' (t1, r2, n+1, addItem(y, result))
			    (* end case *))
		      (* end case *))
		val (n, result) = union' (start s1, start s2, 0, ZERO)
		in
		  SET(n, linkAll result)
		end

	  fun foldl f = let
		fun foldf (E, accum) = accum
		  | foldf (T(_, a, x, b), accum) =
		      foldf(b, f(x, foldf(a, accum)))
		in
		  fn init => fn (SET(_, m)) => foldf(m, init)
		end
	end (* Set *)
    in
      type t = Set.set
      val make = Set.singleton
      val join = Set.union
      val compare = Set.compare
      val fold = Set.foldl
    end (* local *)
  end

(* A store (or a heap/memory) maps addresses to denotable values. *)
structure Store =
  struct
    local
    (* an abbreviated version of the RedBlackMapFn functor from the SML/NJ Library *)
      structure Map =
	struct

	  type key = Addr.t
	  val compare = Addr.compare

	  datatype color = R | B

	  datatype 'a tree
	    = E
	    | T of (color * 'a tree * Addr.t * 'a * 'a tree)

	  datatype 'a map = MAP of (int * 'a tree)

	  fun empty () = MAP(0, E)

	  fun insertWith comb (MAP(nItems, m), xk, x) = let
		val nItems' = ref nItems
		fun ins E = (nItems' := nItems+1; T(R, E, xk, x, E))
		  | ins (s as T(color, a, yk, y, b)) = (case compare(xk, yk)
		       of LESS => (case a
			     of T(R, c, zk, z, d) => (case compare(xk, zk)
				   of LESS => (case ins c
					 of T(R, e, wk, w, f) =>
					      T(R, T(B,e,wk, w,f), zk, z, T(B,d,yk,y,b))
					  | c => T(B, T(R,c,zk,z,d), yk, y, b)
					(* end case *))
				    | EQUAL =>
					T(color, T(R, c, xk, comb(z, x), d), yk, y, b)
				    | GREATER => (case ins d
					 of T(R, e, wk, w, f) =>
					      T(R, T(B,c,zk,z,e), wk, w, T(B,f,yk,y,b))
					  | d => T(B, T(R,c,zk,z,d), yk, y, b)
					(* end case *))
				  (* end case *))
			      | _ => T(B, ins a, yk, y, b)
			    (* end case *))
			| EQUAL => T(color, a, xk, comb(y, x), b)
			| GREATER => (case b
			     of T(R, c, zk, z, d) => (case compare(xk, zk)
				   of LESS => (case ins c
					 of T(R, e, wk, w, f) =>
					      T(R, T(B,a,yk,y,e), wk, w, T(B,f,zk,z,d))
					  | c => T(B, a, yk, y, T(R,c,zk,z,d))
					(* end case *))
				    | EQUAL =>
				        T(color, a, yk, y, T(R, c, xk, comb(z, x), d))
				    | GREATER => (case ins d
					 of T(R, e, wk, w, f) =>
					      T(R, T(B,a,yk,y,c), zk, z, T(B,e,wk,w,f))
					  | d => T(B, a, yk, y, T(R,c,zk,z,d))
					(* end case *))
				  (* end case *))
			      | _ => T(B, a, yk, y, ins b)
			    (* end case *))
		      (* end case *))
		val T(_, a, yk, y, b) = ins m
		in
		  MAP(!nItems', T(B, a, yk, y, b))
		end

	  fun find (MAP(_, t), k) = let
		fun find' E = NONE
		  | find' (T(_, a, yk, y, b)) = (case compare(k, yk)
		       of LESS => find' a
			| EQUAL => SOME y
			| GREATER => find' b
		      (* end case *))
		in
		  find' t
		end

	  fun foldli f = let
		fun foldf (E, accum) = accum
		  | foldf (T(_, a, xk, x, b), accum) =
		      foldf(b, f(xk, x, foldf(a, accum)))
		in
		  fn init => fn (MAP(_, m)) => foldf(m, init)
		end

	  fun next ((t as T(_, _, _, _, b))::rest) = (t, left(b, rest))
	    | next _ = (E, [])
	  and left (E, rest) = rest
	    | left (t as T(_, a, _, _, _), rest) = left(a, t::rest)
	  fun start m = left(m, [])

	  fun collate cmpRng = let
		fun cmp (t1, t2) = (case (next t1, next t2)
		       of ((E, _), (E, _)) => EQUAL
			| ((E, _), _) => LESS
			| (_, (E, _)) => GREATER
			| ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
			    case compare(xk, yk)
			     of EQUAL => (case cmpRng(x, y)
				   of EQUAL => cmp (r1, r2)
				    | order => order
				  (* end case *))
			      | order => order
			    (* end case *))
		      (* end case *))
		in
		  fn (MAP(_, m1), MAP(_, m2)) => cmp (start m1, start m2)
		end

	  local
	  (* support for constructing red-black trees in linear time from increasing
	   * ordered sequences (based on a description by R. Hinze).  Note that the
	   * elements in the digits are ordered with the largest on the left, whereas
	   * the elements of the trees are ordered with the largest on the right.
	   *)
	    datatype 'a digit
	      = ZERO
	      | ONE of (key * 'a * 'a tree * 'a digit)
	      | TWO of (key * 'a * 'a tree * key * 'a * 'a tree * 'a digit)
	  (* add an item that is guaranteed to be larger than any in l *)
	    fun addItem (ak, a, l) = let
		  fun incr (ak, a, t, ZERO) = ONE(ak, a, t, ZERO)
		    | incr (ak1, a1, t1, ONE(ak2, a2, t2, r)) =
			TWO(ak1, a1, t1, ak2, a2, t2, r)
		    | incr (ak1, a1, t1, TWO(ak2, a2, t2, ak3, a3, t3, r)) =
			ONE(ak1, a1, t1, incr(ak2, a2, T(B, t3, ak3, a3, t2), r))
		  in
		    incr(ak, a, E, l)
		  end
	  (* link the digits into a tree *)
	    fun linkAll t = let
		  fun link (t, ZERO) = t
		    | link (t1, ONE(ak, a, t2, r)) = link(T(B, t2, ak, a, t1), r)
		    | link (t, TWO(ak1, a1, t1, ak2, a2, t2, r)) =
			link(T(B, T(R, t2, ak2, a2, t1), ak1, a1, t), r)
		  in
		    link (E, t)
		  end
	    fun wrap f (MAP(_, m1), MAP(_, m2)) = let
		  val (n, result) = f (start m1, start m2, 0, ZERO)
		  in
		    MAP(n, linkAll result)
		  end
	    fun ins ((E, _), n, result) = (n, result)
	      | ins ((T(_, _, xk, x, _), r), n, result) =
		  ins(next r, n+1, addItem(xk, x, result))
	  in
	(* return a map whose domain is the union of the domains of the two input
	 * maps, using the supplied function to define the map on elements that
	 * are in both domains.
	 *)
	  fun unionWith mergeFn = let
		fun union (t1, t2, n, result) = (case (next t1, next t2)
		       of ((E, _), (E, _)) => (n, result)
			| ((E, _), t2) => ins(t2, n, result)
			| (t1, (E, _)) => ins(t1, n, result)
			| ((T(_, _, xk, x, _), r1), (T(_, _, yk, y, _), r2)) => (
			    case compare(xk, yk)
			     of LESS => union (r1, t2, n+1, addItem(xk, x, result))
			      | EQUAL =>
				  union (r1, r2, n+1, addItem(xk, mergeFn(x, y), result))
			      | GREATER => union (t1, r2, n+1, addItem(yk, y, result))
			    (* end case *))
		      (* end case *))
		in
		  wrap union
		end
	  end (* local *)
	end (* Map *)
    in
    type t = D.t Map.map
    val empty : t = Map.empty()
    val compare = Map.collate D.compare
    fun lookup (st, adr) = (case Map.find(st, adr)
	   of SOME dv => dv
	    | NONE => raise Fail "store lookup"
	  (* end case *))
    val update = Map.insertWith D.join
    fun update' (st, adrs, dvs) = ListPair.foldl
	  (fn (adr, dv, st) => update(st, adr, dv))
	    st (adrs, dvs)
    val join = Map.unionWith D.join
    val foldi = Map.foldli
    end (* local *)
  end (* Store *)

(* Abstract state space *)
structure StateSpace =
  struct
    datatype t = State of Syntax.call * BEnv.t * Store.t * Time.t

    fun storeOf (State(_, _, st, _)) = st

    fun same (State(call1, bev1, st1, t1), State(call2, bev2, st2, t2)) =
	  Time.same(t1, t2) andalso Syntax.sameCall(call1, call2)
	  andalso (BEnv.compare(bev1, bev2) = EQUAL)
	  andalso (Store.compare(st1, st2) = EQUAL)

    fun initState call = State(call, BEnv.empty, Store.empty, Time.zero)

  end (* StateSpace *)

(* k-CFA parameters
 * Change these to alter the behavior of the analysis.
 *)
structure Params =
  struct

    val k = 1

    fun tick (Syntax.CALL(lab, _, _), t) = [lab] (* == List.take (lab :: t, k) *)

    fun alloc t x = Addr.new(x, t)

  end

(* k-CFA abstract interpreter *)
structure AbsInterp =
  struct

    fun atomEval (benv : BEnv.t, store : Store.t) = let
	  fun eval (Syntax.VAR(_, x)) = Store.lookup (store, BEnv.lookup(benv, x))
	    | eval (Syntax.LAMBDA lam) = D.make(Closure.Clos(lam, benv))
	  in
	    eval
	  end

    fun next (StateSpace.State(call as Syntax.CALL(lab, f, args), benv, store, time)) = let
	  val time' = Params.tick (call, time)
	  val procs = atomEval (benv, store) f
	  val params = List.map (atomEval (benv, store)) args
	  fun apply (Closure.Clos(lam, benv'), states) = let
		val (_, formals, call') = lam
		val bindings = List.map (Params.alloc time') formals
		val benv'' = BEnv.extend' (benv', formals, bindings)
		val store' = Store.update' (store, bindings, params)
		in
		  StateSpace.State(call', benv'', store', time') :: states
		end
	  in
	    D.fold apply [] procs
	  end
      | next _ = []

  end (* AbsInterp *)

(* State-space exploration. *)
structure Analysis =
  struct

    local
      fun member (sts, st) = List.exists (fn st' => StateSpace.same(st, st')) sts

    (* insert into sorted list of expressions *)
      fun insertExp (exp, []) = [exp]
	| insertExp (exp, e::exps) = (case Syntax.compareExp (exp, e)
	     of LESS => e :: insertExp (exp, exps)
	      | GREATER => exp :: e :: exps
	      | EQUAL => e :: exps
	    (* end case *))
    (* monomorphic store utilities *)
      type mono_store = (Var.t * Syntax.exp list) list
      fun monoBinding (Bind.Bnd(x, _)) = x
      fun monoValue (Closure.Clos(lam, _)) = Syntax.LAMBDA lam
      fun monoValues d = D.fold (fn (v, exps) => monoValue v :: exps) [] d
      fun monoStoreUpdate ([], x, exp) : mono_store = [(x, [exp])]
	| monoStoreUpdate ((y, exps)::r, x, exp) = (case Var.compare(x, y)
	     of LESS => (y, exps) :: monoStoreUpdate (r, x, exp)
	      | GREATER => (x, [exp]) :: (y, exps) :: r
	      | EQUAL => (y, insertExp(exp, exps)) :: r
	    (* end case *))
      fun monoStoreUpdate' (mst, x, exps) : mono_store =
	    List.foldl (fn (exp, mst) => monoStoreUpdate (mst, x, exp)) mst exps
    in

    fun explore (seen, []) = seen
      | explore (seen, todo as st::sts) =
	  if member (seen, st)
	    then explore (seen, sts)
	    else explore (st :: seen, AbsInterp.next st @ sts)

    fun summarize states = List.foldl
	  (fn (state, sum) => Store.join(StateSpace.storeOf state, sum))
	    Store.empty states

  (* : Store.t -> (Var.t * Syntax.exp list) list *)
    fun monovariantStore st = Store.foldi
	  (fn (Bind.Bnd(x, _), d, mst) => monoStoreUpdate'(mst, x, monoValues d))
	    [] st
    end
  end (* Analysis *)

structure Main =
  struct

    (* The Standard Example
     *
     * In direct-style:
     *
     * (let* ((id (lambda (x) x))
     *        (a  (id (lambda (z) (halt z))))
     *        (b  (id (lambda (y) (halt y)))))
     *   (halt b))
     *)
    local
      val labelCount = ref 1
      fun newLabel () = let val n = !labelCount + 1 in labelCount := n; n end
      fun var x = Syntax.VAR(newLabel(), x)
      fun lambda formals call = Syntax.LAMBDA(newLabel(), formals, call)
      fun call f args = Syntax.CALL(newLabel(), f, args)
      fun return x = Syntax.RET(newLabel(), x)
      fun mkLet x e1 e2 = call (lambda [x] e2) [e1]
    in
    val stdExample =
	  mkLet "id" (lambda ["x", "k"] (call (var "k") [var "x"]))
	    (call (var "id") [
		(lambda ["z"] (return "z")),
		(lambda ["a"]
		  (call (var "id") [
		      (lambda ["y"] (return "y")),
		      (lambda ["b"] (return "b"))
		    ]))
	      ])
    end (* local *)

    fun doit () = let
	  val states = Analysis.explore ([], [StateSpace.initState stdExample])
	  val summary = Analysis.summarize states
	  val monoSummary = Analysis.monovariantStore summary
	  in
	    monoSummary
	  end

  end (* Main *)

val result = Main.doit ()

(* Expected answer:
 *
((x ((lambda 11 (y) (ref 10 y))
     (lambda 8 (z) (ref 7 z))))
 (k ((lambda 15 (a) (call 14 (ref 9 id)
                          (lambda 11 (y) (ref 10 y))
                          (lambda 13 (b) (ref 12 b))))
     (lambda 13 (b) (ref 12 b))))
 (id ((lambda 5 (x k) (call 4 (ref 2 k) (ref 3 x)))))
 (b ((lambda 11 (y) (ref 10 y))))
 (a ((lambda 8 (z) (ref 7 z)))))
*)
