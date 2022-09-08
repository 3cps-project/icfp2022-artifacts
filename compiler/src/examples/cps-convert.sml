(* cps-convert.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * The Danvy-Filinski CPS conversion from "Representing Control"
 *)

datatype order = LESS | EQUAL | GREATER

structure List =
  struct
    fun revAppend (xs, ys) = (case xs of [] => ys | x::xr => revAppend (xr, x::ys))
    fun rev xs = revAppend (xs, [])
  end

structure Prim =
  struct

    datatype t = ADD | SUB | MUL | DIV

  end

structure Var =
  struct

    datatype t = V of string * int

    datatype generator = Gen of int

    fun newGen () = Gen 0

    fun new (Gen n, s) = (V(s, n), Gen(n+1))

    fun nameOf (V(s, _)) = s

    fun same (V(s1, n1), V(s2, n2)) = (n1 = n2)

    fun compare (V(_, n1), V(_, n2)) =
          if (n1 < n2) then LESS
          else if (n1 > n2) then GREATER
          else EQUAL

  end

structure VMap =
  struct
  (* represent finite maps as sorted lists *)
    datatype 'a t = VMap of (Var.t * 'a) list

    val empty = VMap[]

    fun insert (VMap items, x, v) = let
          fun ins items = (case items
                 of [] => [(x, v)]
                  | (x', v')::r => (case Var.compare(x, x')
                       of LESS => (x, v) :: items
                        | EQUAL => (x, v) :: r
                        | GREATER => (x', v') :: ins r
                      (* end case *))
                (* end case *))
          in
            VMap(ins items)
          end

    fun find (VMap items, x) = let
          fun find' items = (case items
                 of [] => NONE
                  | (y, v)::r => (case Var.compare(x, y)
                       of LESS => NONE
                        | EQUAL => SOME v
                        | GREATER => find' r
                      (* end case *))
                (* end case *))
          in
            find' items
          end

  end

structure Lambda =
  struct

    datatype t
      = VAR of Var.t            (* variable *)
      | LAMBDA of Var.t * t     (* lambda abstraction *)
      | APP of t * t            (* application *)
      | PRIM of Prim.t * t list (* primitive operation *)
      | IF of t * t * t         (* conditional *)

  end

structure CVar =
  struct

    datatype t = V of string * int

    datatype generator = Gen of int

    fun newGen () = Gen 0

    fun new (Gen n, s) = (V(s, n), Gen(n+1))

  end

structure CPS =
  struct

    datatype t
      = UAPP of uval * uval * cval              (* function application *)
      | CAPP of cval * uval                     (* continuation application *)
      | PAPP of Prim.t * uval list * cval       (* primitive operation *)
      | IF of uval * t * t                      (* conditional *)
      | LETC of CVar.t * cval * t               (* continuation binding *)

    and uval
      = UVAR of Var.t                           (* user variable *)
      | ULAMBDA of Var.t * CVar.t * t           (* user lambda abstraction *)

    and cval
      = CVAR of CVar.t                          (* continuation variable *)
      | CLAMBDA of Var.t * t                    (* continuation abstraction *)
      | HALT

  end

structure Convert = struct

    structure L = Lambda
    structure C = CPS

    datatype env = Env of Var.t VMap.t

    val emptyEnv = Env VMap.empty

    datatype generator = Gen of Var.generator * CVar.generator

    fun newGen () = Gen(Var.newGen(), CVar.newGen())

    fun newUVar (Gen(vgen, cgen), name) = let
          val (k, vgen') = Var.new(vgen, name)
          in
            (k, Gen(vgen', cgen))
          end

    fun newCVar (Gen(vgen, cgen), name) = let
          val (k, cgen') = CVar.new(cgen, name)
          in
            (k, Gen(vgen, cgen'))
          end

    fun findVar (Env vmap, x) = (case VMap.find(vmap, x)
           of SOME x' => C.UVAR x'
            | NONE => raise Fail "unbound variable"
          (* end case *))

    fun bindVar (Env vmap, gen, x) = let
          val (x', gen') = newUVar(gen, Var.nameOf x)
          in
            (x', Env(VMap.insert(vmap, x, x')), gen')
          end

  (* conversion for expressions in tail position.  Note that we never pass a C.CLAMBDA
   * as the third argument, so it is safe to use it twice in the conversion of IF.
   *)
    fun tailExpToExp (env, gen, e, k : C.cval) = (case e
           of L.VAR x => (C.CAPP(k, findVar(env, x)), gen)
            | L.LAMBDA(x, body) => let
                val (x', env', gen) = bindVar (env, gen, x)
                val (k', gen) = newCVar(gen, "k")
                val (body', gen) = tailExpToExp (env', gen, body, C.CVAR k')
                val e' = C.CAPP(k, C.ULAMBDA(x', k', body'))
                in
                  (e', gen)
                end
            | L.APP(e1, e2) =>
                expToExp (env, gen, e1, fn (gen, f') =>
                  expToExp (env, gen, e2, fn (gen, arg') =>
                    (C.UAPP(f', arg', k), gen)))
            | L.PRIM(p, es) => expsToVals (env, gen, es, fn (gen, args) =>
                (C.PAPP(p, args, k), gen))
            | L.IF(e1, e2, e3) =>
                expToExp (env, gen, e1, fn (gen, b') => let
                  val (e2', gen) = tailExpToExp (env, gen, e2, k)
                  val (e3', gen) = tailExpToExp (env, gen, e3, k)
                  in
                    (C.IF(b', e2', e3'), gen)
                  end)
          (* end case *))

    and expToExp (env, gen, e, k : (generator * C.uval) -> C.t * generator) = (case e
           of L.VAR x => k (gen, findVar (env, x))
            | L.LAMBDA(x, body) => let
                val (x', env', gen) = bindVar(env, gen, x)
                val (k', gen) = newCVar (gen, "k")
                val (body', gen) = tailExpToExp(env', gen, body, C.CVAR k')
                in
                  k (gen, C.ULAMBDA(x', k', body'))
                end
            | L.APP(e1, e2) => let
                val (res', gen) = newUVar (gen, "res")
                in
                  expToExp (env, gen, e1, fn (gen, f') =>
                    expToExp (env, gen, e2, fn (gen, arg') => let
                      val (ct, gen) = k(gen, C.UVAR res')
                      in
                        (C.UAPP(f', arg', C.CLAMBDA(res', ct)), gen)
                      end))
                end
            | L.PRIM(p, es) => expsToVals (env, gen, es, fn (gen, args) => let
                val (res', gen) = newUVar (gen, "res")
                val (ct, gen) = k(gen, C.UVAR res')
                in
                  (C.PAPP(p, args, C.CLAMBDA(res', ct)), gen)
                end)
            | L.IF(e1, e2, e3) => let
                val (k', gen) = newCVar (gen, "join")
                val (a', gen) = newUVar (gen, "a")
                val (ct, gen) = k (gen, C.UVAR a')
                val (e', gen) = expToExp (env, gen, e1, fn (gen, b') => let
                      val (e2', gen) = tailExpToExp (env, gen, e2, C.CVAR k')
                      val (e3', gen) = tailExpToExp (env, gen, e3, C.CVAR k')
                      in
                        (C.IF(b', e2', e3'), gen)
                      end)
                in
                  (C.LETC(k', C.CLAMBDA(a', ct), e'), gen)
                end
          (* end case *))

    and expsToVals (env, gen, es, k) = let
          fun expsToVals (gen, [], uvs) = k (gen, List.rev uvs)
            | expsToVals (gen, e::es, uvs) =
                expToExp (env, gen, e, fn (gen, uv) => expsToVals (gen, es, uv::uvs))
          in
            expsToVals (gen, es, [])
          end

    fun transform e = tailExpToExp (emptyEnv, newGen(), e, C.HALT)

  end

structure Main =
  struct

    structure L = Lambda

    val x1 = Var.V("a", 1)
    val x2 = Var.V("b", 2)
    val x3 = Var.V("c", 3)
    val x4 = Var.V("d", 4)
    val x5 = Var.V("e", 5)
    val x6 = Var.V("f", 6)

    val e1 = L.LAMBDA (x3,
          L.IF (L.APP (L.LAMBDA(x1, L.LAMBDA(x2, L.PRIM(Prim.ADD, [L.IF (L.VAR x1, L.VAR x1, L.VAR x2), 
                                                                   L.PRIM(Prim.ADD, [L.VAR x1, 
                                                                                     L.VAR x2])]))),
                       L.LAMBDA(x4, L.VAR x4)),
                L.APP (L.LAMBDA(x5, L.VAR x5),
                       L.LAMBDA(x6, L.VAR x3)),
                L.PRIM (Prim.DIV, [L.VAR x3, L.VAR x3])))

    (* extra expression coverage *)
    val vmap1 = VMap.VMap [(Var.V ("a", 1), Var.V ("a", 1)), (Var.V ("b", 2), Var.V ("b", 2)), (Var.V ("c", 3), Var.V ("c", 3))]
    val env1 = Convert.Env (vmap1)
    val _ = Convert.findVar (env1, Var.V ("a", 1))
    val _ = Convert.findVar (env1, Var.V ("b", 2))
    val _ = Convert.findVar (env1, Var.V ("c", 3))
    val _ = VMap.insert (vmap1, Var.V ("z", 0), Var.V ("z", 0))
    val _ = VMap.insert (vmap1, Var.V ("a", 1), Var.V ("a", 1))
    val _ = VMap.insert (vmap1, Var.V ("b", 2), Var.V ("b", 2))
    val _ = VMap.insert (vmap1, Var.V ("c", 3), Var.V ("c", 3))

    val result = Convert.transform e1

  end
