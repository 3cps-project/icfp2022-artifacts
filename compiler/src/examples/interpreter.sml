
(* An interpreter for a simple language *)
(* TODO: when we handle exceptions better, remove the lazy 
   failure handling from this and replace them with exceptions *)

fun length xs = let
    fun lp (xs, n) = (case xs of [] => n | (_::r) => lp(r, n+1))
in
    lp (xs, 0)
end

fun foldr2 f base lst1 lst2 =
    case (lst1, lst2)
     of ([], []) => base
      (* TODO: lazy failing *)
      | ([], _) => base
      (* TODO: lazy failing *)
      | (_, []) => base
      | (a :: rst1, b :: rst2) => f(a, b, foldr2 f base rst1 rst2)

fun foldl f base lst =
    case lst
     of [] => base
      | a :: rst => foldl f (f (a, base)) rst

fun rev_append (xs, ys) = (case xs of [] => ys | x::xr => rev_append (xr, x::ys))

fun rev xs = rev_append (xs, [])

type var = int
datatype prim = Plus | Times | Assign | Ref | Deref

datatype exp = Int of int
             | Var of var
             | Fun of int list * exp
             | Call of exp * (exp list)
             | IfZero of exp * exp * exp
             | Letrec of (int * (int list * exp)) list * exp
             | Prim of prim

type address = int
type env = (var * address) list
datatype value = VInt of int
               | VClo of (int list * exp) * env
               | VPrim of prim
               | VCell of address
type store = (address * value) list

val empty = []
fun extend (map, a, b) = (a, b)::map
(* TODO: lazy failing *)
fun find_env (map : env, a : var, b) =
    (case map of
         [] => b
       | (a',b')::rst =>
         if a = a' then b' else find_env (rst, a,  b))
(* TODO: lazy failing *)
fun find_store (map : store, a : address, b) =
    (case map of
         [] => b
       | (a',b')::rst =>
         if a = a' then b' else find_store (rst, a,  b))

fun interpret e0 =
    let val dummy_address = 0
        val dummy_value = VInt 0
        val initial_env = []
        val initial_store = [(dummy_address, dummy_value)]
        val initial_address = dummy_address + 1
        fun lookup_env (env, x) =
            find_env(env, x, dummy_address)
        fun lookup_store (store, a) =
            find_store(store, a, dummy_value)
        fun dummy(store, n) = (dummy_value, store, n)
        fun makePrim prim (vs, store, n) =
            (case (prim, vs)
              of (Plus, [VInt i1, VInt i2]) => (VInt (i1 + i2), store, n)
               | (Times, [VInt i1, VInt i2]) => (VInt (i1 * i2), store, n)
               | (Ref, [v]) => (VCell n, extend(store, n, v), n+1)
               | (Deref, [VCell n']) => (lookup_store(store, n'), store, n)
               | (Assign, [VCell n', v]) => (lookup_store(store, n'), extend(store, n', v), n)
               (* TODO: lazy failing *)
               | _ => dummy(store, n))
        fun aux (e, env, store, n) : value * store * address =
            case e
             of Int i => (VInt i, store, n)
             | Var x => (lookup_store(store, lookup_env(env, x)), store, n)
             | Fun lam => (VClo (lam, env), store, n)
             | Call (f, args) =>
               let val (f', store, n) = aux (f, env, store, n)
                   val (args_rev', store, n) =
                       foldl (fn (arg, (args', store, n)) =>
                                 let val (arg', store, n) = aux (arg, env, store, n)
                                 in
                                     (arg' :: args', store, n)
                                 end)
                             ([], store, n) args
                   val args' = rev args_rev'
               in case f'
                   of VClo ((params, body), env) =>
                      if length args_rev' = length params
                      then
                          let val (env, store, n) =
                                  foldr2 (fn (a, b, (env, store, n)) =>
                                             (extend(env, a, n), extend(store, n, b), n+1))
                                         (env, store, n) params args'
                          in
                              aux (body, env, store, n)
                          end
                      else (* TODO: lazy failing *)
                          dummy(store, n)
                    | VPrim prim => makePrim prim (args', store, n)
                    (* TODO: lazy failing *)
                    | _ => dummy(store, n)
               end
             | IfZero (tst, thn, els) =>
               let val (tst', store, n) = aux (tst, env, store, n)
               in
                   case tst'
                    of (VInt 0) => aux (thn, env, store, n)
                    | _ => aux (els, env, store, n)
               end
             | Letrec (binds, body) =>
               let val (n', env) = foldl (fn ((x, lam), (n, env)) =>
                                             (n+1, extend(env, x, n)))
                                         (n, env) binds
                   val store = foldl (fn ((x, lam), store) =>
                                         extend(store, lookup_env(env, x), VClo (lam, env)))
                                     store binds
               in
                   aux (body, env, store, n')
               end
             | Prim prim =>
               (VPrim prim, store, n)
        val (final, _, _) = aux (e0, initial_env, initial_store, initial_address)
    in
        final
    end

val prog1 = Letrec([(1, ([2], (IfZero (Var 2,
                                       Int 1,
                                       Call (Prim Times,
                                             [Var 2,
                                              Call (Var 1,
                                                    [Call (Prim Plus,
                                                           [Var 2,
                                                            Int (~1)])])])))))],
                   Call (Var 1,
                         [Int 5]))
val result1 = interpret prog1
val result1' = VInt 120

val prog2 =
    Letrec ([(1, ([2], (Letrec ([(3, ([4], (IfZero (Var 4,
                                                   Var 2,
                                                   Call (Var 3,
                                                         [Call (Prim Plus,
                                                                [Var 4, Int (~1)])])))))],
                                (Var 3)))))],
            Letrec ([(5, ([6], (Call (Var 1, [Var 6]))))],
                    Call (Call (Call (Var 5, [Call (Var 1, [Int 1])]),
                                [Int 10]),
                          [Int 15])))
val result2 = interpret prog2
val result2' = VInt 1

val prog3 =
    Letrec ([(1, ([1],
                  Letrec ([(2, ([3],
                                IfZero (Var 3,
                                        Var 1,
                                        Call (Var 2,
                                              [Call (Prim Plus, [Var 3, Int (~1)])]))))],
                              Var 2)))],
            Call (Call (Var 1, [Int 1]),
                  [Int 10]))
val result3 = interpret prog3
val result3' = VInt 1

val prog4 =
    Letrec ([(1, ([2],
                  Letrec ([(3,
                            ([4],
                             IfZero (Var 4,
                                     Var 2,
                                     Call (Var 3, [Call (Prim Plus, [Var 4, Int (~1)])]))))],
                          Fun ([5], Var 5))))],
            Call (Call (Var 1, [Int 1]),
                  [Int 10]))
val result4 = interpret prog4
val result4' = VInt 10

val prog5 =
    Letrec ([(1, ([2],
                  Letrec ([(3, ([4], IfZero (Var 4, Var 2, Int (~1))))],
                          Var 3)))],
            Call (Call (Var 1, [Int 1]),
                  [Int 10]))
val result5 = interpret prog5
val result5' = VInt (~1)

val prog6 =
    Letrec ([(1, ([2],
                  Letrec ([(3, ([4], IfZero (Var 4, Var 2, Int (~1))))],
                          Var 3)))],
            Call (Call (Var 1, [Int 1]),
                  [Int 10]))
val result6 = interpret prog5
val result6' = VInt (~1)

val prim_ref = Fun ([1, 2], Call (Var 1, [Call (Prim Ref, [Var 2])]))
val prim_deref = Fun ([1, 2], Call (Var 1, [Call (Prim Deref, [Var 2])]))
val prim_assign = Fun ([1, 2, 3], Call (Var 1, [Call (Prim Assign, [Var 2, Var 3])]))
                    
val prog7 =
    Call (Fun ([101],
               Call (prim_ref,
                     [Fun ([1],
                           (Call (Fun ([102, 0],
                                       Call (Fun ([104],
                                                  Call (Fun ([7],
                                                             Call (prim_deref,
                                                                   [Fun ([6], IfZero (Var 6, 
                                                                                   Call (Var 104, [Int 0]), 
                                                                                   Call (Var 104, [Var 7]))),
                                                                    Var 0])), 
                                                        [Fun ([105, 8], Call (Var 104, [Var 8]))])), 
                                             [Fun ([5],
                                                   Call (prim_assign,
                                                         [Fun ([2],
                                                               (Call (Fun ([103, (~1)],
                                                                           (Call (prim_deref,
                                                                                  [Fun ([3],
                                                                                        IfZero (Var 3,
                                                                                                Call (Var 103, [Int 42]),
                                                                                                Call (prim_deref,
                                                                                                      [Fun ([4], Call (Var 4, [Var 103, Int 0])),
                                                                                                       Var 0]))), 
                                                                                   Var 0]))), 
                                                                      [Var 102, Var 2]))), 
                                                          Var 0, 
                                                          Var 5]))])),
                                  [Var 101, Var 1]))), 
                      Fun ([100, 0], Call (Var 100, [Var 0]))])),
          [Fun ([1], Var 1)])

val result7 = interpret prog7
val result7' = 42

val prog8 = IfZero (Int 0, Int 1, Int 2)
val result8 = interpret prog8
val result8' = 1
