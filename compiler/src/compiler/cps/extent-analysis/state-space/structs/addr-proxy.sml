
functor AddrHashCons (structure AddrBase : ADDR) : ADDR = struct

  type var = AddrBase.var
  type info = AddrBase.info

  structure HashConsAddr = MyHashCons (structure Base = AddrBase)
  open HashConsAddr

  fun same (a1, a2) =
      case compare (a1, a2)
       of EQUAL => true
        | _ => false

  fun hash a1 = index a1

  fun alloc (x, info) =
      HashConsAddr.make (AddrBase.alloc (x, info))

end

(* Proxy addresses. *)
structure AddrProxyBase :> ADDR where type var = Label.t and type info = TEnv.t * CPS.exp * TEnv.t =
struct

    type t = Label.t
    type var = Label.t
    type info = TEnv.t * CPS.exp * TEnv.t

    fun alloc (l, _) = l

    fun toString (l) = "[aP: " ^ (Label.toString l) ^ "]"

    val same = Label.same
    val compare = Label.compare
    val hash = Label.hash

    fun index _ = raise Fail "AddrProxy.index"
    fun fromIndex _ = raise Fail "AddrProxy.fromIndex"

    structure Set = Label.Set
    structure Map = Label.Map
    structure Tbl = Label.Tbl

end

structure AddrProxyTypeBase :> ADDR
    where type var = Label.t
      and type info = TEnv.t * CPS.exp * TEnv.t =
struct

    type t = Label.t * TEnv.t
    type var = Label.t
    type info = TEnv.t * CPS.exp * TEnv.t

    fun alloc (l, (tenv', _, _)) = (l, tenv')

    fun toString (l, tenv') = "[aP: " ^ (Label.toString l) ^ " " ^ (TEnv.toString tenv') ^ "]"

    fun same ((l1, tenv'1), (l2, tenv'2)) =
        Label.same (l1, l2) andalso TEnv.same (tenv'1, tenv'2)
    fun compare ((l1, tenv'1), (l2, tenv'2)) =
        case Label.compare (l1, l2)
         of EQUAL => TEnv.compare (tenv'1, tenv'2)
          | ord => ord
    fun hash (l, _) = Label.hash l (* TODO? *)

    fun index _ = raise Fail "AddrProxy.index"
    fun fromIndex _ = raise Fail "AddrProxy.fromIndex"

    structure Key = struct type ord_key = t val compare = compare end
    structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure Tbl = HashTableFn (HashKey)
    structure MSet = HashSetFn (HashKey)

end

(* A proxy address that tracks both the lambda and the call site. *)
structure AddrProxyTypeBase2 :> ADDR where type var = Label.t and type info = TEnv.t * CPS.exp * TEnv.t =
struct

    type t = Label.t * TEnv.t * Label.t * TEnv.t
    type var = Label.t
    type info = TEnv.t * CPS.exp * TEnv.t

    fun alloc (lab, (tenv', e as CPS.EXP (e_lab, _), tenv)) = (e_lab, tenv', lab, tenv)

    fun toString (e_lab, tenv', lab, tenv) = "[aP: " ^ (Label.toString e_lab) ^ " " ^ (TEnv.toString tenv') ^ " " ^ (Label.toString lab) ^ " " ^ (TEnv.toString tenv) ^ "]"

    fun same ((e_lab1, tenv'1, lab1, tenv1), (e_lab2, tenv'2, lab2, tenv2)) =
        Label.same (e_lab1, e_lab2) andalso Label.same (lab1, lab2) andalso TEnv.same (tenv'1, tenv'2) andalso TEnv.same (tenv1, tenv2)
    fun compare ((e_lab1, tenv'1, lab1, tenv1), (e_lab2, tenv'2, lab2, tenv2)) =
        case Label.compare (e_lab1, e_lab2)
         of EQUAL => (case Label.compare (lab1, lab2)
                       of EQUAL => (case TEnv.compare (tenv'1, tenv'2)
                                     of EQUAL => TEnv.compare (tenv1, tenv2)
                                      | ord => ord)
                        | ord => ord)
          | ord => ord
                  
    fun hash (e_lab, tenv', lab, tenv) = Label.hash lab

    fun index _ = raise Fail "AddrProxy.index"
    fun fromIndex _ = raise Fail "AddrProxy.fromIndex"

    local
        structure Key = struct type ord_key = t val compare = compare end
        structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    in
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure Tbl = HashTableFn (HashKey)
    end

end

structure AddrProxy = AddrHashCons (structure AddrBase = AddrProxyTypeBase)

