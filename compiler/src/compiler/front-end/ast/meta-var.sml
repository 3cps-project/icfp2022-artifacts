(* meta-var.sml
 *
 * COPYRIGHT (c) 2007 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * CMSC 22610 Sample code (Winter 2007)
 *
 * Meta-variable utility code.
 *)

structure MetaVar : sig

  (* create a fresh meta variable at the given lambda depth; if the depth is NONE,
   * then the variable has infinite depth
   *)
    val new : int option -> Types.meta

  (* create a fresh meta variable with infinite depth for the given type variable *)
    val new' : Types.tyvar -> Types.meta

  (* are two meta-variables the same? *)
    val same : Types.meta * Types.meta -> bool

  (* finite sets and maps on meta variables *)
    structure Set : ORD_SET where type Key.ord_key = Types.meta
    structure Map : ORD_MAP where type Key.ord_key = Types.meta

  end = struct

    datatype meta = datatype Types.meta

    val infinity = 100000

    fun mk (d, eq, cls) = MVar{
            info = ref(Types.UNIV{depth = d, eq = eq, cls = cls}),
            stamp = Stamp.new()
          }

  (* create a fresh meta variable *)
    fun new (SOME d) = mk (d, false, Types.Any)
      | new NONE = mk (infinity, false, Types.Any)

    fun new' (Types.TVar{eq, cls, ...}) = mk (infinity, eq, cls)

  (* are two meta-variables the same? *)
    fun same (MVar{stamp=a, ...}, MVar{stamp=b, ...}) = Stamp.same(a, b)

    structure Set = RedBlackSetFn (
      struct
        type ord_key = meta
        fun compare (MVar{stamp = a, ...}, MVar{stamp = b, ...}) = Stamp.compare(a, b)
      end)
    structure Map = RedBlackMapFn (
      struct
        type ord_key = meta
        fun compare (MVar{stamp = a, ...}, MVar{stamp = b, ...}) = Stamp.compare(a, b)
      end)

  end
