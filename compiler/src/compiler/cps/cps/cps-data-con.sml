(* cps-data-con.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSDataCon : sig

    type t = CPSTypes.dcon

    val nameOf : t -> string
    val toString : t -> string

  (* returns the type of a nullary constructor or the result type of non-nullary
   * constructor.
   *)
    val typeOf : t -> CPSTypes.ty_scheme

    val same : t * t -> bool
    val compare : t * t -> order

  end = struct

    datatype t = datatype CPSTypes.dcon

    fun nameOf (DCon{name, ...}) = name
    fun toString (DCon{name, stamp, ...}) = name ^ Stamp.toString stamp

    fun typeOf (DCon{owner, ...}) =
          CPSTypes.TyScheme(CPSTyCon.paramsOf owner, CPSTypes.ConTy([], owner))

    fun same (DCon{stamp=s1, ...}, DCon{stamp=s2, ...}) = Stamp.same(s1, s2)

    fun compare (DCon{stamp=s1, ...}, DCon{stamp=s2, ...}) = Stamp.compare(s1, s2)

  end
