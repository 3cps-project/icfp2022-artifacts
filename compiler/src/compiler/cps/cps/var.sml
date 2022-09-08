(* var.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Lambda and continuation variables for the 3CPS IR.
 *)

signature CPS_VAR = sig

    type t
    type ty

    val new : string * int * ty * Extent.t -> t

    val newTmp : string * ty * Extent.t -> t

    val nameOf : t -> string

  (* variable's name with its stamp *)
    val toString : t -> string

    val typeOf : t -> ty

    val setExtent : t * Extent.t -> unit
    val extentOf : t -> Extent.t

  (* define a property for variables *)
    val newProp : (t -> 'a) -> {
            clrFn  : t -> unit,
            getFn  : t -> 'a,
            peekFn : t -> 'a option,
            setFn  : t * 'a -> unit
          }
  (* define a boolean property for variables *)
    val newFlag : unit -> { getFn : t -> bool, setFn : t * bool -> unit }

    val compare : t * t -> order
    val same : t * t -> bool
    val hash : t -> word

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

end

functor CPSVarFn (type ty) = struct

    type ty = ty

    datatype t = V of {
        prefix : string,
        name : string,
        stamp : Stamp.t,
        ty : ty,
        extent : Extent.t ref,
        useCnt : int ref,
        props : PropList.holder
      }

    fun new (prefix, id, ty, ext) = V{
            prefix = prefix, name = prefix ^ Int.toString id,
            ty = ty, extent = ref ext,
            stamp = Stamp.new(),
            useCnt = ref 0,
            props = PropList.newHolder()
          }

    val cnt = ref 0

    fun newTmp (prefix, ty, ext) = let
          val id = !cnt
    in
        cnt := id + 1;
        new (prefix, id, ty, ext)
    end

    fun prefixOf (V{prefix, ...}) = prefix

    fun nameOf (V{name, ...}) = name

    fun toString (V{name, stamp, ...}) = name ^ Stamp.toString stamp

    fun typeOf (V{ty, ...}) = ty

    fun setExtent (V{extent, ...}, ext) = (extent := ext)
    fun extentOf (V{extent, ...}) = !extent

    fun newProp initFn = PropList.newProp (fn (V{props, ...}) => props, initFn)
    fun newFlag () = PropList.newFlag (fn (V{props, ...}) => props)

    fun same (V{stamp=id1, ...}, V{stamp=id2, ...}) = Stamp.same(id1, id2)

    fun compare (V{stamp=id1, ...}, V{stamp=id2, ...}) = Stamp.compare(id1, id2)

    fun hash (V{stamp, ...}) = Stamp.hash stamp

    structure Set = RedBlackSetFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Map = RedBlackMapFn (
      struct
        type ord_key = t
        val compare = compare
      end)
    structure Tbl = HashTableFn (
      struct
        type hash_key = t
        val hashVal = hash
        val sameKey = same
      end)

  end (* functor VarFn *)

structure LVar =
  struct
    local
      structure LV = CPSVarFn(type ty = CPSTypes.ty_scheme)
    in
    open LV
    fun monoTypeOf x = (case typeOf x
           of CPSTypes.TyScheme([], ty) => ty
            | _ => raise Fail(concat["monoTypeOf: ", toString x, " is polymorphic"])
          (* end case *))
    end (* local *)
  end (* LVar *)

structure CVar = CPSVarFn(type ty = CPSTypes.ct)

