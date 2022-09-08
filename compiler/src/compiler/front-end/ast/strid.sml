(* strid.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Representation of structure identifiers in the AST.
 *)

structure StrId : sig

    type t

    val new : BindTree.strid -> t

    val nameOf : t -> string

    val same : t * t -> bool
    val compare : t * t -> order

  (* variable's name with its stamp *)
    val toString : t -> string

  (* define a property for variables *)
    val newProp : (t -> 'a) -> {
            clrFn  : t -> unit,
            getFn  : t -> 'a,
            peekFn : t -> 'a option,
            setFn  : t * 'a -> unit
          }
  (* define a boolean property for variables *)
    val newFlag : unit -> { getFn : t -> bool, setFn : t * bool -> unit }

  end = struct

    datatype t = SId of {
        name : string,
        stamp : Stamp.t,
        props : PropList.holder
      }

    fun new strid = SId{
            name = BindTree.StrId.nameOf strid,
            stamp = Stamp.new(),
            props = PropList.newHolder()
          }

    fun nameOf (SId{name, ...}) = name

    fun toString (SId{name, stamp, ...}) = concat[name, "_", Stamp.toString stamp]

    fun same (SId{stamp=id1, ...}, SId{stamp=id2, ...}) = Stamp.same(id1, id2)

    fun compare (SId{stamp=id1, ...}, SId{stamp=id2, ...}) = Stamp.compare(id1, id2)

    fun newProp initFn = PropList.newProp (fn (SId{props, ...}) => props, initFn)
    fun newFlag () = PropList.newFlag (fn (SId{props, ...}) => props)

  end
