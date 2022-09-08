(* simple-ty-con.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Type constructors for SimpleAST IR.
 *)

structure SimpleTyCon : sig

    type t = SimpleTypes.tycon

  (* `newAbsTyc (name, tvs)` creates a new abstract type constructor. *)
    val newAbsTyc : (string * SimpleTypes.tyvar list) -> t

  (* create a new datatype tyc; it will have an empty constructor list *)
    val newDataTyc : (string * SimpleTypes.tyvar list) -> t

  (* return the name of a type constructor *)
    val nameOf : t -> string

  (* return a string representation *)
    val toString : t -> string

  (* return true if two type constructors are the same *)
    val same : t * t -> bool

  (* return a hash key for a type constuctor *)
    val hash : t -> word

  (* return the arity of a type constructor *)
    val arityOf : t -> int

  (* return the list of constructors for a datatype.  Returns the empty list for
   * abstract types.
   *)
    val consOf : t -> SimpleTypes.dcon list

  (* per-type properties *)
    val newProp : (t -> 'a) -> {
            clrFn : t -> unit,
            getFn : t -> 'a,
            peekFn : t -> 'a option,
            setFn : (t * 'a) -> unit
          }
    val newFlag : unit -> {
            getFn : t -> bool,
            setFn : t * bool -> unit
          }

  end = struct

    datatype t = datatype SimpleTypes.tycon
    datatype tycon_def = datatype SimpleTypes.tycon_def

  (* per-type properties *)
    fun propsOf (Tyc{props, ...}) = props
    fun newProp mkProp = PropList.newProp (propsOf, mkProp)
    fun newFlag () = PropList.newFlag propsOf

    fun newTyc (name, params, def) = Tyc{
            name = name,
            stamp = Stamp.new(),
            params = params,
            props = PropList.newHolder(),
            def = def
          }

  (* create a new abstract type constructor *)
    fun newAbsTyc (name, params) = newTyc (name, params, AbsTyc)

  (* create a new datatype tyc; it will have an empty constructor list *)
    fun newDataTyc (id, params) = newTyc (id, params, DataTyc{nCons = ref 0, cons = ref[]})

  (* return the name of a type constructor *)
    fun nameOf (Tyc{name, ...}) = name

    fun stampOf (Tyc{stamp, ...}) = stamp

    fun hash tyc = Stamp.hash (stampOf tyc)

    fun toString (Tyc{stamp, name, ...}) =
          concat [name, "_", Stamp.toString stamp]

  (* return true if two type constructors are the same *)
    fun same (tyc1, tyc2) = Stamp.same(stampOf tyc1, stampOf tyc2)

  (* compare two type constructors *)
    fun compare (tyc1, tyc2) = Stamp.compare(stampOf tyc1, stampOf tyc2)

  (* return the arity of a type constructor *)
    fun arityOf (Tyc{params, ...}) = List.length params

    fun consOf (Tyc{def=AbsTyc, ...}) = []
      | consOf (Tyc{def=DataTyc{cons, ...}, ...}) = !cons

  end
