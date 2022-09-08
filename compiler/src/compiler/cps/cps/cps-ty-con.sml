(* cps-ty-con.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSTyCon : sig

    type t = CPSTypes.tycon

  (* `newAbsTyc (name, arity)` creates a new abstract type
   * constructor.
   *)
    val newAbsTyc : string * int -> t

  (* create a new datatype type constructor.  This function returns the type
   * constructor and a function for defining the list of data constructors.
   *)
    val newDataTyc : (string * CPSTyVar.t list) -> {
            dt : t,
            setCons : (string * CPSTypes.t option) list -> CPSTypes.dcon list
          }

    val nameOf : t -> string

    val paramsOf : t -> CPSTyVar.t list

    val same : t * t -> bool
    val compare : t * t -> order

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

    datatype t = datatype CPSTypes.tycon
    datatype tycon_def = datatype CPSTypes.tycon_def

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
    fun newAbsTyc (name, arity) = let
          fun mkParam i = CPSTyVar.new()
          in
            newTyc (name, List.tabulate(arity, mkParam), AbsTyc)
          end

    fun newDataTyc (name, tvs) = let
          val cons = ref[]
          val tyc = newTyc(name, tvs, DataTyc cons)
          fun mkCons (name, ty) = CPSTypes.DCon{
                  stamp = Stamp.new(),
                  name = name,
                  owner = tyc,
                  argTy = ty,
                  props = PropList.newHolder()
                }
          in {
            dt = tyc,
            setCons = fn dcs => let
                val dcs = List.map mkCons dcs
                in
                  cons := dcs; dcs
                end
          } end

    fun nameOf (Tyc{name, ...}) = name

    fun paramsOf (Tyc{params, ...}) = params

    fun same (Tyc{stamp=id1, ...}, Tyc{stamp=id2, ...}) = Stamp.same(id1, id2)

    fun compare (Tyc{stamp=id1, ...}, Tyc{stamp=id2, ...}) = Stamp.compare(id1, id2)

  end
