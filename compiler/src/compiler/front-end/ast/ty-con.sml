(* ty-con.sml
 *
 * COPYRIGHT (c) 2007 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Utility operations on type constructors.
 *)

structure TyCon : sig

  (* `newAbsTyc {id, arity, span, eq, mut}` creates a new abstract type
   * constructor.
   *)
    val newAbsTyc : {
            id : BindTree.tycon,        (* the type constructor's name *)
            arity : int,                (* number of type parameters *)
            span : int,                 (* number of distinct values (~1 for unbounded) *)
            eq : bool,                  (* true for equality types *)
            mut : bool                  (* true for mutable types *)
          } -> Types.tycon

  (* create a new datatype tyc; it will have an empty constructor list *)
    val newDataTyc : (BindTree.tycon * Types.tyvar list) -> Types.tycon

  (* the `unit` type constructor *)
    val unitTyc : Types.tycon

  (* return the name of a type constructor *)
    val nameOf : Types.tycon -> string

  (* return a string representation *)
    val toString : Types.tycon -> string

  (* return true if two type constructors are the same *)
    val same : Types.tycon * Types.tycon -> bool

  (* return a hash key for a type constuctor *)
    val hash : Types.tycon -> word

  (* return the arity of a type constructor *)
    val arityOf : Types.tycon -> int

  (* return the number of constructors for a tycon; returns ~1 for types with unbounded
   * numbers of values.
   *)
    val spanOf : Types.tycon -> int

  (* return the list of constructors for a datatype.  Returns the empty list for
   * abstract types.
   *)
    val consOf : Types.tycon -> Types.dcon list

  (* per-type properties *)
    val newProp : (Types.tycon -> 'a) -> {
            clrFn : Types.tycon -> unit,
            getFn : Types.tycon -> 'a,
            peekFn : Types.tycon -> 'a option,
            setFn : (Types.tycon * 'a) -> unit
          }
    val newFlag : unit -> {
            getFn : Types.tycon -> bool,
            setFn : Types.tycon * bool -> unit
          }

  (* equality type property; these should not be used directly.  Instead, use the
   * function `TypeUtil.isEqType`
   *)
    val getEqMark : Types.tycon -> bool
    val peekEqMark : Types.tycon -> bool option
    val markEq : Types.tycon * bool -> unit

  (* mutable type property. *)
    val isMutable : Types.tycon -> bool

  (* hash tables keyed by type constructors *)
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = Types.tycon

  end = struct

    datatype tycon = datatype Types.tycon
    datatype tycon_def = datatype Types.tycon_def

  (* per-type properties *)
    fun propsOf (Tyc{props, ...}) = props
    fun newProp mkProp = PropList.newProp (propsOf, mkProp)
    fun newFlag () = PropList.newFlag propsOf

  (* equality type property.  This property is set for abstract types when they
   * are defined and for datatypes after their constructors are checked (see
   * typechecker.sml).
   *)
    local
      val {peekFn, getFn, setFn, ...} = newProp (fn _ => false)
    in
    val getEqMark = getFn
    val peekEqMark = peekFn
    fun markEq (tyc, flg) = setFn(tyc, true)
    end

  (* mutable type property.  This property is set for abstract types when they
   * are defined.
   *)
    local
      val {getFn, setFn} = newFlag ()
    in
    val isMutable = getFn
    fun markMutTyc tyc = setFn(tyc, true)
    end

    fun newTyc (id, params, def) = Tyc{
            name = BindTree.TycId.nameOf id,
            stamp = Stamp.new(),
            params = params,
            props = PropList.newHolder(),
            def = def
          }

  (* create a new abstract type constructor *)
    local
      val params = Vector.fromList["'a", "'b", "'c", "'d"]
    in
    fun newAbsTyc {id, arity, span, eq, mut} = let
          fun mkParam i = TyVar.new'(Vector.sub(params, i))
          val tyc = newTyc (id, List.tabulate(arity, mkParam), AbsTyc{span=span})
          in
            markEq (tyc, eq);
            if mut then markMutTyc tyc else ();
            tyc
          end
    end

  (* create a new datatype tyc; it will have an empty constructor list *)
    fun newDataTyc (id, params) = newTyc (id, params, DataTyc{nCons = ref 0, cons = ref[]})

  (* the `unit` type is the one abstract type that has a finite span.
   * NOTE: we define this here so that the "ast" directory does not have to depend
   * on the "env" directory.
   *)
    val unitTyc = newAbsTyc{
            id = BasisBinds.unit_ty, arity = 0, span = 1, eq = true, mut = false
          }

  (* return the name of a type constructor *)
    fun nameOf (Tyc{name, ...}) = name

    fun stampOf (Tyc{stamp, ...}) = stamp

    fun hash tyc = Stamp.hash (stampOf tyc)

    fun toString (Tyc{stamp, name, ...}) = name ^ Stamp.toString stamp

  (* return true if two type constructors are the same *)
    fun same (tyc1, tyc2) = Stamp.same(stampOf tyc1, stampOf tyc2)

  (* compare two type constructors *)
    fun compare (tyc1, tyc2) = Stamp.compare(stampOf tyc1, stampOf tyc2)

  (* return the arity of a type constructor *)
    fun arityOf (Tyc{params, ...}) = List.length params

  (* return the number of constructors for a tycon; returns ~1 for types with unbounded
   * numbers of values.
   *)
    fun spanOf (Tyc{def=AbsTyc{span, ...}, ...}) = span
      | spanOf (Tyc{def=DataTyc{cons=ref dcs, ...}, ...}) = List.length dcs

    fun consOf (Tyc{def=AbsTyc _, ...}) = []
      | consOf (Tyc{def=DataTyc{cons, ...}, ...}) = !cons

    structure Tbl = HashTableFn (
      struct
        type hash_key = tycon
        val hashVal = hash
        val sameKey = same
      end)

  end
