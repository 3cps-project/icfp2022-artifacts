(* simple-var.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Simple AST variables.
 *)

structure SimpleVar : sig

    type t

  (* create a new monomorphic variable *)
    val new : string * SimpleTypes.ty -> t

  (* create a new polymorphic variable *)
    val newPoly : string * SimpleTypes.ty_scheme -> t

  (* `newTmp prefix` returns a generator for temporary variables *)
    val newTmp : string -> SimpleTypes.ty -> t

  (* `copy x` creates a new variable with the same name and type as `x` *)
    val copy : t -> t

  (* return a variable's name *)
    val nameOf : t -> string

  (* variable's name with its stamp *)
    val toString : t -> string

  (* are two variables the same? *)
    val same : t * t -> bool

  (* compare variables *)
    val compare : t * t -> order

    val typeOf : t -> SimpleTypes.ty_scheme
    val monoTypeOf : t -> SimpleTypes.ty

  (* define a property for variables *)
    val newProp : (t -> 'a) -> {
            clrFn  : t -> unit,
            getFn  : t -> 'a,
            peekFn : t -> 'a option,
            setFn  : t * 'a -> unit
          }
  (* define a boolean property for variables *)
    val newFlag : unit -> { getFn : t -> bool, setFn : t * bool -> unit }

  (* mapping from variables to the label of the expression that binds them *)
    val setBindingLabel : t * Label.t -> unit
    val getBindingLabel : t -> Label.t

  (* Marks on functions in the AST/Simple AST that identify them as being
   * "join points", which can be mapped to continuations when converting
   * to CPS.  These arise from pattern-match compilation, but might also
   * be identified via program analysis.
   *)
    val markJoin : t -> unit
    val isJoin : t -> bool

  (* a mark to signify that a function should be inlined whenever possible *)
    val markAlwaysInline : t -> unit
    val alwaysInline : t -> bool

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    structure Ty = SimpleTypes

    datatype t = Var of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the name of the variable *)
            ty : Ty.ty_scheme,  (* type of variable *)
            props : PropList.holder     (* holder for attaching properties *)
          }

    fun mk (name, ty) = Var{
            stamp = Stamp.new(),
            name = name,
            ty = ty,
            props = PropList.newHolder()
          }

    fun newPoly (name, ty) = mk (name, ty)

    fun new (name, ty) = mk (name, Ty.TyScheme([], ty))

    fun copy (Var{name, ty, ...}) = mk (name, ty)

    fun newTmp prefix = let
          val cnt = ref 0
          in
            fn ty => let
                val id = !cnt
                in
                  cnt := id + 1;
                  new (prefix ^ Int.toString id, ty)
                end
          end

    fun nameOf (Var{name, ...}) = name

    fun toString (Var{name, stamp, ...}) = concat[name, "_", Stamp.toString stamp]

    fun typeOf (Var{ty, ...}) = ty

    fun monoTypeOf (Var{ty=Ty.TyScheme([], ty), ...}) = ty
      | monoTypeOf (Var{name, ...}) = raise Fail(concat[
            "monoTypeOf: ", name, " is polymorphic"
          ])

    fun same (Var{stamp=id1, ...}, Var{stamp=id2, ...}) = Stamp.same(id1, id2)

    fun compare (Var{stamp=id1, ...}, Var{stamp=id2, ...}) = Stamp.compare(id1, id2)

    fun hash (Var{stamp, ...}) = Stamp.hash stamp

    fun newProp initFn = PropList.newProp (fn (Var{props, ...}) => props, initFn)
    fun newFlag () = PropList.newFlag (fn (Var{props, ...}) => props)

    local
      val {getFn, setFn} = newFlag ()
    in
    fun markJoin f = if Controls.get Ctl.joinConts then setFn(f, true) else ()
    val isJoin = getFn
    end (* local *)

    local
      val {getFn, setFn} = newFlag ()
    in
    fun markAlwaysInline f = setFn(f, true)
    val alwaysInline = getFn
    end (* local *)

    local
      val {setFn : t * Label.t -> unit, getFn, ...} =
            newProp (fn x => raise Fail("no binding label for " ^ toString x))
    in
    val setBindingLabel = setFn
    val getBindingLabel = getFn
    end (* local *)

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

  end
