(* var.sml
 *
 * COPYRIGHT (c) 2019 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * AST and SimpleAST variables
 *)

structure Var : sig

    type t

    val new : BindTree.varid * Types.ty -> t
    val newPoly : BindTree.varid * Types.ty_scheme -> t

  (* for generating variables that do not correspond to variables in
   * the source program.
   *)
    val newTmp : string -> Types.ty -> t
    val newPolyTmp : string -> Types.ty_scheme -> t

    val copy : t -> t

    val nameOf : t -> string

    val same : t * t -> bool

  (* variable's name with its stamp *)
    val toString : t -> string

    val typeOf : t -> Types.ty_scheme
    val monoTypeOf : t -> Types.ty

  (* return the specialized type of a variable *)
    val typeOf' : t * Types.ty list -> Types.ty

  (* close the type of the variable w.r.t. to the given lambda-nesting depth.
   * The first argument is a list of any explicit type variables that the
   * variable's binding is in the scope of.
   *)
    val closeTypeOf : Types.tyvar list * int * t -> unit

  (* update the type of a variable; this function is required for inlining in
   * the SimpleAST optimizer.
   *)
    val updateType : t * Types.ty_scheme -> unit

  (* define a property for variables *)
    val newProp : (t -> 'a) -> {
            clrFn  : t -> unit,
            getFn  : t -> 'a,
            peekFn : t -> 'a option,
            setFn  : t * 'a -> unit
          }
  (* define a boolean property for variables *)
    val newFlag : unit -> { getFn : t -> bool, setFn : t * bool -> unit }

  (* Marks on functions in the AST/Simple AST that identify them as being
   * "join points", which can be mapped to continuations when converting
   * to CPS.  These arise from pattern-match compilation, but might also
   * be identified via program analysis.
   *)
    val markJoin : t -> unit
    val isJoin : t -> bool

    structure Set : ORD_SET where type Key.ord_key = t
    structure Map : ORD_MAP where type Key.ord_key = t
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    datatype t = Var of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the name of the variable *)
            ty : Types.ty_scheme ref,   (* type of variable *)
            props : PropList.holder     (* holder for attaching properties *)
          }

    fun mk (name, ty) = Var{
            stamp = Stamp.new(),
            name = name,
            ty = ref ty,
            props = PropList.newHolder()
          }

    fun newPoly (id, ty) = mk (BindTree.VarId.nameOf id, ty)

    fun new (id, ty) = mk (BindTree.VarId.nameOf id, Types.TyScheme([], ty))

    fun copy (Var{name, ty, ...}) = mk (name, !ty)

    fun newPolyTmp prefix = let
          val cnt = ref 0
          in
            fn tyScm => let
                val id = !cnt
                in
                  cnt := id + 1;
                  mk (prefix ^ Int.toString id, tyScm)
                end
          end

    fun newTmp prefix = let
          val new = newPolyTmp prefix
          in
            fn ty => new (Types.TyScheme([], ty))
          end

    fun nameOf (Var{name, ...}) = name

    fun toString (Var{name, stamp, ...}) = concat[name, "_", Stamp.toString stamp]

    fun typeOf (Var{ty, ...}) = !ty

    fun monoTypeOf (Var{ty=ref(Types.TyScheme([], ty)), ...}) = TypeUtil.prune ty
      | monoTypeOf (Var{name, ...}) = raise Fail(concat[
            "monoTypeOf: ", name, " is polymorphic"
          ])

    fun typeOf' (Var{ty, ...}, tys) = TypeUtil.applyScheme(!ty, tys)

    fun closeTypeOf (tvs, depth, x as Var{ty as ref(Types.TyScheme(_, ty')), ...}) =
          ty := TypeUtil.closeTy(tvs, depth, ty')

    fun updateType (Var{ty, ...}, tyS) = (ty := tyS)

    fun same (Var{stamp=id1, ...}, Var{stamp=id2, ...}) = Stamp.same(id1, id2)

    fun compare (Var{stamp=id1, ...}, Var{stamp=id2, ...}) = Stamp.compare(id1, id2)

    fun hash (Var{stamp, ...}) = Stamp.hash stamp

    fun newProp initFn = PropList.newProp (fn (Var{props, ...}) => props, initFn)
    fun newFlag () = PropList.newFlag (fn (Var{props, ...}) => props)

    local
      val {getFn, setFn} = newFlag ()
    in
    fun markJoin f = setFn(f, true)
    val isJoin = getFn
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
