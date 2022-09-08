(* simple-data-con.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure SimpleDataCon : sig

    type t = SimpleTypes.dcon

  (* create a new data constructor and add it to the end of its parent's
   * constructor list.
   *)
    val new : SimpleTypes.tycon -> (string * SimpleTypes.ty option) -> t

  (* return true if two data constructors are the same (i.e., have the same stamp) *)
    val same : t * t -> bool

  (* compare two data constructors; the ordering is based on their stamps *)
    val compare : t * t -> order

  (* compare two data constructors with nullary constructors ordered before
   * non-nullary constructors and otherwise by name.  This function is used
   * to specify the canonical order of constructors for a datatype.
   *)
    val lexCompare : t * t -> order

  (* return the name of the data constructor *)
    val nameOf : t -> string

    val toString : t -> string

  (* return the type of the data constructor *)
    val typeOf : t -> SimpleTypes.ty_scheme

  (* return the argument type of the data constructor (if any) *)
    val argTypeOf : t -> SimpleTypes.ty_scheme option

  (* return the datatype type constructor that owns this data constructor *)
    val ownerOf : t -> SimpleTypes.tycon

  (* return the instantiated type/argument type of the data constructor *)
    val typeOf' : t * SimpleTypes.ty list -> SimpleTypes.ty
    val argTypeOf' : t * SimpleTypes.ty list -> SimpleTypes.ty option
    val resultTypeOf' : t * SimpleTypes.ty list -> SimpleTypes.ty

  (* return true if the data constructor is nullary *)
    val isNullary : t -> bool

  (* per-constructor properties *)
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

  (* hash tables keyed by data constructors *)
    structure Tbl : MONO_HASH_TABLE where type Key.hash_key = t

  end = struct

    structure Ty = SimpleTypes
    structure TyUtil = SimpleTypeUtil

    datatype t = datatype Ty.dcon

    fun new (tyc as Ty.Tyc{def=Ty.DataTyc{cons, ...}, ...}) (name, argTy) = let
          val dcon = DCon{
                  stamp = Stamp.new(),
                  name = name,
                  owner = tyc,
                  argTy = argTy,
                  props = PropList.newHolder()
                }
          in
            cons := !cons @ [dcon];
            dcon
          end
      | new tyc (name, argTy) = raise Fail(concat[
            "DataCon.new (", SimpleTyCon.toString tyc, ")"
          ])

    fun same (DCon{stamp=a, ...}, DCon{stamp=b, ...}) = Stamp.same(a, b)

    fun compare (DCon{stamp=a, ...}, DCon{stamp=b, ...}) = Stamp.compare(a, b)

    fun lexCompare (DCon{argTy=NONE, ...}, DCon{argTy=SOME _, ...}) =  LESS
      | lexCompare (DCon{argTy=SOME _, ...}, DCon{argTy=NONE, ...}) = GREATER
      | lexCompare (DCon{name=n1, ...}, DCon{name=n2, ...}) = String.compare(n1, n2)

    fun nameOf (DCon{name, ...}) = name

    fun argTypeOf (DCon{argTy=NONE, ...}) = NONE
      | argTypeOf (DCon{owner as Ty.Tyc{params, ...}, argTy=SOME ty, ...}) =
          SOME(Ty.TyScheme(params, ty))

    fun typeOf (DCon{owner as Ty.Tyc{params, ...}, argTy, ...}) = let
          val ty = Ty.ConTy(List.map Ty.VarTy params, owner)
          in
            case argTy
             of NONE => Ty.TyScheme(params, ty)
              | SOME ty' => Ty.TyScheme(params, Ty.FunTy(ty', ty))
            (* end case *)
          end

    fun ownerOf (DCon{owner, ...}) = owner

    fun typeOf' (dc, args) = TyUtil.applyScheme(typeOf dc, args)

    fun resultTypeOf' (DCon{owner as Ty.Tyc{params, ...}, ...}, args) = let
          val ty = Ty.ConTy(List.map Ty.VarTy params, owner)
          in
            TyUtil.applyScheme(Ty.TyScheme(params, ty), args)
          end

    fun argTypeOf' (DCon{owner as Ty.Tyc{params, ...}, argTy, ...}, args) = (
          case argTy
           of NONE => NONE (* nullary constructor *)
            | SOME ty => SOME(TyUtil.applyScheme(Ty.TyScheme(params, ty), args))
          (* end case *))

    fun isNullary (DCon{argTy = NONE, ...}) = true
      | isNullary _ = false

    fun toString (DCon{stamp, name, owner, argTy, ...}) = String.concat [
            name, "_", Stamp.toString stamp,
            "(", Option.getOpt (Option.map TyUtil.toString argTy, ""), ")",
            ":", SimpleTyCon.toString owner
          ]

  (* per-constructor properties *)
    fun propsOf (DCon{props, ...}) = props
    fun newProp mkProp = PropList.newProp (propsOf, mkProp)
    fun newFlag () = PropList.newFlag propsOf

    structure Tbl = HashTableFn (
      struct
        type hash_key = t
        fun hashVal (DCon{stamp, ...}) = Stamp.hash stamp
        val sameKey = same
      end)

  end

