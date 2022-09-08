(* ty-var.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Type variables
 *)

structure TyVar : sig

  (* create a new type variable *)
    val new : BindTree.tyvar -> Types.tyvar
    val new' : string -> Types.tyvar

  (* create a new type variable with a specified type class *)
    val newOfClass : string * bool * Types.ty_class -> Types.tyvar

  (* return the variable's name *)
    val nameOf : Types.tyvar -> string

  (* unique string representation of type variable *)
    val toString : Types.tyvar -> string

  (* return the class of the variable (if any) *)
    val classOf : Types.tyvar -> Types.ty_class

  (* return true if two type variables are the same (i.e., have the same stamp) *)
    val same : Types.tyvar * Types.tyvar -> bool

  (* sets of type variables *)
    structure Set : ORD_SET where type Key.ord_key = Types.tyvar

  (* finite maps on type variables *)
    structure Map : ORD_MAP where type Key.ord_key = Types.tyvar

  end = struct

    datatype tyvar = datatype Types.tyvar

    fun newOfClass (name, eq, cls) = TVar{
            name = name, stamp = Stamp.new(), eq = eq, cls = cls
          }

    fun new' name = newOfClass(name, false, TypeClass.Any)

    fun new id = new' (BindTree.TyVar.nameOf id)

    fun nameOf (TVar{name, ...}) = name

    fun toString (TVar{stamp, name, eq, cls}) = let
          val l = (case cls of TypeClass.Any => [] | _ => ["_", TypeClass.toString cls])
          val l = name :: "_" :: Stamp.toString stamp :: l
          val l = if eq then "'" :: l else l
          in
            String.concat l
          end

    fun classOf (TVar{cls, ...}) = cls

    fun same (TVar{stamp=a, ...}, TVar{stamp=b, ...}) = Stamp.same(a, b)

    fun compare (TVar{stamp = a, ...}, TVar{stamp = b, ...}) = Stamp.compare(a, b)

    structure Set = RedBlackSetFn (
      struct
        type ord_key = tyvar
        val compare = compare
      end)

    structure Map = RedBlackMapFn (
      struct
        type ord_key = tyvar
        val compare = compare
      end)

  end
