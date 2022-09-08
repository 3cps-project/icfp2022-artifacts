(* cps-types.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Types for the 3-CPS IR.
 *)

structure CPSTypes =
  struct

    type tyvar = CPSTyVar.t

    datatype ty_scheme = TyScheme of tyvar list * t

    and t
      = VarTy of tyvar
      | ConTy of (t list * tycon)
      | TupleTy of t list
      | FunTy of t list * ct list

    and ct = ContTy of t list

    and tycon = Tyc of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the type name *)
            params : tyvar list,        (* type parameters *)
            props : PropList.holder,
            def : tycon_def             (* definition of tyc *)
          }

    and tycon_def
      = AbsTyc
      | DataTyc of dcon list ref

    and dcon = DCon of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the name of the constructor *)
            owner : tycon,              (* the datatype for which this is a constructor *)
            argTy : t option,           (* argument type; NONE for nullary constructors *)
            props : PropList.holder
          }

(* FIXME: move this function to CPSTypeUtil *)
    fun compare (t1, t2) = (case (t1, t2)
           of (VarTy tv1, VarTy tv2) => CPSTyVar.compare (tv1, tv2)
            | (VarTy _, _) => LESS
            | (_, VarTy _) => GREATER
            | (ConTy(tys1, Tyc{stamp=id1, ...}), ConTy(tys2, Tyc{stamp=id2, ...})) => (
                case Stamp.compare(id1, id2)
                 of EQUAL => List.collate compare (tys1, tys2)
                  | order => order
                (* end case *))
            | (ConTy _, _) => LESS
            | (_, ConTy _) => GREATER
            | (TupleTy tys1, TupleTy tys2) => List.collate compare (tys1, tys2)
            | (TupleTy _, _) => LESS
            | (_, TupleTy _) => GREATER
            | (FunTy(tys1, ctys1), FunTy(tys2, ctys2)) => (
                case List.collate compare (tys1, tys2)
                 of EQUAL => List.collate cmpCTy (ctys1, ctys2)
                  | order => order
                (* end case *))
          (* end case *))

    and cmpCTy (ContTy tys1, ContTy tys2) = List.collate compare (tys1, tys2)

    fun toString ty =
        case ty
         of VarTy x =>
            CPSTyVar.toString x
          | ConTy (tys, Tyc tycon) =>
            String.concat [#name tycon, case tys of [] => "" | _ => (String.concat [" (", String.concatWithMap " " toString tys, ")"])]
          | TupleTy tys =>
            String.concat ["(", String.concatWithMap " * " toString tys, ")"]
          | FunTy (tys, ctys) => let
              fun cty_toString (ContTy tys) = String.concat ["[", String.concatWithMap " " toString tys, "]"]
              val ctys_string = String.concatWith " " (List.map cty_toString ctys)
              val tys_string = String.concatWithMap " * " toString tys
          in String.concat [tys_string, " -> ", ctys_string] end

    fun same (ty1, ty2) =
        case compare (ty1, ty2)
         of EQUAL => true
          | _ => false

    fun hash ty = 
        case ty
         of VarTy x => Word.* (0wx7, CPSTyVar.hash x)
          (* should we be hashing the stamp? *)
          | ConTy (tys, Tyc tycon) => Word.* (0wx11, hash_list (tys, Stamp.hash (#stamp tycon)))
          | TupleTy tys => hash_list (tys, 0wx13)
          | FunTy (tys, ctys) => List.foldl (fn (ContTy tys, acc) => hash_list (tys, acc))
                                            (hash_list (tys, 0wx17)) ctys
    and hash_list (tys, initial) =
        List.foldl (fn (ty, acc) => Word.* (acc, hash ty)) initial tys
                  

    structure Key = struct type ord_key = t val compare = compare end
    structure HashKey = struct type hash_key = t val hashVal = hash val sameKey = same end
    structure Map = RedBlackMapFn (Key)
    structure Set = RedBlackSetFn (Key)
    structure Tbl = HashTableFn (HashKey)

  end
