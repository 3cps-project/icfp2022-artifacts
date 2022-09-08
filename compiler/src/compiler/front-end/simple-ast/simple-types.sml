(* simple-types.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Simple AST Types.
 *)

structure SimpleTypes =
   struct

    datatype ty_scheme = TyScheme of (tyvar list * ty)

    and ty
      = VarTy of tyvar
      | ConTy of (ty list * tycon)
      | FunTy of ty * ty
      | TupleTy of ty list

    and tyvar = TVar of Stamp.t         (* represented by its unique stamp *)

    and tycon = Tyc of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the type name *)
            params : tyvar list,        (* type parameters *)
            props : PropList.holder,
            def : tycon_def             (* definition of tyc *)
          }

    and tycon_def
      = AbsTyc
      | DataTyc of {
            nCons : int ref,            (* number of constructors *)
            cons : dcon list ref        (* list of data constructors *)
          }

    and dcon = DCon of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the name of the constructor *)
            owner : tycon,              (* the datatype for which this is a constructor *)
            argTy : ty option,          (* argument type; NONE for nullary constructors *)
            props : PropList.holder
          }

  end
