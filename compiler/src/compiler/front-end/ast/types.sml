(* types.sml
 *
 * COPYRIGHT (c) 2019 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *)

structure Types =
  struct

  (* type classes for overloading *)
    datatype ty_class = datatype TypeClass.t

    datatype ty_scheme = TyScheme of (tyvar list * ty)

    and ty
      = ErrorTy
      | MetaTy of meta
      | VarTy of tyvar
      | ConTy of (ty list * tycon)
      | FunTy of ty * ty
      | TupleTy of ty list

    and meta = MVar of {
            stamp : Stamp.t,            (* unique stamp *)
            info : meta_info ref
          }

    and meta_info
      = UNIV of {
            depth : int,                (* lambda nesting depth *)
            cls : ty_class,             (* type-class constraint *)
            eq : bool                   (* true for equality type variables *)
          }
      | INSTANCE of ty

    and tyvar = TVar of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the varable name *)
            eq : bool,                  (* true for equality-type variables *)
            cls : ty_class              (* type class; this field is `Any` except for
                                         * the type schemes for overloaded variables.
                                         *)
          }

    and tycon = Tyc of {
            stamp : Stamp.t,            (* unique stamp *)
            name : string,              (* the type name *)
            params : tyvar list,        (* type parameters *)
            props : PropList.holder,
            def : tycon_def             (* definition of tyc *)
          }

    and tycon_def
      = AbsTyc of {
            span : int                  (* number of distinct values; ~1 => unbounded *)
          }
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
