(* bind-tree.sml
 *
 * COPYRIGHT (c) 2020 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * Parse-tree representation with variable bindings for MinML programs.
 *)

structure BindTree =
  struct

  (* a term marked with a line number *)
    type 'a mark = {span : Error.span, tree : 'a}

  (* define the various classes of identifiers *)
    structure StrId = IdentifierFn()    (* structure identifiers *)
    structure TycId = IdentifierFn()    (* type constructor identifiers *)
    structure TyVar = IdentifierFn()    (* type variable identifiers *)
    structure ConId = IdentifierFn()    (* data constructor and exception identifiers *)
    structure VarId = IdentifierFn()    (* variables *)

  (* type aliases *)
    type strid = StrId.t
    type tycon = TycId.t
    type tyvar = TyVar.t
    type conid = ConId.t
    type varid = VarId.t

  (* use occurrence of a value/constructor identifier *)
    datatype val_bind = Var of varid | Con of conid

    type 'a qualid = strid list * 'a    (* qualified ID use occurrence *)

  (* top-level declarations *)
    datatype decl
      = MarkDecl of decl mark
      | StructDecl of strid * sign * str_exp
      | LocalDecl of decl list * decl list
      | TyDecl of tyvar list * tycon * ty
      | DataDecl of (tyvar list * tycon * con_decl list) mark list
      | ExnDecl of con_decl
      | ValueDecl of val_decl

  (* "signatures" -- this is just a catalog of the exported identifiers from a
   * structure.  It does not correspond to any source-level syntax.
   *)
    and sign = Sign of {
        strs : strid list,      (* exported structures *)
        tycs : tycon list,      (* exported type constructors *)
        cons : conid list,      (* exported constructors (includes exceptions) *)
        vals : varid list       (* exported value identifiers *)
      }

  (* structure expressions *)
    and str_exp
      = MarkStrExp of str_exp mark
      | IdStrExp of strid qualid
      | DefStrExp of decl list
      | ErrorStrExp

  (* data-constructor definitions *)
    and con_decl
      = MarkConDecl of con_decl mark
      | ConDecl of conid * ty option

  (* value declarations *)
    and val_decl
      = MarkVDecl of val_decl mark
      | ValVDecl of tyvar list * pat * exp
      | FunVDecl of tyvar list * funct list

  (* function definitions *)
    and funct
      = Funct of (varid * (pat list * ty option * exp) mark list) mark

  (* types *)
    and ty
      = MarkTy of ty mark
      | NamedTy of (ty list * tycon qualid)
      | VarTy of tyvar
      | TupleTy of ty list
      | FunTy of (ty * ty)
      | ErrorTy                                 (* placeholder for unbound things *)

  (* expressions *)
    and exp
      = MarkExp of exp mark
      | LetExp of (val_decl list * exp)
      | IfExp of (exp * exp * exp)
      | FnExp of match list                     (* anonymous function *)
      | CaseExp of (exp * match list)
      | HandleExp of (exp * match list)
      | RaiseExp of exp
      | AndAlsoExp of (exp * exp)
      | OrElseExp of (exp * exp)
      | ApplyExp of (exp * exp)                 (* application *)
      | TupleExp of exp list
      | ListExp of exp list                     (* `[` <exp> `,` ... `]` *)
      | SeqExp of exp list                      (* sequence of two or more expressions *)
      | ConExp of conid qualid                  (* data constructor *)
      | VarExp of varid qualid                  (* variable *)
      | ConstExp of Literal.t
      | ConstraintExp of exp * ty               (* type constraint *)
      | ErrorExp                                (* placeholder for unbound identifiers *)

  (* pattern matching rules *)
    and match
      = MarkMatch of match mark
      | CaseMatch of (pat * exp)

    and pat
      = MarkPat of pat mark
      | ConAppPat of conid qualid * pat         (* <QID> <pat> *)
      | ConsPat of (pat * pat)                  (* infix `::`` pattern *)
      | TuplePat of pat list                    (* `(` <pat> `,` ... `)` *)
      | ListPat of pat list                     (* `[` <pat> `,` ... `]` *)
      | WildPat                                 (* `_` *)
      | ConPat of conid qualid                  (* nullary constant *)
      | VarPat of varid                         (* variable binding *)
      | AsPat of pat * pat                      (* <pat> `as` <pat> *)
      | ConstPat of Literal.t
      | ConstraintPat of pat * ty               (* type constraint *)
      | ErrorPat                                (* placeholder for bad data constructors *)

    type comp_unit = decl list mark

  end
