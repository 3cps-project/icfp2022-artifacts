(* ast.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * MinML typed abstract syntax.
 *)

structure AST =
  struct

    datatype ty_scheme = datatype Types.ty_scheme
    datatype ty = datatype Types.ty
    datatype tyvar = datatype Types.tyvar
    datatype dcon = datatype Types.dcon
    type strid = StrId.t
    type var = Var.t

    datatype top_decl
      = StructTopDec of strid * str_exp
      | DConTopDec of dcon                      (* includes exception constructors *)
      | ValTopDec of val_decl

    and str_exp
      = IdStrExp of strid
      | DefStrExp of sign * top_decl list

  (* "signatures" -- this is just a catalog of the exported identifiers from a
   * structure.  It does not correspond to any source-level syntax.
   *)
    and sign = Sign of {
        strs : strid list,      (* exported structures *)
        cons : dcon list,       (* exported constructors (includes exceptions) *)
        vals : var list         (* exported value identifiers *)
      }

    and exp
      = LetExp of val_decl * exp
      | IfExp of exp * exp * exp * ty                   (* ty is result type *)
      | CaseExp of exp * (pat * exp) list * ty          (* ty is result type *)
      | HandleExp of exp * (pat * exp) list * ty        (* ty is result type *)
      | RaiseExp of Error.location * exp * ty           (* ty is result type *)
      | FunExp of (var * exp * ty)                      (* ty is result type *)
      | ApplyExp of exp * exp * ty                      (* ty is result type *)
      | TupleExp of exp list
      | ConstExp of const
      | SeqExp of exp * exp
      | VarExp of var * ty list
      | OverloadExp of overload_var ref                 (* pending overload resolution *)

    and overload_var
      = Unknown of (ty * var list)
      | Instance of var

    and val_decl
      = ValDecl of pat * ty_scheme * exp
      | FunDecl of (var * var list * exp) list

    and pat
      = VarPat of var
      | WildPat of ty
      | ConstPat of const
      | ConPat of dcon * ty list * pat
      | TuplePat of pat list
      | AsPat of var * pat

    and const
      = DConst of dcon * ty list
      | LConst of (Literal.t * ty)

    type comp_unit = top_decl list

  end
