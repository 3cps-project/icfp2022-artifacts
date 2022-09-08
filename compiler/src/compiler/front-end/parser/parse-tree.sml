(* parse-tree.sml
 *
 * COPYRIGHT (c) 2007 John Reppy (http://www.cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Parse-tree representation of MinML programs.
 *)

structure ParseTree =
  struct

  (* a term marked with a line number *)
    type 'a mark = {span : Error.span, tree : 'a}

    type qualid = Atom.atom list * Atom.atom    (* qualified ID use occurrence *)

    type tyvar = Atom.atom

  (* top-level declarations *)
    datatype decl
      = MarkDecl of decl mark
      | StructDecl of Atom.atom * str_exp
      | LocalDecl of decl list * decl list
      | TyDecl of tyvar list * Atom.atom * ty
      | DataDecl of (tyvar list * Atom.atom * con_decl list) mark list
      | ExnDecl of con_decl
      | ValueDecl of val_decl

  (* structure expressions *)
    and str_exp
      = MarkStrExp of str_exp mark
      | IdStrExp of qualid
      | DefStrExp of decl list

  (* data-constructor definitions *)
    and con_decl
      = MarkConDecl of con_decl mark
      | ConDecl of Atom.atom * ty option

  (* value declarations *)
    and val_decl
      = MarkVDecl of val_decl mark
      | ValVDecl of pat * exp
      | FunVDecl of funct list

  (* function definitions *)
    and funct
      = MarkFunct of funct mark
      | Funct of (Atom.atom * pat list * ty option * exp) mark list

  (* types *)
    and ty
      = MarkTy of ty mark
      | NamedTy of (ty list * qualid)
      | VarTy of tyvar
      | TupleTy of ty list
      | FunTy of (ty * ty)

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
      | BinaryExp of (exp * Atom.atom * exp)    (* infix binary expressions *)
      | ApplyExp of (exp * exp)                 (* application *)
      | TupleExp of exp list
      | ListExp of exp list                     (* `[` <exp> `,` ... `]` *)
      | SeqExp of exp list                      (* sequence of two or more expressions *)
      | IdExp of qualid                         (* either variable or nullary constant *)
      | ConstExp of Literal.t
      | ConstraintExp of exp * ty               (* type constraint *)

  (* pattern matching rules *)
    and match
      = MarkMatch of match mark
      | CaseMatch of (pat * exp)

    and pat
      = MarkPat of pat mark
      | ConPat of qualid * pat          (* <QID> <pat> *)
      | ConsPat of (pat * pat)          (* infix `::`` pattern *)
      | TuplePat of pat list            (* `(` <pat> `,` ... `)` *)
      | ListPat of pat list             (* `[` <pat> `,` ... `]` *)
      | WildPat                         (* `_` *)
      | IdPat of qualid                 (* <ID> either variable or nullary constant *)
      | AsPat of pat * pat              (* <pat> `as` <pat> (Successor ML layered pats) *)
      | ConstPat of Literal.t
      | ConstraintPat of pat * ty       (* type constraint *)

    type comp_unit = decl list mark

  (* some utility functions *)

    fun spanOfPat (_, MarkPat{span, ...}) = span
      | spanOfPat (span, _) = span

  end
