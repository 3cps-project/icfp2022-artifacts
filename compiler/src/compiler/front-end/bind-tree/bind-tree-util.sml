(* bind-tree-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure BindTreeUtil : sig

    val qidToString : ('a -> string) -> 'a BindTree.qualid -> string
    val tyToString : BindTree.ty -> string
    val patToString : BindTree.pat -> string

  end = struct

    structure B = BindTree

    fun qidToString idToS (path, id) =
          String.concatWith "."
            (List.foldr (fn (id, ids) => B.StrId.toString id :: ids) [idToS id] path)

    val qidToS = qidToString

    fun tyToString ty = (case ty
           of B.MarkTy{tree, ...} => tyToString tree
            | B.NamedTy([], tyc) => qidToS B.TycId.toString tyc
            | B.NamedTy([ty], tyc) => concat[tyToString ty, " ", qidToS B.TycId.toString tyc]
            | B.NamedTy(tys, tyc) => concat[
                  "(", String.concatWithMap "," tyToString tys, ") ", qidToS B.TycId.toString tyc
                ]
            | B.VarTy tv => B.TyVar.toString tv
            | B.TupleTy tys => String.concatWithMap " * " tyToString tys
            | B.FunTy(ty1, ty2) => (case ty1
                 of B.FunTy _ => concat["(", tyToString ty1, ") -> ", tyToString ty2]
                  | _ => concat[tyToString ty1, " -> ", tyToString ty2]
                (* end case *))
            | B.ErrorTy => "<error-ty>"
          (* end case *))

    fun patToString pat = (case pat
           of B.MarkPat{tree, ...} => patToString tree
            | B.ConAppPat(dc, p) => let
                fun paren () = concat[qidToS B.ConId.nameOf dc, "(", patToString p, ")"]
                in
                  case p
                   of B.ConAppPat _ => paren()
                    | B.ConsPat _ => paren()
                    | _ => concat[qidToS B.ConId.nameOf dc, " ", patToString p]
                  (* end case *)
                end
            | B.ConsPat(p1, p2) => (case p1
                 of B.ConsPat _ => concat["(", patToString p1, ") :: ", patToString p2]
                  | _ => concat[patToString p1, " :: ", patToString p2]
                (* end case *))
            | B.TuplePat ps => concat["(", String.concatWithMap ", " patToString ps, ")"]
            | B.ListPat ps => concat["[", String.concatWithMap ", " patToString ps, "]"]
            | B.WildPat => "_"
            | B.ConPat dc => qidToS B.ConId.nameOf dc
            | B.VarPat x => B.VarId.nameOf x
            | B.AsPat(p1, p2) => concat["(", patToString p1, " as ", patToString p2, ")"]
            | B.ConstPat lit => Literal.toString lit
            | B.ConstraintPat(p, ty) => concat["(", patToString p, " : ", tyToString ty, ")"]
            | B.ErrorPat => "<error-pat>"
          (* end case *))

  end
