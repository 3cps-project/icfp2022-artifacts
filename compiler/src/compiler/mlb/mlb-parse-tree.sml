(* mlb-parse-tree.sml
 *
 * COPYRIGHT (c) 2021 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *
 * Parse-tree representation of MLB files.
 *)

structure MLBParseTree =
  struct

  (* a term marked with a source-map span *)
    type 'a mark = {span : Error.span, tree : 'a}

  (* identifiers and file names *)
    type id = Atom.atom mark

  (* annotations *)
    type ann = string mark

    datatype bas_exp
      = MarkBasExp of bas_exp mark
      | DecBasExp of bas_dec                    (* basic *)
      | IdBasExp of id                          (* basis identifier *)
      | LetBasExp of (bas_dec * bas_exp)        (* let declaration *)

    and bas_dec
      = MarkBasDec of bas_dec mark
      | BasisBasDec of bas_bind			(* basis *)
      | LocalBasDec of bas_dec * bas_dec        (* local *)
      | OpenBasDec of id list                   (* open n >= 1 *)
      | StructureBasDec of mod_bind             (* basis structure binding *)
      | SignatureBasDec of mod_bind             (* basis signature binding *)
      | FunctorBasDec of mod_bind               (* basis functor binding *)
      | SeqBasDec of bas_dec list               (* sequences *)
      | PathBasDec of string                    (* import ML basis or source *)
      | AnnBasDec of ann list * bas_dec     	(* annotation *)

  (* binds bases *)
    and bas_bind
      = MarkBasBind of bas_bind mark
      | BindBasBind of (id * bas_exp) list

  (* binds structures, signatures and functors *)
    and mod_bind
      = MarkModBind of mod_bind mark
      | BindModBind of (id * id) list

    type mlb = bas_dec

  end (* MLBParseTree *)
