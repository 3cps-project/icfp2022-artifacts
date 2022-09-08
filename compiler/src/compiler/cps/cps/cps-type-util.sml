(* cps-type-util.sml
 *
 * COPYRIGHT (c) 2020 John Reppy (http://cs.uchicago.edu/~jhr)
 * All rights reserved.
 *)

structure CPSTypeUtil : sig

    val tyToString : CPSTypes.t -> string
    val tysToString : CPSTypes.t list -> string (* for printing type arguments *)
    val ctyToString : CPSTypes.ct -> string
    val tySchemeToString : CPSTypes.ty_scheme -> string

    val applyScheme : CPSTypes.ty_scheme * CPSTypes.t list -> CPSTypes.t

  end = struct

    structure Ty = CPSTypes
    structure TVMap = CPSTyVar.Map

  (* return a string representation of a type (for debugging) *)
    fun tyToString (Ty.VarTy tv) = CPSTyVar.toString tv
      | tyToString (Ty.ConTy([], tyc)) = CPSTyCon.nameOf tyc
      | tyToString (Ty.ConTy(tys, tyc)) = CPSTyCon.nameOf tyc ^ tysToString tys
      | tyToString (Ty.TupleTy[]) = "unit"
      | tyToString (Ty.TupleTy tys) = concat[
            "(* ", String.concatWithMap ", " tyToString tys, ")"
          ]
      | tyToString (Ty.FunTy(tys, ctys)) = concat[
            "(-> ", String.concatWithMap ", " tyToString tys, " / ",
            String.concatWithMap ", " ctyToString ctys, ")"
          ]

    and tysToString tys = concat[
            "<", String.concatWithMap "," tyToString tys, ">"
          ]

    and ctyToString (Ty.ContTy[]) = concat["(cont)"]
      | ctyToString (Ty.ContTy tys) = concat["(cont ", tysToString tys, ")"]

    fun tySchemeToString (Ty.TyScheme (tvars, ty)) = concat[
            "forall", " ", String.concatWithMap " " CPSTyVar.toString tvars, ", ", tyToString ty
        ]

    fun applyScheme (Ty.TyScheme([], ty), []) = ty
      | applyScheme (Ty.TyScheme(tvs, ty), tyArgs) = let
          val subst = ListPair.foldlEq
                (fn (tv, ty, s) => TVMap.insert(s, tv, ty))
                  TVMap.empty (tvs, tyArgs)
          fun apply (Ty.VarTy tv) = (case TVMap.find(subst, tv)
                 of SOME ty => ty
                  | NONE => Ty.VarTy tv
                (* end case *))
            | apply (Ty.ConTy(tyArgs, tyc)) = Ty.ConTy(List.map apply tyArgs, tyc)
            | apply (Ty.TupleTy tys) = Ty.TupleTy(List.map apply tys)
            | apply (Ty.FunTy(tys, ctys)) = Ty.FunTy(List.map apply tys, List.map applyc ctys)
          and applyc (Ty.ContTy tys) = Ty.ContTy(List.map apply tys)
          in
            apply ty
          end
(*+DEBUG*)
handle ex => (
print(concat["applyScheme ([", String.concatWithMap "," CPSTyVar.toString tvs, "] ",
tyToString ty, ", [", String.concatWithMap "," tyToString tyArgs, "])\n"]);
raise ex)
(*-DEBUG*)

  end
