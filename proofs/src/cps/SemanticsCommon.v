
(* This file contains definition common to both the concrete and abstract semantics. 
   This includes:
   - the definition of extent annotations
   - the definition of freeness of variables and continuation variables in the CPS datatypes
*)

Require Import Ensembles.

Require Import cps.CPS.

Inductive extentMark := ExtentR : extentMark (* Register extent *)
                      | ExtentS : extentMark. (* Stack extent *)
Inductive annotation := Anno : var -> extentMark -> annotation. 
(* the set of annotations is a set of pairs of variables and extent marks *)
Definition annotationSet := Ensemble annotation. 

(* Assume the existence of the initial set of annotations from a CPS term.
   This involves traversing the term, collecting all variables, 
   and packaging them with the extent markings.
   Our simulation result will hold no matter what choice is used, 
   since the initial states of both the concrete and the abstract semantics
   both use the same set.
*)
Parameter initialAnnotationSet : CPS.term -> annotationSet.

(* Freeness over the CPS datatypes. *)
Fixpoint free_term (e : term) (x : var) : Prop :=
  match e with
  | Call f arg qs => free_atom f x \/ free_atom arg x \/ List.fold_right (fun q acc => free_atomK q x \/ acc) False qs
  | CallK q arg  => free_atomK q x \/ free_atom arg x
  end
with free_atom (ae : atom) (x : var) : Prop :=
  match ae with
  | Var y => x = y
  | Lam y ks body => x <> y /\ (free_term body x)
  end
with free_atomK (q : atomK) (x : var) : Prop :=
  match q with
  | VarK k => False
  | LamK y body => x <> y /\ (free_term body x)
  end.

Fixpoint freeK_term (e : term) (k : varK) : Prop :=
  match e with
  | Call f arg qs => freeK_atom f k \/ freeK_atom arg k \/ List.fold_right (fun q acc => freeK_atomK q k \/ acc) False qs
  | CallK q arg  => freeK_atomK q k \/ freeK_atom arg k
  end
with freeK_atom (ae : atom) (k : varK) : Prop :=
  match ae with
  | Var y => False
  | Lam y ks body => (List.fold_right (fun k' acc => k <> k' /\ acc) True ks) /\
                     (freeK_term body k)
  end
with freeK_atomK (q : atomK) (k : varK) : Prop :=
  match q with
  | VarK k' => k = k'
  | LamK y body => freeK_term body k
  end.

