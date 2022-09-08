
(* This file contains some common definitions used throughout the proofs.
 *)

Require Import coqutil.Decidable coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.SortedList.
Require Import Lia.

(* A "decidable" type *)

Module Type DEC.
  Parameter t : Set.
  Parameter eq : t -> t -> bool. 
  Parameter dec : Decidable.EqDecider eq.

  Parameter ltb : t -> t -> bool.
  Parameter ltb_antirefl : forall k, ltb k k = false.
  Parameter ltb_trans : forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true.
  Parameter ltb_total : forall k1 k2, ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2.

  Parameter map : forall (T : Type), map.map t T.
  Parameter map_ok : forall (T : Type), map.ok (map T).

End DEC.


(* A "finite" type.
 *)

Module Type FIN (S : DEC).
  Include DEC.
  Parameter alloc : S.t -> t.
End FIN.

(* An "infinite" type.
   This is characterized bya "fresh" function, 
   which allows for always being able to obtain a key that is not in a finite map.
 *)
Module Type INF.
  Include DEC.

  Parameter fresh : forall {T : Type}, map T -> t.
  Parameter freshP : forall {T : Type} (m : map T), map.get m (fresh m) = None.

End INF.

Require Import Arith.

(* Implementation of the "infinite" type using natural numbers
 *)

Module Nat_Inf : INF.
  Definition t := nat.
  Definition eq := Nat.eqb. 
  Definition dec := Decidable.Nat.eqb_spec.
  Definition ltb := Nat.ltb.
  Definition ltb_antirefl := Nat.ltb_irrefl. 
  Definition ltb_trans : forall (k1 k2 k3 : t), ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true. 
  Proof.
    intros k1 k2 k3.
    repeat rewrite Nat.ltb_lt. 
    apply Nat.lt_trans.
  Qed.
  Definition ltb_total : forall (k1 k2 : t), ltb k1 k2 = false -> ltb k2 k1 = false -> k1 = k2.
  Proof. 
    intros. 
    rewrite Nat.ltb_ge in *.
    apply Nat.le_antisymm; trivial.
  Qed.    

  Local Instance string_strict_order: @SortedList.parameters.strict_order _ ltb
    := { ltb_antirefl := ltb_antirefl
         ; ltb_trans := ltb_trans
         ; ltb_total := ltb_total }.
  Definition Build_parameters T := SortedList.parameters.Build_parameters t T ltb.
  Definition map T := SortedList.map (Build_parameters T) string_strict_order.
  Definition map_ok T : @Interface.map.ok t T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.


  (* Freshness for maps on natural numbers.
     The maximum of all elements, plus one, in a map is not in the map.
  *)
  Definition fresh {T : Type} (m : map T) : t := 
    (map.fold (fun max key (_ : T) => Nat.max max (key + 1)) 0 m).

  Definition freshP_helper : forall {T : Type} (m : map T) (n : nat), 
      (forall k v, map.get m k = Some v -> k < n) ->
      map.get m n = None.
  Proof.
    intros.

    intros.
    specialize (H n).
    remember (map.get m n).
    destruct o; eauto.
    clear Heqo.
    exfalso.
    specialize (H v eq_refl).
    Lia.lia.
  Qed. 

  (* Freshness has the property we desire *)
  Definition freshP : forall {T : Type} (m : map T), map.get m (fresh m) = None.

    intros T m.
    apply freshP_helper.
    intros.
    revert H.
    unfold fresh.
    eapply map.fold_spec.
    - rewrite map.get_empty; eauto; congruence.
    - intros.
      case (Nat.eq_dec k k0);
      intro eq; subst. 
      + unfold lt in *.
        rewrite <- Nat.le_max_r; auto.
        Lia.lia.
      + rewrite map.get_put_diff in H1; auto.
        specialize (H0 H1).
        unfold lt in *.
        rewrite <- Nat.le_max_l; auto.
        Unshelve. 
        exact (map_ok T). 
Qed.

End Nat_Inf.

(* Some utility definitions and lemmas on list types *)
Definition listAll {T : Type} (P : T -> Prop) l : Prop := 
  let fix loop l := 
      match l with
      | nil => True
      | cons e l' => P e /\ loop l'
      end
  in loop l
.

Definition listExists {T : Type} (P : T -> Prop) l : Prop := 
  let fix loop l := 
      match l with
      | nil => False
      | cons e l' => P e \/ loop l'
      end
  in loop l
.

Definition eq_list {a : Type} (eq : a -> a -> bool) :=
  let fix eq_list' (lst1 : list a) (lst2 : list a) :=
      match lst1, lst2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | cons a1 rest1, cons a2 rest2 => andb (eq a1 a2) (eq_list' rest1 rest2)
  end in eq_list' .

Lemma eq_list_same : forall {T : Type} eq lst, (forall a : T, eq a a = true) -> eq_list eq lst lst = true.
Proof.
  intros T eq l H.
  induction l; simpl; trivial. 
  rewrite H; simpl; trivial.
Qed.

Lemma eq_list_same' : forall {T : Type} (eq : T -> T -> bool) lst, listAll (fun a => eq a a = true) lst -> eq_list eq lst lst = true.
Proof.
  intros T eq l H.
  induction l; simpl; trivial.
  simpl in H; destruct H.
  rewrite H; simpl; apply IHl; trivial.
Qed.

Lemma listAll_universal : forall {T : Type} (P : T -> Prop) lst, (forall e, P e) -> listAll (fun e => P e) lst.
Proof.
  intros T P l H.
  induction l; simpl; trivial.
  - constructor; trivial.
Qed.

Definition option_bind {A B : Type} (f : A -> option B) (o : option A) : option B :=
  match o with
  | Some a => f a
  | None => None
  end.

(* Utility definitions for selecting elements out of a list *)
Fixpoint nth_opt {T : Type} (n:nat) (l:list T) {struct l} : option T :=
  match n, l with
  | O, cons x _ => Some x
  | O, nil => None
  | S _, nil => None
  | S m, cons _ rst => nth_opt m rst
  end.

Definition select_idxs {A : Type} (lst : list A) (idxs : list nat) : option (list A) :=
  let lp i acc :=
      option_bind (fun acc => option_bind (fun lst_i => Some (cons lst_i acc)) (nth_opt i lst)) acc in
  List.fold_right lp (Some nil) idxs.

(* A lemma for decidable predicates *)
Lemma BoolSpec_implication: forall P Q R S : Prop, forall b, (Q -> P) -> (S -> R) -> BoolSpec Q S b -> BoolSpec P R b.
  intros.
  destruct H1; try apply BoolSpecT; try apply BoolSpecF.
  - apply H; trivial.
  - apply H0; trivial.
Qed.

