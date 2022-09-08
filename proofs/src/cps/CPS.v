
(* This file contains the CPS data structure 
 *)

Require Import common.Common.
Require Import common.Util.

Require Import coqutil.Map.SortedList.
Require Import Coq.Strings.String.
Require Import coqutil.Datatypes.String.

(* The type of "user" variables *)
Module Var : DEC.
  Definition t := string.
  Definition eq := String.eqb. 
  Definition dec := Decidable.String.eqb_spec.

  Definition ltb := String.ltb.
  Definition ltb_antirefl := String.ltb_antirefl.
  Definition ltb_trans := String.ltb_trans.
  Definition ltb_total := String.ltb_total.

  Local Instance string_strict_order: @SortedList.parameters.strict_order _ String.ltb
    := { ltb_antirefl := String.ltb_antirefl
         ; ltb_trans := String.ltb_trans
         ; ltb_total := String.ltb_total }.
  Definition Build_parameters T := SortedList.parameters.Build_parameters String.string T String.ltb.
  Definition map T := SortedList.map (Build_parameters T) string_strict_order.
  Definition map_ok T : @Interface.map.ok String.string T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.
End Var.

Definition var := Var.t.

(* The type of "continuation" variables *)
Module VarK : DEC.
  Definition t := string.
  Definition eq := String.eqb. 
  Definition dec := Decidable.String.eqb_spec.

  Definition ltb := String.ltb.
  Definition ltb_antirefl := String.ltb_antirefl.
  Definition ltb_trans := String.ltb_trans.
  Definition ltb_total := String.ltb_total.

  Local Instance string_strict_order: @SortedList.parameters.strict_order _ String.ltb
    := { ltb_antirefl := String.ltb_antirefl
         ; ltb_trans := String.ltb_trans
         ; ltb_total := String.ltb_total }.
  Definition Build_parameters T := SortedList.parameters.Build_parameters String.string T String.ltb.
  Definition map T := SortedList.map (Build_parameters T) string_strict_order.
  Definition map_ok T : @Interface.map.ok String.string T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.
End VarK.

Definition varK := VarK.t.

(* A CPS term is either a call or a continuation call (callK) 
   A user atom is either a variable or a user lambda, the latter which consists 
   of a user variable parameter, a list of continuation variable parameters, and a body.
   A continuation atom is either a continuation variable or a continuation lambda,
   the latter which consists of a user variable parameter and a body.
 *)
Inductive term : Set :=
| Call : atom -> atom -> list atomK -> term (* call f arg q1 ... qn *)
| CallK : atomK -> atom -> term (* callK q arg *)
with atom : Set :=
| Var : var -> atom (* x *)
| Lam : var -> list varK -> term -> atom (* lambda x k1 ... kn . body *)
with atomK : Set :=
| VarK : varK -> atomK (* k *)
| LamK : var -> term -> atomK (* cont x . body *)
.

(* The mutual induction scheme on the CPS datatypes. *)
Section CPSInduct.
Context {P_term : term -> Prop} 
        {P_atom : atom -> Prop} 
        {P_atomK : atomK -> Prop}
        {IHCall : forall f arg qs, P_atom f -> P_atom arg -> listAll P_atomK qs -> P_term (Call f arg qs)} (* (List.fold_right (fun q => and (P_atomK q)) True qs) -> P_term (Call f arg qs)} *)
        {IHCallK : forall q arg, P_atomK q -> P_atom arg -> P_term (CallK q arg)}
        {IHVar : forall x, P_atom (Var x)}
        {IHLam : forall x ks body, (P_term body) -> P_atom (Lam x ks body)}
        {IHVarK : forall k, P_atomK (VarK k)}
        {IHLamK : forall x body, (P_term body) -> P_atomK (LamK x body)}
.

Fixpoint term_ind' (e : term) {struct e} : P_term e :=
  match e with
  | Call f arg qs => let
      fix loop (qs : list atomK) : listAll P_atomK qs :=
      match qs return listAll P_atomK qs with
      | nil => I
      | cons q qs => conj (atomK_ind' q) (loop qs) 
      end 
    in IHCall f arg qs (atom_ind' f) (atom_ind' arg) (loop qs)
  | CallK q arg => IHCallK q arg (atomK_ind' q) (atom_ind' arg) 
  end
with atom_ind' (ae : atom) {struct ae} : P_atom ae :=
       match ae with
       | Var x => IHVar x
       | Lam x ks body => IHLam x ks body (term_ind' body)
       end
with atomK_ind' (q : atomK) {struct q} : P_atomK q :=
       match q with
       | VarK k => IHVarK k
       | LamK x body => IHLamK x body (term_ind' body)
       end
.

End CPSInduct.

Combined Scheme cps_ind
         from term_ind', atom_ind', atomK_ind'.

(* Boolean-valued equality on the CPS datatypes, along with associated lemmas. *)
Fixpoint eq_term (t1 : term) (t2 : term) :=
  match t1, t2 with
  | Call f1 arg1 qs1, Call f2 arg2 qs2 =>
    andb (andb (eq_atom f1 f2) (eq_atom arg1 arg2)) (eq_list eq_atomK qs1 qs2)
  | Call _ _ _, _ => false
  | _, Call _ _ _ => false
  | CallK argK1 arg1, CallK argK2 arg2 =>
      andb (eq_atomK argK1 argK2) (eq_atom arg1 arg2)
  end
with eq_atom (ae1 : atom) (ae2 : atom) :=
       match ae1, ae2 with
       | Var x1, Var x2 => Var.eq x1 x2
       | Var _, _ => false
       | _, Var _ => false
       | Lam x1 ks1 body1, Lam x2 ks2 body2 =>
         andb (Var.eq x1 x2) (andb (eq_list VarK.eq ks1 ks2) (eq_term body1 body2))
       end
with eq_atomK (q1 : atomK) (q2 : atomK) :=
       match q1, q2 with
       | VarK k1, VarK k2 => VarK.eq k1 k2
       | VarK _, _ => false
       | _, VarK _ => false
       | LamK x1 body1, LamK x2 body2 =>
         andb (Var.eq x1 x2) (eq_term body1 body2)
       end.

Ltac lazy_trivial none := trivial.
Ltac crush := crush_param lazy_trivial tt.

Lemma eq_cps_same : (forall e : term, eq_term e e = true) /\ (forall ae : atom, eq_atom ae ae = true) /\ (forall q : atomK, eq_atomK q q = true).
Proof.
  apply cps_ind; crush; simpl; crush;
    try rewrite eq_list_same'; simpl; crush;
    try (rewrite H; rewrite H0; simpl; crush);
    try (destruct (Var.dec x x); crush);
    try (destruct (VarK.dec k k); crush);
    try (destruct (VarK.dec a a); crush);
    try (apply listAll_universal; destruct (VarK.dec k k));
    try (apply listAll_universal; crush; destruct (VarK.dec e e); crush). 
Qed.

Lemma eq_term_same : forall t, eq_term t t = true.
Proof. 
  destruct eq_cps_same; crush.
Qed.

Lemma eq_atom_same : forall t, eq_atom t t = true.
Proof. 
  destruct eq_cps_same; crush.
Qed.

Lemma eq_atomK_same : forall t, eq_atomK t t = true.
Proof. 
  destruct eq_cps_same; crush.
Qed.

Theorem listAll_BoolSpec: forall qs qs', listAll (fun q : atomK => forall y : atomK, BoolSpec (q = y) (q <> y) (eq_atomK q y)) qs -> BoolSpec (qs = qs') (qs <> qs') (eq_list eq_atomK qs qs').
  induction qs; crush; case qs'; simpl; crush; (try apply BoolSpecT; crush); (try apply BoolSpecF; crush).
  destruct H.
  destruct (H a0); simpl; crush; (try apply BoolSpecF; crush).
  specialize (IHqs l H0).
  eapply BoolSpec_implication; try (exact IHqs); crush.
Qed.

Theorem eq_list_not_same: forall {A} eq (dec : forall x y : A, BoolSpec (x = y) (x <> y) (eq x y)) l l', 
    l <> l' -> eq_list eq l l' = false.
  intros A eq dec l. 
  induction l; intro l'; case l'; crush.
  simpl; crush.
  case (dec a a0); simpl; crush.
  apply IHl; crush.
Qed.

Theorem list_VarK_dec : forall (l l' : list VarK.t), l = l' \/ l <> l'.
  intro l; induction l; intro l'; case l'; crush.
  - apply or_introl; crush.
  - apply or_intror; crush.
  - destruct (IHl l'); crush.
    + apply or_intror; crush.
    + apply or_intror; crush.
  - destruct (IHl l0); crush.
    + case (VarK.dec a t); crush.
      ++ apply or_introl; crush.
      ++ apply or_intror; crush.
    + apply or_intror; crush.
Qed.

(* Decidable equality exists for the CPS datatypes *)
Theorem cps_dec : Decidable.EqDecider eq_term /\ Decidable.EqDecider eq_atom /\ Decidable.EqDecider eq_atomK.
Proof.
  apply cps_ind; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    + destruct (H a); simpl; crush; try (simpl; apply BoolSpecF; crush).
      destruct (H0 a0); simpl; crush; try (simpl; apply BoolSpecF; crush).
      eapply BoolSpec_implication; try apply listAll_BoolSpec; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    + destruct (H a); simpl; crush; try (simpl; apply BoolSpecF; crush).
      destruct (H0 a0); simpl; crush; try (simpl; apply BoolSpecF; crush).
      apply BoolSpecT; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    destruct (Var.dec x v); simpl; crush; try apply BoolSpecF; try apply BoolSpecT; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    destruct (Var.dec x v); simpl; crush; try apply BoolSpecF; crush.
    assert (ks = l \/ ks <> l).
    + apply list_VarK_dec.
    + destruct H0; crush. 
      -- assert (eq_list VarK.eq l l = true) by (apply eq_list_same; crush; destruct (VarK.dec a a); crush).
         rewrite H0; simpl.
         eapply BoolSpec_implication; try (exact (H t)); crush.
      -- rewrite (eq_list_not_same VarK.eq VarK.dec ks l); crush; simpl.
         apply BoolSpecF; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    destruct (VarK.dec k v); simpl; crush; try apply BoolSpecF; try apply BoolSpecT; crush.
  - case y; crush; simpl; crush; try apply BoolSpecF; crush.
    destruct (Var.dec x v); simpl; crush; try apply BoolSpecF; crush.
    eapply BoolSpec_implication; try (exact (H t)); crush.
Qed.

Theorem term_dec : forall (t1 t2 : term), BoolSpec (t1 = t2) (t1 <> t2) (eq_term t1 t2).
Proof.
  destruct cps_dec; crush.
Qed.

Theorem atom_dec : forall (a1 a2 : atom), BoolSpec (a1 = a2) (a1 <> a2) (eq_atom a1 a2).
Proof.
  destruct cps_dec; crush.
Qed.

Theorem atomK_dec : forall (q1 q2 : atomK), BoolSpec (q1 = q2) (q1 <> q2) (eq_atomK q1 q2).
Proof.
  destruct cps_dec; crush.
Qed.


(* The following contains the definition of a boolean-valued less-than (<) operator on the CPS datatypes.
   We need this to define maps over CPS terms
 *)
Section Inner.
  Context {A : Type}.
  Context (ltb : A -> A -> bool).
  Context (eqb : A -> A -> bool).

  (* less-than extended lexicographically to lists *)
  Fixpoint list_ltb (ls1 ls2 : list A) :=
    match ls1 with
    | nil => match ls2 with
             | nil => false
             | cons _ _ => true
             end
    | cons l1 ls1 =>
      match ls2 with
      | nil => false
      | cons l2 ls2 => orb (ltb l1 l2)
                           (andb (eqb l1 l2) (list_ltb ls1 ls2))
      end
    end.

  Fixpoint list_eq (ls1 ls2 : list A) :=
    match ls1 with
    | nil => match ls2 with
             | nil => true
             | cons _ _ => false
             end
    | cons l1 ls1 =>
      match ls2 with
      | nil => false
      | cons l2 ls2 => (andb (eqb l1 l2) (list_eq ls1 ls2))
      end
    end.

  Theorem list_eq_dec : forall a b : list A,
      (forall a b, BoolSpec (a = b) (a <> b) (eqb a b)) -> BoolSpec (a = b) (a <> b) (list_eq a b).
  Proof. 
    induction a.
    - intro b; case b; simpl; crush.
      + apply BoolSpecT; crush.
      + apply BoolSpecF; crush.
    - intros; case b; simpl; crush; try (apply BoolSpecF; crush; fail).
      specialize (IHa l H).
      specialize (H a a1).
      destruct H; destruct IHa; simpl; crush; 
        try (apply BoolSpecF; crush; fail);
        try (apply BoolSpecT; crush; fail).
  Qed.

End Inner.

(* The actual less-than definition. *)
Fixpoint term_ltb t1 t2 : bool :=
  match t1 with
  | Call f1 arg1 qs1 => 
    match t2 with
    | Call f2 arg2 qs2 => 
      orb (atom_ltb f1 f2) 
          (andb (eq_atom f1 f2)
                (orb (atom_ltb arg1 arg2)
                     (andb (eq_atom arg1 arg2)
                           (list_ltb atomK_ltb eq_atomK qs1 qs2))))
    | CallK _ _ => true
    end
  | CallK q1 arg1 => 
    match t2 with
    | Call _ _ _ => false
    | CallK q2 arg2 => 
      orb (atomK_ltb q1 q2)
          (andb (eq_atomK q1 q2)
                (atom_ltb arg1 arg2))
    end
  end
with atom_ltb a1 a2 : bool := 
       match a1 with
       | Var x1 => 
         match a2 with
         | Var x2 => Var.ltb x1 x2
         | Lam _ _ _ => true
         end
       | Lam x1 ks1 body1 => 
         match a2 with
         | Var _ => false
         | Lam x2 ks2 body2 => 
           orb (Var.ltb x1 x2)
               (andb (Var.eq x1 x2)
                     (orb (list_ltb VarK.ltb VarK.eq ks1 ks2)
                          (andb (list_eq VarK.eq ks1 ks2)
                                (term_ltb body1 body2))))
         end
           
       end
with atomK_ltb aK1 aK2 : bool := 
       match aK1 with
       | VarK k1 => 
         match aK2 with
         | VarK k2 => VarK.ltb k1 k2
         | LamK _ _ => true
         end
       | LamK x1 body1 => 
         match aK2 with
         | VarK _ => false
         | LamK x2 body2 => 
           orb (Var.ltb x1 x2)
               (andb (Var.eq x1 x2)
                     (term_ltb body1 body2))
         end
       end.

(* The following are the needed proofs about the less-than function: anti-reflexivity, transitivity, and anti-symmetry *)
Definition cps_ltb_antirefl : (forall k, term_ltb k k = false) /\ (forall a, atom_ltb a a = false) /\ (forall aK, atomK_ltb aK aK = false). 
Proof.
  apply cps_ind; crush; repeat (simpl; crush).
  - rewrite H; rewrite H0; crush; simpl in *. 
    revert H1; induction qs; crush; simpl in *; 
    (repeat rewrite eq_atom_same in *); simpl in *; crush.
    rewrite H1; rewrite eq_atomK_same; simpl in *.
    apply IHqs.
    crush.
  - rewrite H; crush.
    rewrite eq_atomK_same; crush.
  - apply Var.ltb_antirefl.
  - rewrite Var.ltb_antirefl; destruct (Var.dec x x); simpl; crush. 
    rewrite (eq_list_same VarK.eq). 
    + rewrite H.
      induction ks; simpl in *; crush.
      rewrite (VarK.ltb_antirefl a); simpl; crush.
      destruct (VarK.dec a a); crush.
    + intro k; destruct (VarK.dec k k); crush.
  - rewrite VarK.ltb_antirefl; crush.
  - rewrite Var.ltb_antirefl; crush.
    rewrite H; rewrite Bool.andb_comm; simpl in *; crush.
Qed.

Lemma ltb_lex_trans : forall {A B : Type} (ltb1 : A -> A -> bool) (ltb2 : B -> B -> bool) eqb1,
    (forall a b, BoolSpec (a = b) (a <> b) (eqb1 a b)) ->
    (forall a1 a2 a3 b1 b2 b3, 
        (ltb1 a1 a2 = true -> ltb1 a2 a3 = true -> ltb1 a1 a3 = true) ->
        (ltb2 b1 b2 = true -> ltb2 b2 b3 = true -> ltb2 b1 b3 = true) ->
        orb (ltb1 a1 a2) (andb (eqb1 a1 a2) (ltb2 b1 b2)) = true -> 
        orb (ltb1 a2 a3) (andb (eqb1 a2 a3) (ltb2 b2 b3)) = true -> 
        orb (ltb1 a1 a3) (andb (eqb1 a1 a3) (ltb2 b1 b3)) = true).
Proof. 
  intros.
  revert H0 H1 H2 H3.
  destruct (H a1 a2); subst;
  destruct (H a2 a3); subst;
  try (destruct (H a1 a3); subst); simpl in *; crush;
    revert H0 H1 H2 H3;
  case (ltb1 a3 a3);
  case (ltb2 b1 b2);
  case (ltb2 b2 b3); simpl in *; crush; try (apply H1; crush); try (apply H3; crush); crush;
  try (apply H2; rewrite Bool.orb_comm in H4; rewrite Bool.orb_comm in H5; simpl in *; crush; fail); 
  rewrite Bool.orb_comm in *; simpl in *; crush;
    try (apply H3; crush).
Qed.


Lemma list_ltb_trans : forall {A} (ltb eqb : A -> A -> bool) (x y z : list A),
    (forall a b, BoolSpec (a = b) (a <> b) (eqb a b)) ->
    (forall k1 k2 k3, ltb k1 k2 = true -> ltb k2 k3 = true -> ltb k1 k3 = true) ->
    list_ltb ltb eqb x y = true -> 
    list_ltb ltb eqb y z = true -> 
    list_ltb ltb eqb x z = true.
Proof.
  intros A ltb eqb x y z eqb_dec ltb_trans.
  revert y z.
  induction x;
  intros y z; simpl in *;
  case y; simpl in *;
  case z; simpl in *; crush.
  apply (ltb_lex_trans ltb (list_ltb ltb eqb) eqb eqb_dec a a1 a0 x l0 l); crush.  
  - eapply ltb_trans; crush.
  - eapply IHx; crush.
Qed.

Definition cps_ltb_trans : (forall k1 k2 k3, term_ltb k1 k2 = true -> term_ltb k2 k3 = true -> term_ltb k1 k3 = true) /\ (forall k1 k2 k3, atom_ltb k1 k2 = true -> atom_ltb k2 k3 = true -> atom_ltb k1 k3 = true) /\ (forall k1 k2 k3, atomK_ltb k1 k2 = true -> atomK_ltb k2 k3 = true -> atomK_ltb k1 k3 = true).
Proof.
  apply cps_ind.
  - intros f arg qs.
    intros H0 H1 H2.
    intros k2 k3.
    case k2; case k3; crush; simpl in *; crush.
    specialize (H0 a1 a).
    specialize (H1 a2 a0).
    revert H H0 H1 H3.
    intros. 
    destruct (Bool.orb_prop (atom_ltb f a1)
                            (eq_atom f a1 && (atom_ltb arg a2 || eq_atom arg a2 && list_ltb atomK_ltb eq_atomK qs l0)) H); clear H;
    destruct (Bool.orb_prop (atom_ltb a1 a) 
                            (eq_atom a1 a && (atom_ltb a2 a0 || eq_atom a2 a0 && list_ltb atomK_ltb eq_atomK l0 l)) H3); clear H3;
    try (rewrite H4 in * ); try (rewrite H5 in * ).
    + rewrite H0 in *; crush.
    + destruct (andb_prop (eq_atom a1 a) (atom_ltb a2 a0 || eq_atom a2 a0 && list_ltb atomK_ltb eq_atomK l0 l) H); clear H.
      assert (a1 = a) by (revert H3; case (atom_dec a1 a); crush); subst.
      eapply Bool.orb_true_intro; apply or_introl; crush.
    + destruct (andb_prop (eq_atom f a1) (atom_ltb arg a2 || eq_atom arg a2 && list_ltb atomK_ltb eq_atomK qs l0) H4); clear H4.
      assert (f = a1) by (revert H3; case (atom_dec f a1); crush); subst.
      eapply Bool.orb_true_intro; apply or_introl; crush.
    + destruct (andb_prop (eq_atom f a1) (atom_ltb arg a2 || eq_atom arg a2 && list_ltb atomK_ltb eq_atomK qs l0) H4); clear H4.
      destruct (andb_prop (eq_atom a1 a) (atom_ltb a2 a0 || eq_atom a2 a0 && list_ltb atomK_ltb eq_atomK l0 l) H); clear H.
      assert (f = a1) by (revert H3; case (atom_dec f a1); crush); subst.
      assert (a1 = a) by (revert H4; case (atom_dec a1 a); crush); subst.
      eapply Bool.orb_true_intro; apply or_intror; crush.
      rewrite Bool.andb_true_iff; crush.
      ++ destruct (Bool.orb_prop (atom_ltb arg a2) (eq_atom arg a2 && list_ltb atomK_ltb eq_atomK qs l0) H5); clear H5;
         destruct (Bool.orb_prop (atom_ltb a2 a0) (eq_atom a2 a0 && list_ltb atomK_ltb eq_atomK l0 l) H6); clear H6.
         +++ eapply Bool.orb_true_intro; apply or_introl; apply H1; crush.
         +++ destruct (andb_prop (eq_atom a2 a0) (list_ltb atomK_ltb eq_atomK l0 l) H5); clear H5.
             assert (a2 = a0) by (revert H6; case (atom_dec a2 a0); crush); subst.
             eapply Bool.orb_true_intro; apply or_introl; crush.
         +++ destruct (andb_prop (eq_atom arg a2) (list_ltb atomK_ltb eq_atomK qs l0) H); clear H.
             assert (arg = a2) by (revert H6; case (atom_dec arg a2); crush); subst.
             eapply Bool.orb_true_intro; apply or_introl; crush.
         +++ eapply Bool.orb_true_intro; apply or_intror; crush.
             destruct (andb_prop (eq_atom a2 a0) (list_ltb atomK_ltb eq_atomK l0 l) H5); clear H5.
             destruct (andb_prop (eq_atom arg a2) (list_ltb atomK_ltb eq_atomK qs l0) H); clear H.
             assert (a2 = a0) by (revert H6; case (atom_dec a2 a0); crush); subst.
             assert (arg = a0) by (revert H5; case (atom_dec arg a0); crush); subst. 
             rewrite Bool.andb_true_iff; crush.
             revert l0 l H7 H8.
             induction qs.
             ++++ intros l0 l. case l0; case l; crush.
             ++++ intros l0 l; case l0; case l; simpl in *; crush.
                  specialize (IHqs H2 l2 l1).
                  destruct (Bool.orb_prop (atomK_ltb a3 a2) (eq_atomK a3 a2 && list_ltb atomK_ltb eq_atomK l2 l1) H7); clear H7;
                  destruct (Bool.orb_prop (atomK_ltb a1 a3) (eq_atomK a1 a3 && list_ltb atomK_ltb eq_atomK qs l2) H8); clear H8.
                  -- eapply Bool.orb_true_intro; apply or_introl; crush.
                     apply (H a3 a2); crush.
                  -- eapply Bool.orb_true_intro; apply or_introl; crush.
                     destruct (andb_prop (eq_atomK a1 a3) (list_ltb atomK_ltb eq_atomK qs l2) H7); clear H7.
                     assert (a1 = a3) by (revert H8; case (atomK_dec a1 a3); crush); subst; crush. 
                  -- eapply Bool.orb_true_intro; apply or_introl; crush.
                     destruct (andb_prop (eq_atomK a3 a2) (list_ltb atomK_ltb eq_atomK l2 l1) H9); clear H9.
                     assert (a3 = a2) by (revert H8; case (atomK_dec a3 a2); crush); subst; crush. 
                  -- destruct (andb_prop (eq_atomK a1 a3) (list_ltb atomK_ltb eq_atomK qs l2) H7); clear H7.
                     destruct (andb_prop (eq_atomK a3 a2) (list_ltb atomK_ltb eq_atomK l2 l1) H9); clear H9.
                     eapply Bool.orb_true_intro; apply or_intror; crush.
                     assert (a1 = a3) by (revert H8; case (atomK_dec a1 a3); crush); subst.
                     assert (a3 = a2) by (revert H7; case (atomK_dec a3 a2); crush); subst. 
                     rewrite Bool.andb_true_iff; crush.
                     apply IHqs; crush.
  - intros. 
    revert H1 H2; case k2; case k3; simpl in *; crush.
    specialize (H a1 a);
    specialize (H0 a2 a0);
    revert H H0 H1 H2.
    eapply ltb_lex_trans; apply atomK_dec.
  - intros. 
    revert H H0.
    case k2; case k3; simpl in *; crush.
    eapply Var.ltb_trans; crush.
  - intros.
    revert H0 H1.
    case k2; case k3; simpl in *; crush.
    specialize (H t0 t).

    destruct (Bool.orb_prop (Var.ltb x v0)
                            (Var.eq x v0 &&
                                    (list_ltb VarK.ltb VarK.eq ks l0 || list_eq VarK.eq ks l0 && term_ltb body t0)) H0); clear H0;

    destruct (Bool.orb_prop (Var.ltb v0 v)
                            (Var.eq v0 v &&
                                    (list_ltb VarK.ltb VarK.eq l0 l || list_eq VarK.eq l0 l && term_ltb t0 t)) H1); clear H1.
    + rewrite (Var.ltb_trans x v0 v); crush.
    + rewrite (Bool.andb_true_iff (Var.eq v0 v) (list_ltb VarK.ltb VarK.eq l0 l || list_eq VarK.eq l0 l && term_ltb t0 t)) in H0; destruct H0.
      assert (v0 = v) by (revert H0; case (Var.dec v0 v); crush); subst.
      eapply Bool.orb_true_intro; apply or_introl; crush.
    + rewrite (Bool.andb_true_iff (Var.eq x v0) 
                                  (list_ltb VarK.ltb VarK.eq ks l0 || list_eq VarK.eq ks l0 && term_ltb body t0)) in H2; destruct H2.
      assert (x = v0) by (revert H1; case (Var.dec x v0); crush); subst.
      eapply Bool.orb_true_intro; apply or_introl; crush.
    + rewrite (Bool.andb_true_iff (Var.eq x v0) 
                                  (list_ltb VarK.ltb VarK.eq ks l0 || list_eq VarK.eq ks l0 && term_ltb body t0)) in H2; destruct H2.
      assert (x = v0) by (revert H1; case (Var.dec x v0); crush); subst.
      rewrite (Bool.andb_true_iff (Var.eq v0 v) (list_ltb VarK.ltb VarK.eq l0 l || list_eq VarK.eq l0 l && term_ltb t0 t)) in H0; destruct H0.
      assert (v0 = v) by (revert H0; case (Var.dec v0 v); crush); subst.
      eapply Bool.orb_true_intro; apply or_intror; crush.
      apply andb_true_intro; crush.
      destruct (Bool.orb_prop (list_ltb VarK.ltb VarK.eq ks l0)
                              (list_eq VarK.eq ks l0 && term_ltb body t0) H2); clear H2;
      destruct (Bool.orb_prop (list_ltb VarK.ltb VarK.eq l0 l) (list_eq VarK.eq l0 l && term_ltb t0 t) H3); clear H3.
      ++ eapply Bool.orb_true_intro; apply or_introl; crush. 
         eapply list_ltb_trans.
         +++ apply VarK.dec.
         +++ apply VarK.ltb_trans.
         +++ apply H4.
         +++ apply H2.
      ++ rewrite (Bool.andb_true_iff (list_eq VarK.eq l0 l) (term_ltb t0 t)) in H2; destruct H2.
         pose proof (list_eq_dec VarK.eq l0 l VarK.dec).
         rewrite H3 in *; inversion H5; crush.
         eapply Bool.orb_true_intro; apply or_introl; crush. 
      ++ rewrite (Bool.andb_true_iff (list_eq VarK.eq ks l0) (term_ltb body t0)) in H4; destruct H4.
         pose proof (list_eq_dec VarK.eq ks l0 VarK.dec).
         rewrite H3 in *; inversion H5; crush.
         eapply Bool.orb_true_intro; apply or_introl; crush. 
      ++ rewrite (Bool.andb_true_iff (list_eq VarK.eq ks l0) (term_ltb body t0)) in H4; destruct H4.
         rewrite (Bool.andb_true_iff (list_eq VarK.eq l0 l) (term_ltb t0 t)) in H2; destruct H2.
         eapply Bool.orb_true_intro; apply or_intror; crush. 
         apply andb_true_intro; crush; try apply H; crush.
         pose proof (list_eq_dec VarK.eq ks l0 VarK.dec).
         rewrite H3 in *; inversion H6; crush.
  - intros.
    revert H H0.
    case k2; case k3; simpl in *; crush.
    eapply VarK.ltb_trans; crush.
  - intros.
    revert H0 H1.
    case k2; case k3; simpl in *; crush.
    specialize (H t0 t).
    eapply ltb_lex_trans; try apply Var.dec; try apply Var.ltb_trans; try apply H; crush.
Qed.

Definition cps_ltb_total : (forall k1 k2, term_ltb k1 k2 = false -> term_ltb k2 k1 = false -> k1 = k2) /\ (forall k1 k2, atom_ltb k1 k2 = false -> atom_ltb k2 k1 = false -> k1 = k2) /\ (forall k1 k2, atomK_ltb k1 k2 = false -> atomK_ltb k2 k1 = false -> k1 = k2). 
Proof.
  apply cps_ind; crush.
  - revert H2 H3; destruct k2; crush; revert H2; revert H3; simpl in *.
    + specialize (H a); specialize (H0 a0).
      revert H H0.
      case (atom_ltb f a); 
      case (atom_ltb a f); 
      case (atom_ltb arg a0); 
      case (atom_ltb a0 arg); simpl in *; crush; rewrite Bool.andb_comm in *; simpl in *;
      try (rewrite H in *; crush; rewrite eq_atom_same in *; crush);
      try (rewrite H0 in *; crush; rewrite eq_atom_same in *; crush).
      simpl in *; rewrite Bool.andb_comm in *; simpl in *.
      f_equal.
      revert l H1 H3 H2.
      induction qs.
      ++ intro l; case l; crush.
         simpl in *; crush.
      ++ intro l; case l; crush; simpl in *; crush.
         destruct (Bool.orb_false_elim (atomK_ltb a2 a1) (eq_atomK a2 a1 && list_ltb atomK_ltb eq_atomK l0 qs) H3).
         destruct (Bool.orb_false_elim (atomK_ltb a1 a2) (eq_atomK a1 a2 && list_ltb atomK_ltb eq_atomK qs l0) H2).
         specialize (H1 a2 H7 H5).
         rewrite H1 in *; crush.
         f_equal; eapply IHqs; crush; rewrite eq_atomK_same in *; simpl in *; crush.
    + crush.
  - revert H1 H2; destruct k2; crush; revert H1 H2; simpl in *.
    + crush.
    + specialize (H a); specialize (H0 a0).
      revert H H0.
      case (atomK_ltb q a);
      case (atomK_ltb a q);
      case (atom_ltb arg a0);
      case (atom_ltb a0 arg); simpl in *; crush; rewrite Bool.andb_comm in *; simpl in *;
      rewrite H in *; crush;
      try (rewrite eq_atomK_same in *; crush; fail). 
      rewrite H0; crush.
  - revert H H0; destruct k2; crush; revert H H0; simpl in *.
    + crush; rewrite (Var.ltb_total x v H H0); trivial.
    + crush.
  - revert H0 H1; destruct k2; crush; revert H0 H1; simpl in *.
    + crush.
    + pose proof (Var.ltb_total x v) as H3; revert H3.
      specialize (H t); revert H.
      intros.
      destruct (Bool.orb_false_elim (Var.ltb x v) (Var.eq x v && (list_ltb VarK.ltb VarK.eq ks l || list_eq VarK.eq ks l && term_ltb body t)) H0); clear H0.
      destruct (Bool.orb_false_elim (Var.ltb v x) (Var.eq v x && (list_ltb VarK.ltb VarK.eq l ks || list_eq VarK.eq l ks && term_ltb t body)) H1); clear H1.
      rewrite (Var.ltb_total x v H2 H0) in *.
      destruct (Var.dec v v); crush; simpl in *; crush.
      destruct (Bool.orb_false_elim (list_ltb VarK.ltb VarK.eq ks l) (list_eq VarK.eq ks l && term_ltb body t) H4); clear H4.
      destruct (Bool.orb_false_elim (list_ltb VarK.ltb VarK.eq l ks) (list_eq VarK.eq l ks && term_ltb t body) H5); clear H5.
      assert (ks = l).
      ++ revert dependent l.
         induction ks.
         +++ intro l; case l; simpl in *; crush. 
         +++ intro l; case l; simpl in *; crush.
             specialize (IHks l0).
             destruct (Bool.orb_false_elim (VarK.ltb a v0) (VarK.eq a v0 && list_ltb VarK.ltb VarK.eq ks l0) H6);
             destruct (Bool.orb_false_elim (VarK.ltb v0 a) (VarK.eq v0 a && list_ltb VarK.ltb VarK.eq l0 ks) H4).
             pose proof (VarK.ltb_total a v0 H5 H10).
             rewrite H12 in *; crush; destruct (VarK.dec v0 v0); simpl in *; crush; f_equal.
             apply IHks; crush.
      ++ rewrite H5 in *.
         destruct (list_eq_dec VarK.eq l l VarK.dec); crush.
         f_equal; apply H; crush.
  - revert H H0; destruct k2; crush; revert H H0; simpl in *.
    + crush. rewrite (VarK.ltb_total k v H H0); crush.
    + crush.
  - revert H0 H1; destruct k2; crush; revert H0 H1; simpl in *.
    + crush.
    + specialize (H t); pose proof (Var.ltb_total x v) as H1; revert H1 H.
      case (Var.ltb x v);
      case (Var.ltb v x);
      case (term_ltb t body);
      case (term_ltb body t); crush; simpl in *; crush; rewrite Bool.andb_comm in *; simpl in *; crush; intuition subst; crush;
      try (destruct (Var.dec v v); crush; fail).
Qed.

Definition term_ltb_antirefl : (forall k, term_ltb k k = false). 
Proof. 
  destruct cps_ltb_antirefl; crush.
Qed.

Definition term_ltb_trans : forall k1 k2 k3, term_ltb k1 k2 = true -> term_ltb k2 k3 = true -> term_ltb k1 k3 = true. 
Proof.
  destruct cps_ltb_trans; apply H; crush.
Qed.

Definition term_ltb_total : forall k1 k2, term_ltb k1 k2 = false -> term_ltb k2 k1 = false -> k1 = k2.
Proof.
  destruct cps_ltb_total; apply H; crush.
Qed.

(* The actual term module for CPS terms *)
Module Term.
  Definition t := term.
  Definition eq := eq_term. 
  Definition dec := term_dec.

  
  Definition ltb := term_ltb.
  Definition ltb_antirefl := term_ltb_antirefl.
  Definition ltb_trans := term_ltb_trans.
  Definition ltb_total := term_ltb_total.

  Local Instance strict_order: @SortedList.parameters.strict_order _ ltb
    := { ltb_antirefl := ltb_antirefl
         ; ltb_trans := ltb_trans
         ; ltb_total := ltb_total }.
  Definition Build_parameters T := SortedList.parameters.Build_parameters term T term_ltb.
  Definition map T := SortedList.map (Build_parameters T) strict_order.
  Definition map_ok T : @Interface.map.ok term T (map T).
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.

End Term.

