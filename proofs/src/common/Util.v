
(* This file contains some "utility" tactics used throughout the proofs. 
 *)

Ltac cases exp :=
  let casevar := fresh "casevar" in
  let eqnname := fresh "caseeq" in
  remember exp as casevar eqn:eqnname;
  destruct casevar; symmetry in eqnname; clear eqnname.

Ltac case_match :=match goal with
  | [H : context[match ?e with _ => _ end] |- _ ]
    => let e':= fresh in
       let eqnname := fresh in
       remember e as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.
Ltac case_match_goal :=match goal with
  | [ |- context[match ?e with _ => _ end] ]
    => let e':= fresh in
       let eqnname := fresh in
       remember e as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.


Ltac break :=
  repeat match goal with
         | [H: unit|-_]=> destruct H
         | [H: _*_|-_]=> destruct H
         | [H: _/\_|-_]=> destruct H
         | [H: exists x, _|-_]=> destruct H
         | [H : Some _ = Some _ |- _] => inversion H; clear H
         | [H := _ |- _] => unfold H in *; clear H
         end.

Ltac break_goal :=
  repeat match goal with
         | [ |- _ /\ _] => constructor; intros
         | [ |- _ <-> _] => constructor; intros
         end.

Ltac crush_try_hints hints :=
  match hints with
  | ( ?hints' , ?hint) => (try apply hint;
                           try rewrite hint;
                           crush_try_hints hints')
  | tt => trivial
  | ?hint => try apply hint; try rewrite hint
  end.

Ltac crush_param tac hints :=
  repeat (intros;
          break_goal;
          break;
          subst;
          try congruence;
          trivial;
          try eassumption;
          tac ();
          crush_try_hints hints).

Ltac brute_param crush :=
  crush ();
  match goal with
  | [ H : forall (x : ?t), _,  H' : ?t |- _ ] => specialize (H H'); (brute_param crush)
  | [ H : ?t |- exists _ : ?t, _ ] => exists H; (brute_param crush)
  | [ |- _ \/ _ ] => left; (brute_param crush)
  | [ |- _ \/ _ ] => right; (brute_param crush)
  end.

Require Import coqutil.Map.Interface.
Definition map := map.map.

Ltac map_rewrite' crush hints :=
  try rewrite map.get_put_same;
  match goal with
  | [H : _ |- _] => rewrite map.get_put_same in H
  | _ => trivial
  end;
  let rewrite_get_put_diff := rewrite map.get_put_diff; try congruence; trivial in
  let rewrite_get_put_diff_in H := rewrite map.get_put_diff in H; try congruence; trivial in
  try match goal with
      | [H : map.get _ _ = Some _ |- _] => rewrite H
      end;
  try match goal with
      | [H : map.get _ _ = None |- _] => rewrite H
      end;
  try match goal with
      | [H : Some _ = map.get _ _ |- _] => rewrite <- H
      end;
  try match goal with
      | [H : None = map.get _ _ |- _] => rewrite <- H
      end;
  match goal with
  | [H : ?k1 <> ?k2 |- (map.get (map.put _ ?k1 _) ?k2 = _)] => rewrite_get_put_diff
  | [H : ?k2 <> ?k1 |- (map.get (map.put _ ?k2 _) ?k1 = _)] => rewrite_get_put_diff
  | [H : ?k1 <> ?k2 |- (_ = map.get (map.put _ ?k1 _) ?k2)] => rewrite_get_put_diff
  | [H : ?k2 <> ?k1 |- (_ = map.get (map.put _ ?k2 _) ?k1)] => rewrite_get_put_diff
  | [H : ?k1 <> ?k2, H' : (map.get (map.put _ ?k1 _) ?k2 = _) |- _] => rewrite_get_put_diff_in H' 
  | [H : ?k2 <> ?k1, H' :  (map.get (map.put _ ?k1 _) ?k2 = _) |- _] => rewrite_get_put_diff_in H' 
  | [H : ?k1 <> ?k2, H' : (_ = map.get (map.put _ ?k1 _) ?k2) |- _] => rewrite_get_put_diff_in H' 
  | [H : ?k2 <> ?k1, H' : (_ = map.get (map.put _ ?k1 _) ?k2) |- _] => rewrite_get_put_diff_in H' 
  | [H' : (map.get (map.put _ ?k1 _) ?k2 = _), H : ?k1 <> ?k2 |- _] => rewrite_get_put_diff_in H' 
  | [H' :  (map.get (map.put _ ?k1 _) ?k2 = _), H : ?k2 <> ?k1 |- _] => rewrite_get_put_diff_in H' 
  | [H' : (_ = map.get (map.put _ ?k1 _) ?k2), H : ?k1 <> ?k2 |- _] => rewrite_get_put_diff_in H' 
  | [H' : (_ = map.get (map.put _ ?k1 _) ?k2), H : ?k2 <> ?k1 |- _] => rewrite_get_put_diff_in H' 
  | _ => trivial
  end;
  try rewrite map.get_empty;
  match goal with
  | [H : _ |- _] => rewrite map.get_empty in H; trivial
  | _ => trivial
  end.

Ltac map_prove_neq' crush hints :=
  let prove_neg := intro; crush hints; try break_map' crush hints; trivial; congruence in
  repeat match goal with
         | [H : ?k1 <> ?k2, H' : (map.get (map.put _ ?k1 _) ?k2 = _) |- _] => trivial
         | [H : ?k2 <> ?k1, H' :  (map.get (map.put _ ?k1 _) ?k2 = _) |- _] => trivial
         | [H : ?k1 <> ?k2, H' : (_ = map.get (map.put _ ?k1 _) ?k2) |- _] => trivial
         | [H : ?k2 <> ?k1, H' :  (_ = map.get (map.put _ ?k1 _) ?k2) |- _] => trivial
         | [H : ?k1 <> ?k2 |- (map.get (map.put _ ?k1 _) ?k2 = _)] => trivial
         | [H : ?k2 <> ?k1 |- (map.get (map.put _ ?k2 _) ?k1 = _)] => trivial
         | [H : ?k1 <> ?k2 |- (_ = map.get (map.put _ ?k1 _) ?k2)] => trivial
         | [H : ?k2 <> ?k1 |- (_ = map.get (map.put _ ?k2 _) ?k1)] => trivial
         | [ |- (map.get (map.put _ ?k1 _) ?k2 = _)] => assert (k1 <> k2) by prove_neg
         | [ |- (map.get (_ = map.put _ ?k1 _) ?k2)] => assert (k1 <> k2) by prove_neg
         | [H : (map.get (map.put _ ?k1 _) ?k2 = _) |- _] => assert (k1 <> k2) by prove_neg
         | [H : (map.get (_ = map.put _ ?k1 _) ?k2) |- _] => assert (k1 <> k2) by prove_neg
         | _ => trivial
         end
with break_map' crush hints := 
    repeat (crush hints; (repeat map_rewrite' crush hints); crush hints; map_prove_neq' crush hints).

Ltac map_crush_param' proofs crush hints :=
  match proofs with
  | ( ?proofs' , ?a) => let p := fresh "map_ok_proofs" in
                      pose proof a as p;
                      map_crush_param' proofs' crush hints;
                      clear p
  | ?a => let p := fresh "map_ok_proofs" in
          pose proof a as p;
          break_map' crush hints;
          clear p
  end.


Ltac map_rewrite crush hints :=
  try match goal with
      | [H : map.get _ _ = Some _ |- _] => rewrite H
      | [H : map.get _ _ = None |- _] => rewrite H
      | [H : Some _ = map.get _ _ |- _] => rewrite <- H
      | [H : None = map.get _ _ |- _] => rewrite <- H
      end;
  try rewrite map.get_empty;
  repeat match goal with
         | [H : _ |- _] => rewrite map.get_empty in H
         end;
  try rewrite map.get_put_same;
  repeat match goal with
         | [H : _ |- _] => rewrite map.get_put_same in H
         end;

  let prove_neg := let eq := fresh "eq" in
                   intro eq; subst; try congruence; trivial; (* cheap *)
                   crush hints; try break_map crush hints in (* expensive *)

  try match goal with
      | [ |- map.get (map.put _ ?k1 _) ?k2 = _] =>
        assert (k1 <> k2) by prove_neg; rewrite map.get_put_diff;
        try congruence
      | [H : (map.get (map.put _ ?k1 _) ?k2 = _) |- _] =>
        assert (k1 <> k2) by prove_neg; rewrite map.get_put_diff in H;
        try congruence
      end
   
with break_map crush hints := 
    repeat (crush hints; (repeat map_rewrite crush hints)).

Ltac map_crush_param proofs crush hints :=
  match proofs with
  | ( ?proofs' , ?a) => let p := fresh "map_ok_proofs" in
                      pose proof a as p;
                      map_crush_param proofs' crush hints;
                      clear p
  | ?a => let p := fresh "map_ok_proofs" in
          pose proof a as p;
          break_map crush hints;
          clear p
  end.

