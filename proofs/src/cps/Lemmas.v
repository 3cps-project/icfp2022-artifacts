
(* This file contains lemmas for proving that simulation is preserved across state transitions. 
   Just as we had a definition for simulation for each structure (environments, stores, etc)
   we have lemmas about each.

   For example, if we extend related environments in the proper way, they should remain related.

   Additionally, there are lemmas relating each of the components of the semantics.

   For example, if there are related environments and stores, then the
   concrete and abstract evaluations of the same CPS atom are related.

   At the top of this file there are several tactics useful for proving these lemmas.
   *)

Require Import coqutil.Map.Interface.
Definition map := map.map.
Require Import Ensembles.

Require Import common.Util.
Require Import common.Common.

Require Import cps.CPS.
Require Import cps.SemanticsCommon.
Require Import cps.ConcreteSemantics.
Require Import cps.AbstractSemantics.
Require Import cps.SimulationRelation.

(* The following are tactics useful for solving these simulation relation proofs *)
Ltac break_leqsim H :=
  match type of H with
  | (leqsim_env _ _ _) => destruct H
  | (leqsim_store _ _ _) => destruct H
  | (leqsim_value _ _ _) => destruct H
  | (leqsim_valueK _ _ _) => destruct H
  | (leqsim_valueKs _ _ _) => destruct H
  | (leqsim_proxy _ _ _ _) => destruct H
  | (leqsim_proxies _ _ _ _) => destruct H
  | (leqsim_storeProxy _ _ _ _) => destruct H
  | (leqsim_annotationSet _ _) => destruct H
  | (leqsim_state _ _ _ _) => destruct H
  end.

Ltac break_leqsim_goal :=
  repeat match goal with
         | [ |- leqsim_env _ _ _] => constructor; intros
         | [ |- leqsim_store _ _ _] => constructor; intros
         | [ |- leqsim_value _ _ _] => constructor; intros
         | [ |- leqsim_valueK _ _ _] => constructor; intros
         | [ |- leqsim_valueKs _ _ _] => constructor; intros
         | [ |- leqsim_proxy _ _ _ _] => constructor; intros
         | [ |- leqsim_proxies _ _ _ _] => constructor; intros
         | [ |- leqsim_storeProxy _ _ _ _] => constructor; intros
         | [ |- leqsim_annotationSet _ _] => constructor; intros
         | [ |- leqsim_state _ _ _ _] => constructor; intros
         end.

Ltac lazy_trivial none := trivial.
Ltac crush_hints hints := crush_param lazy_trivial hints.
Ltac crush := crush_hints tt.

Ltac map_crush_hints hints :=
  map_crush_param (env_proofs, store_proofs, storeProxy_proofs,
                   aenv_proofs, astore_proofs, astoreProxy_proofs,
                   leqsim_addr_proofs, leqsim_addrProxy_proofs)
                  crush_hints
                  hints.
Ltac map_crush := map_crush_hints tt.

Ltac map_crush_hints' hints :=
  map_crush_param' (env_proofs, store_proofs, storeProxy_proofs,
                   aenv_proofs, astore_proofs, astoreProxy_proofs,
                   leqsim_addr_proofs, leqsim_addrProxy_proofs)
                  crush_hints
                  hints.
Ltac map_crush' := map_crush_hints' tt.

Ltac try_exists :=
  match goal with
  | [ H : ?t, H' : ?t |- exists _ : ?t, _ ] => trivial
  | [ H : ?t |- exists _ : ?t, _ ] => exists H
  | _ => trivial
  end.

Ltac auto_specializeH_hints_helper H hints t hints' :=
  lazymatch hints' with
  | tt => match (*multimatch *) goal with
          | [ H' : t |- _ ] => specialize (H H'); auto_specializeH_hints H hints
          end
  | (?hints'' , ?hint) =>
    match type of hint with
    | t => specialize (H hint); auto_specializeH_hints H hints''
    | _ => auto_specializeH_hints_helper H hints t hints''
    end
  | ?hint =>
    match type of hint with
    | t => specialize (H hint); auto_specializeH_hints H tt
    | _ => auto_specializeH_hints_helper H hints t tt
    end
  end
with auto_specializeH_hints H hints :=
  lazymatch type of H with
  | forall (x : ?t), _ => auto_specializeH_hints_helper H hints t hints
  | _ => idtac
  end.

Ltac auto_specialize_hints crush hints :=
  repeat (crush;
          repeat match goal with
                 | [ H : forall (x : ?t), _ |- _ ] => auto_specializeH_hints H hints
                 end).
  
Ltac auto_specialize_lemma_hints lemma hints :=
  let lem := fresh "lemma" in
  pose proof lemma as lem;
  match type of lem with
    forall (x : ?t), _ => auto_specializeH_hints_helper lem hints t hints
  | _ => clear lem; idtac
  end.

Ltac map_case_match :=match goal with
  | [H : context[match map.get ?m ?k with _ => _ end] |- _ ]
    => let e':= fresh in
       let eqnname := fresh in
       remember (map.get m k) as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.
Ltac map_case_match_goal :=match goal with
  | [ |- context[match map.get ?m ?k with _ => _ end] ]
    => let e':= fresh in
       let eqnname := fresh in
       remember (map.get m k) as e' eqn:eqnname; symmetry in eqnname; destruct e'
  end.

Tactic Notation (at level 1) "auto_specialize" tactic(crush) :=
  auto_specialize_hints crush tt. 
Tactic Notation (at level 1) "auto_specialize" tactic(crush) "using" constr(hints) :=
  auto_specialize_hints crush hints. 
Tactic Notation (at level 1) "auto_specializeH" constr(H) :=
  auto_specializeH_hints H tt.
Tactic Notation (at level 1) "auto_specializeH" constr(H) "using" constr(hints) :=
  auto_specializeH_hints H hints. 
Tactic Notation (at level 1) "auto_lemma" constr(lemma) :=
  auto_specialize_lemma_hints lemma tt. 
Tactic Notation (at level 1) "auto_lemma" constr(lemma) "using" constr(hints) :=
  auto_specialize_lemma_hints lemma hints.

Ltac lazy_map_crush none := map_crush.
Ltac brute := brute_param lazy_map_crush. 

(* Below are the start of the actual lemmas *)

Lemma map_get_or : forall {key value : Type} {map : map key value} (m : map) k, (exists v, map.get m k = Some v) \/ map.get m k = None.
Proof.
  intros.
  case (map.get m k); brute.
Qed.

(* Accessing related environments yields related results. *)
Theorem leqsim_env_get : forall (leqsim_addr : leqsim_addr) (a : addr) (aa : aaddr) (rho : env) (arho : aenv) (x : var),
    leqsim_env leqsim_addr rho arho ->
    map.get rho x = Some a ->
    map.get leqsim_addr a = Some aa ->
    map.get arho x = Some aa.
Proof.
  crush; break_leqsim H; specialize (H x a H0); destruct H; crush.
Qed.

(* Extending the address-relation preserves environment relatedness. *)
Theorem leqsim_env_ext0 : forall (leqsim_addr : leqsim_addr) (a : addr) (aa : aaddr) (rho : env) (arho : aenv),
    leqsim_env leqsim_addr rho arho ->
    map.get leqsim_addr a = None ->
    leqsim_env (map.put leqsim_addr a aa) rho arho.
Proof. 
  crush.
  break_leqsim_goal.
  break_leqsim H.
  
  firstorder map_crush.
Qed.

(* Extending related environments yields related results. *)
Theorem leqsim_env_ext : forall (leqsim_addr : leqsim_addr) (x : var) (a : addr) (aa : aaddr) (rho : env) (arho : aenv),
    leqsim_env leqsim_addr rho arho ->
    map.get leqsim_addr a = None ->
    leqsim_env (map.put leqsim_addr a aa)
          (map.put rho x a)
          (map.put arho x aa).
Proof. 
  crush.
  break_leqsim_goal.
  case (Var.dec x x0); map_crush.
  - eexists; firstorder map_crush.
  - break_leqsim H. (auto_specialize crush); eexists; map_crush. 
Qed.

(* An abstract value set that contains a related closure means the whole value is related *)
Theorem leqsim_value_single_sub : forall leqsim_addr x ks body rho arho ad,
    leqsim_env leqsim_addr rho arho ->
    In aclo ad (AClosure x ks body arho) ->
    leqsim_value leqsim_addr (Closure x ks body rho) ad.
Proof.
  crush; break_leqsim_goal; eexists; crush. 
Qed.

(* An singleton abstract value set containing a related closure is related *)
Theorem leqsim_value_single : forall leqsim_addr x ks body rho arho,
    leqsim_env leqsim_addr rho arho ->
    leqsim_value leqsim_addr (Closure x ks body rho) (Singleton aclo (AClosure x ks body arho)).
Proof.
  crush; eapply leqsim_value_single_sub; try apply In_singleton; crush.
Qed.

(* Evaluating an atom under related components yields a related result *)
Theorem leqsim_eval : forall (leqsim_addr : leqsim_addr) (ae : atom) (rho : env) (sigma : store) (arho : aenv) (asigma : astore) (d : value),
    leqsim_env leqsim_addr rho arho ->
    leqsim_store leqsim_addr sigma asigma ->
    eval ae rho sigma = Some d ->
    exists ad, 
      aeval ae arho asigma = Some ad /\
      leqsim_value leqsim_addr d ad.
Proof.
  crush.
  cases ae; crush; unfold eval in *; unfold aeval.
  - unfold Common.option_bind in *. 
    repeat map_case_match; crush.
    break_leqsim H; break_leqsim H0.
    (auto_specialize crush). 
    eexists; crush; map_crush.
  - eexists; crush; try apply leqsim_value_single; crush.
Qed.

(* Joining a related value on the left yields another related value *)
Theorem leqsim_value_ext_left : forall leqsim_addr d ad ad',
    leqsim_value leqsim_addr d ad ->
    leqsim_value leqsim_addr d (join_avalue ad ad').
Proof.
  crush.
  break_leqsim H; crush.
  break_leqsim_goal; eexists; crush; try apply Union_introl; crush.
Qed.

(* Joining a related value on the right yields another related value *)
Theorem leqsim_value_ext_right : forall leqsim_addr d ad ad',
    leqsim_value leqsim_addr d ad' ->
    leqsim_value leqsim_addr d (join_avalue ad ad').
Proof.
  crush.
  break_leqsim H; crush.
  break_leqsim_goal; eexists; crush; try apply Union_intror; crush.
Qed.

(* Extending the address-relation map preserves relatedness of values *)
Theorem leqsim_value_ext0 : forall leqsim_addr a aa d ad,
    map.get leqsim_addr a = None ->
    leqsim_value leqsim_addr d ad ->
    leqsim_value (map.put leqsim_addr a aa) d ad.
Proof.
  crush. 
  break_leqsim H0; crush.
  break_leqsim_goal; eexists; crush.
  apply leqsim_env_ext0; crush.
Qed.

Theorem get_astore_ext : forall asigma aa aa' ad, 
    aa' <> aa ->
    map.get (add_join asigma aa ad) aa' = map.get asigma aa'.
Proof.
  crush; unfold add_join.
  map_case_match_goal; map_crush. 
Qed.


(* Extending the abstract store with a joined value relatedness of the stores *)
Theorem leqsim_store_ext : forall leqsim_addr sigma asigma a aa d ad,
    map.get leqsim_addr a = None ->
    leqsim_value leqsim_addr d ad ->
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_store (map.put leqsim_addr a aa) (map.put sigma a d) (add_join asigma aa ad).
Proof.
  crush.
  break_leqsim_goal; crush.
  case (AAddr.dec aa aa0); map_crush.
  - unfold add_join.
    case (map_get_or asigma aa0); crush; rewrite H4; crush.
    + exists (join_avalue ad x); map_crush.
      apply leqsim_value_ext0; crush.
      case (Addr.dec a a0); map_crush.
      ++ apply leqsim_value_ext_left; crush.
      ++ apply leqsim_value_ext_right; crush.
         break_leqsim H1; brute.
    + exists ad; map_crush.
      case (Addr.dec a a0); map_crush.
      ++ apply leqsim_value_ext0; crush.
      ++ apply leqsim_value_ext0; crush.
         break_leqsim H1; brute. 
  - assert (a <> a0) by (intro; map_crush).
    break_leqsim H1.
    specialize (H1 a0 aa0 d0 H2 H3); crush.
    exists x; map_crush.
    + rewrite get_astore_ext; map_crush.
    + apply leqsim_value_ext0; map_crush.
Qed.

(* Evaluating continuation atoms under related components yields related results *)
Lemma leqsim_evalK : forall leqsim_addr indexOf rho arho q,
    leqsim_env leqsim_addr rho arho ->
    leqsim_valueK leqsim_addr (evalK indexOf rho q) (aevalK indexOf arho q).
Proof.
  crush; case q; simpl in *; crush; constructor; crush.
Qed.

(* Evaluating a list of continuation atoms under related components yields related results *)
Lemma leqsim_evalKs : forall leqsim_addr indexOf rho arho qs,
    leqsim_env leqsim_addr rho arho ->
    leqsim_valueKs leqsim_addr (List.map (evalK indexOf rho) qs) (List.map (aevalK indexOf arho) qs).
Proof.
  crush; induction qs; simpl in *; crush; constructor; crush.
  apply leqsim_evalK; crush.
Qed.                  

(* If a proxy is related to an abstract proxy and the abstract proxy
   is in a set, then the proxy is related to the set. *)
Theorem leqsim_proxies_single_sub : forall leqsim_addr leqsim_addrProxy proxy aproxy aproxies,
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    In _ aproxies aproxy ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies.
Proof.
  crush; break_leqsim_goal; eexists; map_crush; constructor; map_crush.
Qed.

(* Proxies are related to singleton sets containing a related element. *)
Theorem leqsim_proxies_single : forall leqsim_addr leqsim_addrProxy proxy aproxy,
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy (Singleton _ aproxy).
Proof.
  crush; eapply leqsim_proxies_single_sub; crush; apply In_singleton. 
Qed.

(* Joining a related set of proxies on the left yields another related value. *)
Theorem leqsim_proxies_ext_left : forall leqsim_addr leqsim_addrProxy proxy aproxies aproxies',
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy (join_aproxies aproxies aproxies').
Proof.
  crush; break_leqsim H; break_leqsim_goal; crush.
  eexists; crush; apply Union_introl; crush.
Qed.  

(* Joining a related set of proxies on the right yields another related value. *)
Theorem leqsim_proxies_ext_right : forall leqsim_addr leqsim_addrProxy proxy aproxies aproxies',
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy (join_aproxies aproxies' aproxies).
Proof.
  crush; break_leqsim H; break_leqsim_goal; crush.
  eexists; crush; apply Union_intror; crush.
Qed.  

(* Extending the address-relation map preserves relatedness for continuation values. *)
Theorem leqsim_valueK_ext0 : forall leqsim_addr a aa c ac,
    map.get leqsim_addr a = None ->
    leqsim_valueK leqsim_addr c ac ->
    leqsim_valueK (map.put leqsim_addr a aa) c ac.
Proof.
  crush; break_leqsim H0; constructor; apply leqsim_env_ext0; crush.
Qed.

(* Extending the address-relation map preserves relatedness for lists of continuation values. *)
Theorem leqsim_valueKs_ext0 : forall leqsim_addr a aa cs acs,
    map.get leqsim_addr a = None ->
    leqsim_valueKs leqsim_addr cs acs ->
    leqsim_valueKs (map.put leqsim_addr a aa) cs acs.
Proof.
  crush; induction H0; constructor; try apply leqsim_valueK_ext0; crush.
  apply IHleqsim_valueKs; crush.
Qed.

(* Extending the address-relation map preserves relatedness for proxies. *)
Theorem leqsim_proxy_ext0 : forall leqsim_addr leqsim_addrProxy a aa proxy aproxy,
    map.get leqsim_addr a = None ->
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    leqsim_proxy (map.put leqsim_addr a aa) leqsim_addrProxy proxy aproxy.
Proof.
  crush; break_leqsim H0; constructor; try apply leqsim_env_ext0; crush; apply leqsim_valueKs_ext0; crush. 
Qed.

(* Extending the address-relation map preserves relatedness for sets of proxies. *)
Theorem leqsim_proxies_ext0 : forall leqsim_addr leqsim_addrProxy a aa proxy aproxies,
    map.get leqsim_addr a = None ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies ->
    leqsim_proxies (map.put leqsim_addr a aa) leqsim_addrProxy proxy aproxies.
Proof.
  crush; break_leqsim H0; break_leqsim_goal; crush.
  eexists; crush; apply leqsim_proxy_ext0; crush.
Qed.

(* Extending the proxy address-relation map preserves relatedness for proxies. *)
Theorem leqsim_proxy_extProxy0 : forall leqsim_addr leqsim_addrProxy aP aaP proxy aproxy,
    map.get leqsim_addrProxy aP = None ->
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    leqsim_proxy leqsim_addr (map.put leqsim_addrProxy aP aaP) proxy aproxy.
Proof.
  crush; break_leqsim H0; crush; constructor; crush; map_crush.
Qed.

(* Extending the proxy address-relation map preserves relatedness for sets of proxies. *)
Theorem leqsim_proxies_extProxy0 : forall leqsim_addr leqsim_addrProxy aP aaP proxy aproxies,
    map.get leqsim_addrProxy aP = None ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies ->
    leqsim_proxies leqsim_addr (map.put leqsim_addrProxy aP aaP) proxy aproxies.
Proof.
  crush; break_leqsim H0; crush; constructor; eexists; crush; apply leqsim_proxy_extProxy0; crush.
Qed.

Theorem get_astoreProxy_joinProxy : forall asigmaP aaP aaP' aproxies, 
    aaP' <> aaP ->
    map.get (add_joinP asigmaP aaP aproxies) aaP' = map.get asigmaP aaP'.
Proof.
  crush; unfold add_joinP; map_case_match_goal; map_crush.
Qed.  

(* Extending (joining) the stores preserves store-relateness (under extended address maps) *)
Theorem leqsim_storeProxy_extProxy : forall leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP proxy aproxies,
    map.get leqsim_addrProxy aP = None ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_storeProxy leqsim_addr
             (map.put leqsim_addrProxy aP aaP)
             (map.put sigmaP aP proxy)
             (add_joinP asigmaP aaP aproxies).
Proof.
  crush.
  break_leqsim_goal; crush.
  case (AAddrProxy.dec aaP aaP0); map_crush.
  - unfold add_joinP.
    case (map_get_or asigmaP aaP0); crush; rewrite H4; crush.
    + exists (join_aproxies aproxies x); map_crush.
      apply leqsim_proxies_extProxy0; crush.
      case (AddrProxy.dec aP aP0); map_crush.
      ++ apply leqsim_proxies_ext_left; crush.
      ++ apply leqsim_proxies_ext_right; crush.
         break_leqsim H1; brute.
    + exists aproxies; map_crush.
      case (AddrProxy.dec aP aP0); map_crush.
      ++ apply leqsim_proxies_extProxy0; crush.
      ++ apply leqsim_proxies_extProxy0; crush.
         break_leqsim H1; brute.
  - assert (aP <> aP0) by (intro; map_crush).
    map_crush.
    break_leqsim H1.
    rewrite get_astoreProxy_joinProxy; map_crush. 
    (auto_specialize crush); eexists; map_crush.
    apply leqsim_proxies_extProxy0; map_crush.
Qed.


(* Extending the address-relation map preserves relatedness for proxy stores. *)
Theorem leqsim_storeProxy_ext : forall leqsim_addr leqsim_addrProxy sigmaP asigmaP a aa,
    map.get leqsim_addr a = None ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_storeProxy (map.put leqsim_addr a aa) leqsim_addrProxy sigmaP asigmaP.
Proof.
  crush; break_leqsim H0; break_leqsim_goal; crush.
  (auto_specialize crush).
  eexists; crush; apply leqsim_proxies_ext0; crush.
Qed.

Lemma update_leqsim_addr : forall (leqsim_addr : leqsim_addr) a aa,
    map.get leqsim_addr a = None ->
    forall a' aa',
      a <> a' ->
      map.get leqsim_addr a' = Some aa' ->
      map.get (map.put leqsim_addr a aa) a' = Some aa'.
Proof.
  map_crush.
Qed.

Lemma update_leqsim_addrProxy : forall (leqsim_addrProxy : leqsim_addrProxy) (aP : addrProxy) (aaP : aaddrProxy),
    map.get leqsim_addrProxy aP = None ->
    forall (aP' : addrProxy) (aaP' : aaddrProxy),
      aP <> aP' ->
      map.get leqsim_addrProxy aP' = Some aaP' ->
      map.get (map.put leqsim_addrProxy aP aaP) aP' = Some aaP'.
Proof.
  map_crush.
Qed.


(* Related proxy stores gives related queries. *)
Theorem leqsim_proxy_exists :
  forall leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP proxy,
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    map.get sigmaP aP = Some proxy ->
    map.get leqsim_addrProxy aP = Some aaP ->
    exists aproxies aproxy,
           map.get asigmaP aaP = Some aproxies /\
           In _ aproxies aproxy /\
           leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy.
Proof.
  crush. 
  break_leqsim H.
  specialize (H aP aaP proxy H0 H1).
  crush.
  eexists x.
  break_leqsim H2; crush.
  exists x; crush.
Qed.
  
(* Related lists of continuation values are indeed related at each component. *)
Theorem leqsim_valueKs_nth_opt :
  forall leqsim_addr i cs c_i acs,
    leqsim_valueKs leqsim_addr cs acs ->
    Common.nth_opt i cs = Some c_i->
    exists ac_i,
      Common.nth_opt i acs = Some ac_i /\
      leqsim_valueK leqsim_addr c_i ac_i.
Proof. 
  crush.
  revert i c_i H0; induction H; crush.
  - simpl in H0; destruct i; crush.
  - simpl in H1; simpl. destruct i; crush. 
    + exists ac_i; crush.
    + apply IHleqsim_valueKs; crush.
Qed.

(* The auxiliary functions findCloK provide related results *)
Lemma leqsim_findCloK : forall leqsim_addr leqsim_addrProxy sigmaP asigmaP
                               c ac aP aaP
                               c' aP',
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    map.get leqsim_addrProxy aP = Some aaP ->
    leqsim_valueK leqsim_addr c ac ->
    findCloK sigmaP c aP c' aP' ->
    exists ac' aaP',
      map.get leqsim_addrProxy aP' = Some aaP' /\
      leqsim_valueK leqsim_addr c' ac' /\
      afindCloK asigmaP ac aaP ac' aaP'.
Proof.
  crush. revert ac aaP H0 H1; induction H2; crush.
  - exists ac; exists aaP.
    inversion H1; crush. 
    econstructor; crush.
  - inversion H4; crush. 
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e rho cs aP') H H0 H3); crush.
    inversion H7; crush.
    specialize (leqsim_valueKs_nth_opt leqsim_addr i cs c_i acs H16 H1); crush.
    specialize (IHfindCloK H x0 aaP0 H17 H9); crush.
    exists x1; exists x2; crush.
    econstructor; crush.
Qed.

(* The auxiliary functions poppedBindings_valueK provide related results *)
Lemma leqsim_poppedBindings_valueK : forall localBindings alocalBindings leqsim_addr leqsim_addrProxy sigmaP asigmaP
                                             c ac aP aaP bindings_local abindings_local,
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    map.get leqsim_addrProxy aP = Some aaP ->
    leqsim_valueK leqsim_addr c ac ->
    leqsim_bindings leqsim_addr bindings_local abindings_local ->
    (forall e rho arho,
        leqsim_env leqsim_addr rho arho ->
        leqsim_bindings leqsim_addr (localBindings e rho) (alocalBindings e arho)) ->
    leqsim_bindings leqsim_addr
                    (poppedBindings_valueK localBindings sigmaP c aP bindings_local)
                    (apoppedBindings_valueK alocalBindings asigmaP ac aaP abindings_local).
Proof.
  crush. 
  constructor; crush.
  revert aaP H0 ac H1 abindings_local H2.
  induction H4; crush.
  - inversion H2; crush.
    destruct H4; crush.
    specialize (H4 x a H0); crush.
    exists x0; crush.
    constructor; crush.
  - inversion H5; crush.
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e rho cs aP') H H0 H2); crush.
    inversion H9; crush.
    specialize (leqsim_valueKs_nth_opt leqsim_addr i cs c_i acs H18 H1); crush.
    specialize (IHpoppedBindings_valueK H H3 aaP0 H19 x1 H11 (alocalBindings e arho) (H3 e rho arho H17)); crush.
    exists x2; crush; eapply ChainPoppedABindings_valueK; crush.
Qed.

(* An abstract list of continuation values related to a list of
   indexes is also a list of indices. *)
Lemma leqsim_valueKs_idxs_exists :
  forall leqsim_addr idxs acs,
    leqsim_valueKs leqsim_addr (List.map Index idxs) acs ->
    acs = List.map AIndex idxs.
Proof.
  crush.
  revert acs H.
  induction idxs; crush.
  - inversion H; crush.
  - inversion H; crush.
    inversion H5; crush; simpl; rewrite (IHidxs acs0 H3); crush.
Qed.

(* An abstract proxy related to a proxy of indexes also contains only indexes. *)
Theorem leqsim_proxy_idxs_exists :
  forall leqsim_addr leqsim_addrProxy aP aaP e rho arho acs idxs,
    let proxy := (Proxy e rho (List.map Index idxs) aP) in
    let aproxy := (AProxy e arho acs aaP) in
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    acs = List.map AIndex idxs.
Proof.
  crush.
  inversion H; crush.
  apply (leqsim_valueKs_idxs_exists leqsim_addr idxs acs); crush.
Qed.

(* Selecting out of related lists of continuation values yields related results. *)
Theorem leqsim_valueKs_select_idxs :
  forall leqsim_addr cs acs cs' idxs,
    leqsim_valueKs leqsim_addr cs acs ->
    select_idxs cs idxs = Some cs' ->
    exists acs',
      select_idxs acs idxs = Some acs' /\
      leqsim_valueKs leqsim_addr cs' acs'.
Proof.
  crush. 
  revert cs acs cs' H H0.
  induction idxs; crush; simpl in *; crush.  
  - exists nil; crush; constructor; crush.
  - unfold option_bind in *; crush; simpl in *; crush.
    assert (exists l, select_idxs cs idxs = Some l) by
        (destruct (select_idxs cs idxs); crush; destruct (nth_opt a cs); crush; exists l; crush).
    destruct H1; rewrite H1 in *.
    assert (exists b, nth_opt a cs = Some b) by
        (destruct (nth_opt a cs); crush; eexists; crush).
    destruct H2; rewrite H2 in *.
    specialize (IHidxs cs acs x H H1); crush.
    rewrite H3; crush.
    specialize (leqsim_valueKs_nth_opt leqsim_addr a cs x0 acs H H2); crush.
    rewrite H0.
    exists (cons x2 x1); crush.
    constructor; crush.
Qed.

(* Selecting a continuation value out of related proxies yields related results. *)
Theorem leqsim_proxy_fix :
  forall leqsim_addr leqsim_addrProxy e rho arho aP aaP cs acs cs' idxs,
    leqsim_proxy leqsim_addr leqsim_addrProxy (Proxy e rho cs aP) (AProxy e arho acs aaP) ->
    select_idxs cs idxs = Some cs' ->
    exists acs',
      (select_idxs acs idxs = Some acs' /\
       leqsim_proxy leqsim_addr leqsim_addrProxy (Proxy e rho cs' aP) (AProxy e arho acs' aaP)).
Proof.
  crush.
  inversion H; crush.
  specialize (leqsim_valueKs_select_idxs leqsim_addr cs acs cs' idxs H11 H0); crush.
  exists x; crush.
  constructor; crush.
Qed.

(* The auxiliary functions popProxy provide related results *)
Lemma leqsim_popProxy : forall leqsim_addr leqsim_addrProxy sigmaP asigmaP proxy proxy' aproxy,
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    popProxy sigmaP proxy proxy' ->
    exists aproxy',
      leqsim_proxy leqsim_addr leqsim_addrProxy proxy' aproxy' /\
      apopProxy asigmaP aproxy aproxy'.
Proof.
  crush.
  revert aproxy H0; induction H1; crush.
  - inversion H1; crush.
    exists (AProxy e arho acs aaP); crush.
    constructor.
    induction H10; crush; simpl in *; crush. 
    destruct H0. 
    + left.
      case c_i; break_leqsim H2; crush.
    + right.
      apply IHleqsim_valueKs; crush.
      constructor; crush.
  - inversion H3; crush.
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e' rho' cs' aP') H H0 H13); crush.
    inversion H6; crush.
    specialize (leqsim_proxy_fix leqsim_addr leqsim_addrProxy e' rho' arho0 aP' aaP0 cs' acs0 cs'_fixed idxs H6 H1); crush.
    specialize (IHpopProxy H (AProxy e' arho0 x0 aaP0) H8); crush.
    specialize (leqsim_proxy_idxs_exists leqsim_addr leqsim_addrProxy aP aaP e rho arho acs idxs H3); crush.
    exists x1; crush.
    econstructor; crush.
Qed.    

(* The auxiliary functions poppedBindings_proxy provide related results *)
Lemma leqsim_poppedBindings_proxy : forall (localBindings : term -> env -> var -> addr -> Prop) alocalBindings leqsim_addr leqsim_addrProxy sigmaP asigmaP
                                            proxy aproxy,
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy ->
    (forall e rho arho,
        leqsim_env leqsim_addr rho arho ->
        leqsim_bindings leqsim_addr (localBindings e rho) (alocalBindings e arho)) ->
    leqsim_bindings leqsim_addr 
                    (poppedBindings_proxy localBindings sigmaP proxy)
                    (apoppedBindings_proxy alocalBindings asigmaP aproxy).
Proof.
  crush.
  constructor; crush.
  revert aproxy H0.
  induction H2; crush.
  - inversion H3; crush.
    specialize (leqsim_proxy_idxs_exists leqsim_addr leqsim_addrProxy aP aaP e rho arho acs idxs H3); crush.
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e' rho' cs' aP') H H0 H13); crush.
    inversion H6; crush.
    specialize (H1 e rho arho H11); crush.
    inversion H1; crush.
    specialize (H7 x a H2); crush.
    exists x1; crush; eapply ImmPoppedABindings_proxy; crush.
  - inversion H4; crush.
    specialize (leqsim_proxy_idxs_exists leqsim_addr leqsim_addrProxy aP aaP e rho arho acs idxs H4); crush.
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e' rho' cs' aP') H H0 H14); crush.
    inversion H7; crush.
    specialize (leqsim_proxy_fix leqsim_addr leqsim_addrProxy e' rho' arho0 aP' aaP0 cs' acs cs'_fixed idxs H7 H2); crush.
    specialize (IHpoppedBindings_proxy H H1 (AProxy e' arho0 x1 aaP0) H9); crush.
    exists x2; crush; eapply ChainPoppedABindings_proxy; crush.
Qed.


(* The stack extent check yields related annotations sets. *)
Theorem leqsim_checkS :
  forall (leqsim_addr : leqsim_addr) an aan
         (bindings_live : var -> addr -> Prop) (abindings_live : var -> aaddr -> Prop) 
         (bindings_popped : var -> addr -> Prop) (abindings_popped : var -> aaddr -> Prop),
    leqsim_annotationSet an aan ->

    leqsim_bindings leqsim_addr bindings_live abindings_live ->
    leqsim_bindings leqsim_addr bindings_popped abindings_popped ->
                                       
    let an' := checkS bindings_live bindings_popped an in
    let aan' := acheckS abindings_live abindings_popped aan in
    leqsim_annotationSet an' aan'.
Proof.
  crush.
  unfold checkS; unfold acheckS.
  break_leqsim H; break_leqsim_goal; unfold Included in *; crush.
  induction x.
  induction e; simpl in *; crush;
  unfold In in *;
  unfold Setminus in *;
  unfold In in *; crush.
  - apply H; crush.
  - apply H; crush.
  - intro H4; crush.
    destruct H0.
    specialize (H0 v x H4).
    destruct H1.
    specialize (H1 v x H5).
    apply H3.
    crush.
    assert (x1 = x0) by crush; crush.
    exists x0; crush.
Qed.

(* The register extent check yields related annotations sets. *)
Theorem leqsim_checkR :
  forall (leqsim_addr : leqsim_addr) an aan
         (bindings_live : var -> addr -> Prop) (abindings_live : var -> aaddr -> Prop)
         (x : var),
    leqsim_annotationSet an aan ->
    leqsim_bindings leqsim_addr bindings_live abindings_live ->
    let an' := checkR x bindings_live an in
    let aan' := acheckR x abindings_live aan in
    leqsim_annotationSet an' aan'.
Proof.
  crush.
  unfold checkR; unfold acheckR.
  break_leqsim H; break_leqsim_goal; unfold Included in *; crush.
  induction x0.
  induction e; simpl in *; crush;
  unfold In in *;
  unfold Setminus in *;
  unfold In in *; crush.
  - apply H; crush.
  - intro H3; crush.
    destruct H0.
    specialize (H0 v x0 H4).
    apply H2.
    crush.
    exists x; crush.
  - apply H; crush.
Qed.

(* The following lemmas are for liveness queries. *)
  
(* Induction schemes for the liveness definitions. *)
Scheme live_var_ind' := Minimality for live_var Sort Prop
  with live_value_ind' := Minimality for live_value Sort Prop
.
Combined Scheme live_ind
         from live_var_ind', live_value_ind'.

Scheme live_varK_ind' := Minimality for live_varK Sort Prop
  with live_valueK_ind' := Minimality for live_valueK Sort Prop
.
Combined Scheme liveK_ind
         from live_varK_ind', live_valueK_ind'.

(* Relatedness for lists of values. *)
Inductive leqsim_values : leqsim_addr -> list value -> list avalue -> Prop :=
| ListValue_Rel_nil : forall leqsim_addr, leqsim_values leqsim_addr nil nil
| ListValue_Rel_cons : forall leqsim_addr d_i ds ad_i ads,
    leqsim_values leqsim_addr ds ads ->
    leqsim_value leqsim_addr d_i ad_i ->
    leqsim_values leqsim_addr (cons d_i ds) (cons ad_i ads).


(* A concrete binding being live implies the corresponding abstract
   binding is live under related components. *)
Lemma leqsim_live_var_value :
  (forall sigma rho y x a,
      live_var sigma rho y x a ->
      forall leqsim_addr asigma arho,
        leqsim_store leqsim_addr sigma asigma ->
        leqsim_env leqsim_addr rho arho ->
        exists aa,
        map.get leqsim_addr a = Some aa /\
        alive_var asigma arho y x aa) /\
  (forall sigma d x a,
      live_value sigma d x a ->
      forall leqsim_addr asigma ad,
      leqsim_store leqsim_addr sigma asigma ->
      leqsim_value leqsim_addr d ad ->
      exists aa, 
      map.get leqsim_addr a = Some aa /\
      alive_value asigma ad x aa).
Proof.
  apply live_ind; crush.
  - break_leqsim H1; crush.
    specialize (H1 x a H); crush.
    exists x0; crush; constructor; crush.
  - specialize (leqsim_eval leqsim_addr (Var y) rho sigma arho asigma d H3 H2 H).
    crush.
    specialize (H1 leqsim_addr asigma x0 H2 H5); crush.
    exists x1; crush;
    eapply ChainALiveVar; crush.
  - inversion H3; crush.
    specialize (H1 leqsim_addr asigma x1 H2 H11); crush.
    exists x0; crush. econstructor; crush. 
Qed.

(* Related components yield related liveness results for variables. *)
Lemma leqsim_live_var :
  forall leqsim_addr x a
         sigma rho y
         asigma arho,
    live_var sigma rho y x a ->
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_env leqsim_addr rho arho ->
    exists aa, 
    map.get leqsim_addr a = Some aa /\
    alive_var asigma arho y x aa.
Proof.
  crush; eapply leqsim_live_var_value; crush.
Qed.

(* A concrete binding being live via a value implies the corresponding abstract
   binding is live via the related value under related components. *)
Lemma leqsim_live_value :
  forall leqsim_addr x a
         sigma d
         asigma ad,
    live_value sigma d x a ->
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_value leqsim_addr d ad ->
    exists aa,
    map.get leqsim_addr a = Some aa /\
    alive_value asigma ad x aa.
Proof.
  crush; eapply leqsim_live_var_value; crush.
Qed.

(* A binding being live for some value in a list of values means its
   corresponding abstract binding is live for the corresponding list of
   values. *)
Lemma leqsim_live_values :
  forall leqsim_addr x a
         sigma ds
         asigma ads,
    leqsim_store leqsim_addr sigma asigma ->
    List.fold_right (fun (d : value) (acc : Prop) => live_value sigma d x a \/ acc) False ds ->
    leqsim_values leqsim_addr ds ads ->
    exists aa,
    map.get leqsim_addr a = Some aa /\
    List.fold_right (fun (ad : avalue) (acc : Prop) => alive_value asigma ad x aa \/ acc) False ads.
Proof.
  crush. 
  induction H1; crush; simpl in *; crush; try contradiction.
  destruct H0.
  - specialize (leqsim_live_value leqsim_addr x a sigma d_i asigma ad_i H0 H H2); crush.
    exists x0; crush.
    left; crush.
  - specialize (IHleqsim_values H H0); crush.
    eexists x0; crush.
    right; crush.
Qed.

(* If a binding is live via continuation variables or continuation
   values then the corresponding abstract binding is live. *)
Lemma leqsim_live_varK_valueK :
  (forall indexOf sigmaP sigma k aP x a,
      live_varK indexOf sigmaP sigma k aP x a ->
      forall leqsim_addr leqsim_addrProxy asigmaP asigma aaP,
        leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
        leqsim_store leqsim_addr sigma asigma ->
        map.get leqsim_addrProxy aP = Some aaP ->
        exists aa,
        map.get leqsim_addr a = Some aa /\
        alive_varK indexOf asigmaP asigma k aaP x aa) /\
  (forall indexOf sigmaP sigma c aP x a,
      live_valueK indexOf sigmaP sigma c aP x a ->
      forall leqsim_addr leqsim_addrProxy asigmaP asigma ac aaP,
      leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
      leqsim_store leqsim_addr sigma asigma ->
      leqsim_valueK leqsim_addr c ac ->
      map.get leqsim_addrProxy aP = Some aaP ->
      exists aa,
      map.get leqsim_addr a = Some aa /\
      alive_valueK indexOf asigmaP asigma ac aaP x aa).
Proof.
  apply liveK_ind; crush.
  - assert (leqsim_valueK leqsim_addr (Index (indexOf k)) (AIndex (indexOf k))) by (constructor; crush).

    specialize (H0 leqsim_addr leqsim_addrProxy asigmaP asigma (AIndex (indexOf k)) aaP H1 H2 H4 H3).
    destruct H0; exists x0; crush; constructor; crush.
  - inversion H5; crush.
    specialize (leqsim_proxy_exists leqsim_addr leqsim_addrProxy sigmaP asigmaP aP aaP (Proxy e' rho' cs' aP') H3 H H6); crush.
    inversion H9; crush.
    specialize (leqsim_valueKs_nth_opt leqsim_addr i cs' c' acs H18 H0); crush.
    specialize (H2 leqsim_addr leqsim_addrProxy asigmaP asigma x1 aaP0 H3 H4 H11 H19); crush.
    exists x2; crush.
    eapply IndexALiveValueK; crush.
  - inversion H4; crush. 
    specialize (H1 leqsim_addr leqsim_addrProxy asigmaP asigma aaP H2 H3 H5); crush.
    exists x0; crush; eapply ClosureVarKALiveValueK; crush.
  - inversion H3; crush.
    specialize (leqsim_live_var leqsim_addr x a sigma rho_cloK z asigma arho_cloK H0 H2 H10); crush.
    exists x0; crush; eapply ClosureVarALiveValueK; crush.
Qed.

(* If a binding is live via continuation variables then the corresponding abstract binding is live. *)
Lemma leqsim_live_varK :
  forall indexOf leqsim_addr leqsim_addrProxy x a
         sigmaP sigma k aP
         asigmaP asigma aaP,
    live_varK indexOf sigmaP sigma k aP x a ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_store leqsim_addr sigma asigma ->
    map.get leqsim_addrProxy aP = Some aaP ->
    exists aa,
      map.get leqsim_addr a = Some aa /\
      alive_varK indexOf asigmaP asigma k aaP x aa.
Proof.
  crush; eapply leqsim_live_varK_valueK; crush.
Qed.

(* If a binding is live via continuation values then the corresponding abstract binding is live. *)
Lemma leqsim_live_valueK :
  forall indexOf leqsim_addr leqsim_addrProxy x a 
         sigmaP sigma c aP
         asigmaP asigma ac aaP,
    live_valueK indexOf sigmaP sigma c aP x a ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_valueK leqsim_addr c ac ->
    map.get leqsim_addrProxy aP = Some aaP ->
    exists aa,
      map.get leqsim_addr a = Some aa /\
      alive_valueK indexOf asigmaP asigma ac aaP x aa.
Proof.
  crush; eapply leqsim_live_varK_valueK; crush.
Qed.

(* If a binding is live via a list of continuation values then the corresponding abstract binding is live. *)
Lemma leqsim_live_valueKs :
  forall indexOf leqsim_addr leqsim_addrProxy x a
         sigmaP sigma cs aP
         asigmaP asigma acs aaP,
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_store leqsim_addr sigma asigma ->
    List.fold_right (fun (c : valueK) (acc : Prop) => live_valueK indexOf sigmaP sigma c aP x a \/ acc) False cs ->
    leqsim_valueKs leqsim_addr cs acs ->
    map.get leqsim_addrProxy aP = Some aaP ->
    exists aa,
      map.get leqsim_addr a = Some aa /\
      List.fold_right (fun (ac : avalueK) (acc : Prop) => alive_valueK indexOf asigmaP asigma ac aaP x aa \/ acc) False acs.
Proof.
  crush. 
  induction H2; crush; simpl in *; crush; try contradiction.
  destruct H1.
  - specialize (leqsim_live_valueK indexOf leqsim_addr leqsim_addrProxy x a sigmaP sigma c_i aP asigmaP asigma ac_i aaP H1 H H0 H4 H3); crush.
    exists x0; crush.
    left; crush.
  - specialize (IHleqsim_valueKs H H0 H1); crush.
    eexists x0; crush.
    right; crush.
Qed.

(* The primary liveness relation lemma. If a binding is live, it's corresponding abstract binding is live. *)
Lemma leqsim_live : forall indexOf leqsim_addr leqsim_addrProxy
                           sigma sigmaP ds cs aP
                           asigma asigmaP ads acs aaP,
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_values leqsim_addr ds ads ->
    leqsim_valueKs leqsim_addr cs acs ->
    map.get leqsim_addrProxy aP = Some aaP ->
    leqsim_bindings leqsim_addr 
                    (live indexOf sigma sigmaP ds cs aP)
                    (alive indexOf asigma asigmaP ads acs aaP).
Proof.
  crush; constructor; crush. 
  unfold live in H4; unfold alive; crush.
  destruct H4.
  - specialize (leqsim_live_values leqsim_addr x a sigma ds asigma ads H H4 H1); crush.
    exists x0; crush; left; crush.
  - specialize (leqsim_live_valueKs indexOf leqsim_addr leqsim_addrProxy x a sigmaP sigma cs aP asigmaP asigma acs aaP H0 H H4 H2 H3); crush.
    exists x0; crush; right; crush.
Qed.

(* The concrete and abstract localBindings functions give reulated results. *)
Lemma leqsim_localBindings : forall boundVars leqsim_addr e rho arho,
    leqsim_env leqsim_addr rho arho ->
    leqsim_bindings leqsim_addr (localBindings boundVars e rho) (alocalBindings boundVars e arho).
Proof. 
  crush; constructor; crush. 
  unfold localBindings in *; unfold alocalBindings in *; crush.
  destruct H.
  specialize (H x a H0); crush.
  exists x0; crush.
Qed.
