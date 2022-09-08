
Require Import coqutil.Map.Interface.
Definition map := map.map.
Require Import Ensembles.

Require Import common.Util.

Require Import cps.CPS.
Require Import cps.ConcreteSemantics.
Require Import cps.AbstractSemantics.
Require Import cps.SimulationRelation.
Require Import cps.Lemmas.

(* The initial states are related by the simulation relation leqsim.
 *)

Theorem leqsim_initial : forall e,
    let aP0 := @AddrProxy.fresh proxy map.empty in
    let aaP0 := AAddrProxy.alloc e in
    leqsim_state map.empty (map.put map.empty aP0 aaP0) (initial e) (ainitial e).
Proof. 
  intro. unfold initial; unfold ainitial.
  apply State_Rel; map_crush; break_leqsim_goal; map_crush.
  - case (AddrProxy.dec (@AddrProxy.fresh ConcreteSemantics.proxy map.empty) aP); map_crush. 
    exists (Singleton aproxy AUnknownProxy); map_crush.
    break_leqsim_goal; exists AUnknownProxy; crush; map_crush; try (apply In_singleton; crush).
    break_leqsim_goal; crush.
Qed.

(* Simulation is preserved by transition:
   Let s --> s' be concrete states and a be an abstract state such that s \leqsim a. 
   Then there exists some abstract state a' such that a --> a' and s' \leqsim a'.

   s   \leqsim   a

   |             |
   |             | exists
   |             |
   v             v

   s'  \leqsim   a'

   The simulation after transition occurs extended address-relation
   maps, since new concrete addresses may be introduced, and those
   need to be related to the corresponding created abstract addresses.
   Importantly, these extended address maps are equal on the domain of 
   the unextended maps, meaning that any updates to simulation don't
   interfere with the previous state.
   
   The proof is fairly straight-forward, decomposing the state
   transition relation (one case for calls, one for continuation
   calls) and then pushing the simulation lemmas from Lemmas.v through
   to derive the abstract state transition.

   The proofs of simulation hold for any choice of implementation of
   the auxiliary maps indexOf and boundVars, since the concrete and
   abstract semantics use them in the same way.
 *)

Theorem leqsim_rel : forall indexOf boundVars
                           leqsim_addr leqsim_addrProxy
                           state state' astate,
    leqsim_state leqsim_addr leqsim_addrProxy state astate ->
    trans indexOf boundVars state state' -> 
    exists astate' leqsim_addr' leqsim_addrProxy',
           atrans indexOf boundVars astate astate' /\
           (forall a aa, map.get leqsim_addr a = Some aa ->
                         map.get leqsim_addr' a = Some aa) /\
           (forall aP aaP, map.get leqsim_addrProxy aP = Some aaP ->
                           map.get leqsim_addrProxy' aP = Some aaP) /\
           leqsim_state leqsim_addr' leqsim_addrProxy' state' astate'.
Proof.
  crush.
  break_leqsim H.
  cases e; crush.
  - inversion H0; crush.
    specialize (leqsim_eval leqsim_addr a rho sigma arho asigma (Closure x ks body rho_clo) H H2 H18); crush.
    specialize (leqsim_eval leqsim_addr a0 rho sigma arho asigma d_arg H H2 H20); crush.

    assert (leqsim_proxy leqsim_addr leqsim_addrProxy
                         (Proxy (Call a a0 l) rho (List.map (evalK indexOf rho) l) aP)
                         (AProxy (Call a a0 l) arho (List.map (aevalK indexOf arho) l) aaP))
      by (constructor; crush; apply leqsim_evalKs; crush).

    specialize (leqsim_popProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP
                                (Proxy (Call a a0 l) rho (List.map (evalK indexOf rho) l) aP)
                                proxy'
                                (AProxy (Call a a0 l) arho (List.map (aevalK indexOf arho) l) aaP)
                                H3 H11 H21); crush.

    revert H0; inversion H8; crush.
    eexists.
    exists (map.put leqsim_addr (Addr.fresh sigma) (AAddr.alloc x)).
    exists (map.put leqsim_addrProxy (AddrProxy.fresh sigmaP) (AAddrProxy.alloc body)).

    assert (map.get leqsim_addr (Addr.fresh sigma) = None) as fresh
        by (eapply H5; apply (Addr.freshP sigma)).
    assert (map.get leqsim_addrProxy (AddrProxy.fresh sigmaP) = None) as freshProxy
        by (eapply H6; apply (AddrProxy.freshP sigmaP)).
    crush.

    + eapply ATransCall; eauto; crush. 
    + apply update_leqsim_addr; map_crush. 
    + apply update_leqsim_addrProxy; map_crush.
    + apply State_Rel; map_crush; try apply H5; try apply H6; crush. 
      ++ apply leqsim_env_ext; crush.
      ++ apply leqsim_store_ext; crush.
      ++ apply leqsim_storeProxy_ext; map_crush.
         apply leqsim_storeProxy_extProxy; map_crush.
         apply leqsim_proxies_single; map_crush.
      ++ eapply leqsim_checkR; crush;
           try eapply leqsim_checkS; crush;
             try eapply leqsim_live; crush;
               try eapply leqsim_poppedBindings_proxy; crush;
                 try eapply leqsim_evalKs; crush;
                   try eapply leqsim_localBindings; crush;
                     try (constructor; try eapply leqsim_value_single; crush; constructor; crush; constructor).
  - inversion H0; crush.
    specialize (leqsim_eval leqsim_addr a0 rho sigma arho asigma d_arg H H2 H17); crush.
    specialize (leqsim_evalK leqsim_addr indexOf rho arho a H); crush.
    specialize (leqsim_findCloK leqsim_addr leqsim_addrProxy sigmaP asigmaP (evalK indexOf rho a) (aevalK indexOf arho a) aP aaP (ClosureK x body rho_cloK) aP' H3 H1 H9 H18); crush.
    inversion H11; crush.

    eexists.

    exists (map.put leqsim_addr (Addr.fresh sigma) (AAddr.alloc x)).
    exists leqsim_addrProxy.

    assert (map.get leqsim_addr (Addr.fresh sigma) = None) as fresh
        by (eapply H5; apply (Addr.freshP sigma)).

    crush.
    + eapply ATransReturn; eauto. 
    + apply update_leqsim_addr; map_crush. 
    + apply State_Rel; map_crush; try apply H5; try apply H6; crush. 
      ++ apply leqsim_env_ext; crush.
      ++ apply leqsim_store_ext; crush.
      ++ apply leqsim_storeProxy_ext; map_crush.
      ++ eapply leqsim_checkR; crush;
          try eapply leqsim_checkS; crush;
            try eapply leqsim_live; crush;
              try eapply leqsim_poppedBindings_valueK; crush;
                try eapply leqsim_localBindings; crush;
                  try (constructor; try eapply leqsim_value_single; crush; constructor);
                  try (constructor; try eapply leqsim_aevalK; crush; constructor).
Qed.


