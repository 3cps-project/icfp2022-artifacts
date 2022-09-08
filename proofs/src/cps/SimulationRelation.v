
(* This file contains the definition of the simulation relation
   between concrete and abstract states.

   We do this by defining a simulation between each component of the
   states - environments, stores, etc. These definitions each rely on
   maps that relate concrete addresses to abstract addresses, and
   similar for proxy addresses.
   
   The idea is that as the abstract semantics simulates the concrete
   semantics, these maps are inductively constructed to track the
   relation between the states.
   
*)

Require Import coqutil.Map.Interface.
Definition map := map.map.
Require Import Ensembles.

Require Import cps.CPS.
Require Import cps.SemanticsCommon.
Require Import cps.ConcreteSemantics.
Require Import cps.AbstractSemantics.


(* Maps relating concrete addresses to abstract addresses *)
Definition leqsim_addr : map.map addr aaddr := Addr.map aaddr.
Definition leqsim_addr_proofs : map.ok leqsim_addr := Addr.map_ok aaddr.

(* Maps relating concrete proxy addresses to abstract proxy addresses *)
Definition leqsim_addrProxy : map.map addrProxy aaddrProxy := AddrProxy.map aaddrProxy.
Definition leqsim_addrProxy_proofs : map.ok leqsim_addrProxy := AddrProxy.map_ok aaddrProxy.

(* Simulation between environments.
   This holds if every entry in the concrete environment has a
   correponding entry in the abstract environment. *)
Inductive leqsim_env : leqsim_addr -> env -> aenv -> Prop :=
| Env_Rel : forall leqsim_addr rho arho,
    (forall x a,
        map.get rho x = Some a ->
        exists aa,
          (map.get arho x = Some aa) /\
          (map.get leqsim_addr a = Some aa)) ->
    leqsim_env leqsim_addr rho arho.

(* Simulation between values. This holds if there exists an abstract
   closure in the abstract value that is related to the concrete closure - 
   it must have the same lambda and a related environment. *)
Inductive leqsim_value : leqsim_addr -> value -> avalue -> Prop :=
| Value_Rel : forall leqsim_addr x ks body rho_clo ad,
    (exists rho_aclo,
        In aclo ad (AClosure x ks body rho_aclo) /\
        leqsim_env leqsim_addr rho_clo rho_aclo) ->
    leqsim_value leqsim_addr (Closure x ks body rho_clo) ad.

(* Simulation between continuation values. 
   Index values are only related to Index values with the same index, and
   continuation closures are only related to abstract continuation
   closures with the same continuation lambda and related environment. *)
Inductive leqsim_valueK : leqsim_addr -> valueK -> avalueK -> Prop :=
| Index_Rel : forall leqsim_addr i,
    leqsim_valueK leqsim_addr (Index i) (AIndex i)
| ClosureK_Rel : forall leqsim_addr x body rho_cloK arho_cloK,
    (leqsim_env leqsim_addr rho_cloK arho_cloK) ->
    leqsim_valueK leqsim_addr (ClosureK x body rho_cloK) (AClosureK x body arho_cloK).

(* Simulation between lists of continuation values. These lists must
   have the same length and be related at each index. *)
Inductive leqsim_valueKs : leqsim_addr -> list valueK -> list avalueK -> Prop :=
| ListValueK_Rel_nil : forall leqsim_addr, leqsim_valueKs leqsim_addr nil nil
| ListValueK_Rel_cons : forall leqsim_addr c_i cs ac_i acs,
    leqsim_valueKs leqsim_addr cs acs ->
    leqsim_valueK leqsim_addr c_i ac_i ->
    leqsim_valueKs leqsim_addr (cons c_i cs) (cons ac_i acs).

(* Simulation between proxies. The unknown proxies are only related to each other, 
   and a concrete proxy is related to an abstract proxy when their components are related. *)
Inductive leqsim_proxy : leqsim_addr -> leqsim_addrProxy -> proxy -> aproxy -> Prop :=
| Proxy_Rel : forall leqsim_addr leqsim_addrProxy e rho cs aP arho acs aaP,
    leqsim_env leqsim_addr rho arho ->
    leqsim_valueKs leqsim_addr cs acs ->
    (map.get leqsim_addrProxy aP = Some aaP) ->
    leqsim_proxy leqsim_addr leqsim_addrProxy (Proxy e rho cs aP) (AProxy e arho acs aaP)
| UnknownProxy_Rel : forall leqsim_addr leqsim_addrProxy,
    leqsim_proxy leqsim_addr leqsim_addrProxy UnknownProxy AUnknownProxy.

(* Simulation between a concrete proxy and a set of abstract proxies.
   The concrete proxy must have a related abstract proxy in the set of abstract proxies. *)
Inductive leqsim_proxies : leqsim_addr -> leqsim_addrProxy -> proxy -> aproxies -> Prop :=
| Proxies_Rel : forall leqsim_addr leqsim_addrProxy proxy aproxies,
    (exists aproxy,
        In _ aproxies aproxy /\
        leqsim_proxy leqsim_addr leqsim_addrProxy proxy aproxy) ->
    leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies.

(* Simulation between stores. Stores are related if each entry in the
   concrete store has a corresponding related entry in the abstract store. *)
Inductive leqsim_store : leqsim_addr -> store -> astore -> Prop :=
| Store_Rel : forall leqsim_addr sigma asigma,
    (forall a aa d,
        map.get sigma a = Some d ->
        map.get leqsim_addr a = Some aa ->
        exists ad,
          (map.get asigma aa = Some ad) /\
          (leqsim_value leqsim_addr d ad)) ->
    leqsim_store leqsim_addr sigma asigma.
        
(* Simulation between proxy stores. Proxy stores are related if each entry in the
   concrete proxy store has a corresponding related entry in the abstract store. *)
Inductive leqsim_storeProxy : leqsim_addr -> leqsim_addrProxy -> storeProxy -> astoreProxy -> Prop :=
| StoreProxy_Rel : forall leqsim_addr leqsim_addrProxy sigmaP asigmaP,
    (forall aP aaP proxy,
        map.get sigmaP aP = Some proxy ->
        map.get leqsim_addrProxy aP = Some aaP ->
        exists aproxies,
          (map.get asigmaP aaP = Some aproxies) /\
          (leqsim_proxies leqsim_addr leqsim_addrProxy proxy aproxies)) ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP.

(* Annotations sets are related if the set for the abstract is a subset of that of the concrete. *)
Inductive leqsim_annotationSet : annotationSet -> annotationSet -> Prop :=
| AnnotationSet_Rel : forall an an', Included _ an' an -> leqsim_annotationSet an an'.

(* States are related if the share the same program term and are related at each component. *)
Inductive leqsim_state : leqsim_addr -> leqsim_addrProxy -> state -> astate -> Prop :=
| State_Rel : forall leqsim_addr leqsim_addrProxy
                e rho aP sigma sigmaP an
                    arho aaP asigma asigmaP an',
    leqsim_env leqsim_addr rho arho ->
    map.get leqsim_addrProxy aP = Some aaP ->
    leqsim_store leqsim_addr sigma asigma ->
    leqsim_storeProxy leqsim_addr leqsim_addrProxy sigmaP asigmaP ->
    leqsim_annotationSet an an' -> 
    (forall a, map.get leqsim_addr a = None <-> map.get sigma a = None) ->
    (forall aP, map.get leqsim_addrProxy aP = None <-> map.get sigmaP aP = None) ->
    leqsim_state leqsim_addr leqsim_addrProxy
           (State e rho aP sigma sigmaP an)
           (AState e arho aaP asigma asigmaP an').

(* Sets of bindings are related if each concrete binding has a corresponding abstract binding *)
Inductive leqsim_bindings : leqsim_addr -> (var -> addr -> Prop) -> (var -> aaddr -> Prop) -> Prop :=
| Bindings_Rel : forall leqsim_addr (bindings : var -> addr -> Prop) (abindings : var -> aaddr -> Prop),
    (forall x a,
        bindings x a ->
        exists aa,
          map.get leqsim_addr a = Some aa /\
          abindings x aa) ->
    leqsim_bindings leqsim_addr bindings abindings.
