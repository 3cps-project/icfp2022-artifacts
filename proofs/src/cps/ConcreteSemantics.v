
(* This file contains the definitions and transition relation for 
   the concrete "collecting" semantics.
 *)

Require Import coqutil.Map.Interface.
Definition map := map.map.
Require Import FunInd.
Require Import common.Common.
Require Import Ensembles.

Require Import cps.CPS.
Require Import cps.SemanticsCommon.

Module Addr : INF := Nat_Inf.
Module AddrProxy : INF := Nat_Inf.

(* Concrete addresses *)
Definition addr := Addr.t.

(* Concrete proxy addresses *)
Definition addrProxy := AddrProxy.t.

(* Concrete environments *)
Definition env : map.map var addr := Var.map addr.
Definition env_proofs : map.ok env := Var.map_ok addr.

(* Concrete values *)
Inductive value := Closure : var -> list varK -> term -> env -> value.

(* Concrete continuation values *)
Inductive valueK := ClosureK : var -> term -> env -> valueK
                  | Index : nat -> valueK.

(* Concrete proxies
   We add an "unknown proxy", which essentially represents the HALT continuation *)
Inductive proxy := Proxy : term -> env -> list valueK -> addrProxy -> proxy
                  | UnknownProxy : proxy.

(* Concrete stores *)
Definition store : map addr value := Addr.map value.
Definition store_proofs : map.ok store := Addr.map_ok value.

(* Concrete proxy stores *)
Definition storeProxy : map addrProxy proxy := AddrProxy.map proxy.
Definition storeProxy_proofs : map.ok storeProxy := AddrProxy.map_ok proxy.

(* Concrete states *)
Inductive state := State : term -> env -> addrProxy -> store -> storeProxy -> annotationSet -> state.

(* Concrete atom evaluation *)
Function eval (ae : atom) (rho : env) (sigma : store) : option value :=
  match ae with
  | Var x => option_bind (fun a => map.get sigma a) (map.get rho x)
  | Lam x ks body => Some (Closure x ks body rho)
  end.

(* Concrete continuation atom evaluation *)
Function evalK (indexOf : varK -> nat) (rho : env) (q : atomK) : valueK :=
  match q with
  | VarK k => Index (indexOf k)
  | LamK x body => ClosureK x body rho
  end.

Inductive binding := Binding : var -> addr -> binding.
(* Concrete sets of bindings *)
Definition bindings := Ensemble binding.

(* Concrete proxy auxiliary functions *)
Inductive findCloK : storeProxy -> valueK -> addrProxy -> valueK -> addrProxy -> Prop :=
| ImmFindCloK : forall sigmaP x body env aP,
    findCloK sigmaP (ClosureK x body env) aP (ClosureK x body env) aP
| ChainFindCloK : forall sigmaP i aP c_res aP_res
                         e rho cs c_i aP',
    map.get sigmaP aP = Some (Proxy e rho cs aP') ->
    nth_opt i cs = Some c_i ->
    findCloK sigmaP c_i aP' c_res aP_res ->
    findCloK sigmaP (Index i) aP c_res aP_res
.

Inductive poppedBindings_valueK : (term -> env -> var -> addr -> Prop) -> storeProxy -> valueK -> addrProxy -> (var -> addr -> Prop) -> var -> addr -> Prop :=
| ImmPoppedBindings_valueK : forall localBindings sigmaP i aP x a (bindings_local : var -> addr -> Prop),
    bindings_local x a -> 
    poppedBindings_valueK localBindings sigmaP (Index i) aP bindings_local x a
| ChainPoppedBindings_valueK : forall localBindings sigmaP i aP x a bindings_local
                                    e rho cs aP' c_i,
    map.get sigmaP aP = Some (Proxy e rho cs aP')->
    nth_opt i cs = Some c_i ->
    poppedBindings_valueK localBindings sigmaP c_i aP' (localBindings e rho) x a ->
    poppedBindings_valueK localBindings sigmaP (Index i) aP bindings_local x a
.

Inductive popProxy : storeProxy -> proxy -> proxy -> Prop :=
| ImmPopProxy : forall sigmaP e rho cs aP,
    let isCloK c_i := match c_i with
                      | ClosureK _ _ _ => True
                      | _ => False
                      end in
    listExists isCloK cs ->
    popProxy sigmaP (Proxy e rho cs aP) (Proxy e rho cs aP)
| ChainPopProxy : forall sigmaP e rho idxs aP e' rho' cs' aP' cs'_fixed proxy_res,
    map.get sigmaP aP = Some (Proxy e' rho' cs' aP') ->
    select_idxs cs' idxs = Some cs'_fixed ->
    popProxy sigmaP (Proxy e' rho' cs'_fixed aP') proxy_res ->
    popProxy sigmaP (Proxy e rho (List.map Index idxs) aP) proxy_res
.

Inductive poppedBindings_proxy : (term -> env -> var -> addr -> Prop) -> storeProxy -> proxy -> var -> addr -> Prop :=
| ImmPoppedBindings_proxy : forall (localBindings : term -> env -> var -> addr -> Prop) sigmaP e rho idxs aP e' rho' cs' aP' x a,
    map.get sigmaP aP = Some (Proxy e' rho' cs' aP') ->
    localBindings e rho x a ->
    poppedBindings_proxy localBindings sigmaP (Proxy e rho (List.map Index idxs) aP) x a
| ChainPoppedBindings_proxy : forall localBindings sigmaP e rho idxs aP e' rho' cs' aP' cs'_fixed x a,
    map.get sigmaP aP = Some (Proxy e' rho' cs' aP') ->
    select_idxs cs' idxs = Some cs'_fixed ->
    poppedBindings_proxy localBindings sigmaP (Proxy e' rho' cs'_fixed aP') x a ->
    poppedBindings_proxy localBindings sigmaP (Proxy e rho (List.map Index idxs) aP) x a
.

(* Concrete liveness *)
Inductive live_var : store -> env -> var -> var -> addr -> Prop :=
| ImmLiveVar : forall sigma rho x a,
    map.get rho x = Some a ->
    live_var sigma rho x x a
| ChainLiveVar : forall sigma rho y x a d,
    eval (Var y) rho sigma = Some d ->
    live_value sigma d x a ->
    live_var sigma rho y x a
with live_value : store -> value -> var -> addr -> Prop :=
| ChainLiveValue : forall sigma y ks body rho_clo z x a, 
    free_atom (Lam y ks body) z ->
    live_var sigma rho_clo z x a ->
    live_value sigma (Closure y ks body rho_clo) x a
.

Inductive live_varK : (varK -> nat) -> storeProxy -> store -> varK -> addrProxy -> var -> addr -> Prop :=
| LiveVarK : forall indexOf sigmaP sigma k aP x a,
    live_valueK indexOf sigmaP sigma (Index (indexOf k)) aP x a ->
    live_varK indexOf sigmaP sigma k aP x a
with live_valueK : (varK -> nat) -> storeProxy -> store -> valueK -> addrProxy -> var -> addr -> Prop :=
| IndexLiveValueK : forall indexOf sigmaP sigma aP i x a e' rho' cs' aP' c',
    map.get sigmaP aP = Some (Proxy e' rho' cs' aP')->
    nth_opt i cs' = Some c' ->
    live_valueK indexOf sigmaP sigma c' aP' x a ->
    live_valueK indexOf sigmaP sigma (Index i) aP x a
| ClosureVarKLiveValueK : forall indexOf sigmaP sigma aP y body rho_cloK x a k,
    freeK_atomK (LamK y body) k ->
    live_varK indexOf sigmaP sigma k aP x a ->
    live_valueK indexOf sigmaP sigma (ClosureK y body rho_cloK) aP x a
| ClosureVarLiveValueK : forall indexOf sigmaP sigma aP y body rho_cloK x a z,
    free_atomK (LamK y body) z ->
    live_var sigma rho_cloK z x a ->
    live_valueK indexOf sigmaP sigma (ClosureK y body rho_cloK) aP x a
.


Definition live (indexOf : varK -> nat) (sigma : store) (sigmaP : storeProxy) (ds : list value) (cs : list valueK) (aP : addrProxy) (x : var) (a : addr) : Prop := 
  let live1 := List.fold_right (fun d acc => live_value sigma d x a \/ acc) False ds in
  let live2 := List.fold_right (fun c acc => live_valueK indexOf sigmaP sigma c aP x a \/ acc) False cs in
  live1 \/ live2
.

(* Concrete local bindings associated with a CPS term *)
Definition localBindings (boundVars : term -> list var) (e : term) (rho : env) (x : var) (a : addr) : Prop :=
  map.get rho x = Some a /\ listExists (fun y => x = y) (boundVars e).

(* Concrete stack extent check *)
Definition checkS (live : var -> addr -> Prop) (popped : var -> addr -> Prop) (an : annotationSet) : annotationSet :=
  let kill anno := match anno with
                   | Anno x ExtentS => exists a, live x a /\ popped x a
                   | Anno x ExtentR => False
                   end in
  Setminus annotation an kill.

(* Concrete register extent check *)
Definition checkR (x : var) (live : var -> addr -> Prop) (an : annotationSet) : annotationSet :=
  let kill anno := match anno with
                   | Anno y ExtentR => x = y /\ exists a, live x a
                   | Anno y ExtentS => False
                   end in
  Setminus annotation an kill.

(* Initial concrete state. We use the unknown proxy initially, which sets up the halt value. *)
Definition initial (e : term) : state :=
  let env0 := map.empty in
  let sigma0 := map.empty in
  let aP0 := (@AddrProxy.fresh proxy map.empty) in
  let sigmaP0 := (map.put map.empty aP0 UnknownProxy) in
  let an0 := (initialAnnotationSet e) in
  State e env0 aP0 sigma0 sigmaP0 an0.

(* Concrete state transition. This is parameterized over the indexOf
   and boundVars functions - simulation between the concrete and
   abstract holds no matter what the definition for these functions
   are, as long as they are the same between the two. *)
Inductive trans : (varK -> nat) -> (term -> list var) -> state -> state -> Prop :=
| TransCall : forall indexOf boundVars f arg qs rho aP sigma sigmaP
                     x body rho_clo d_arg proxy' an ks,

    eval f rho sigma = Some (Closure x ks body rho_clo) ->
    List.length ks = List.length qs ->
    eval arg rho sigma = Some d_arg ->
    let a := Addr.fresh sigma in
    let rho' := map.put rho_clo x a in
    let sigma' := map.put sigma a d_arg in
    
    let cs := List.map (evalK indexOf rho) qs in
    let proxy_call := Proxy (Call f arg qs) rho cs aP in
    popProxy sigmaP proxy_call proxy' ->
    let aP' := AddrProxy.fresh sigmaP in
    let sigmaP' := map.put sigmaP aP' proxy' in

    let ds := (cons (Closure x ks body rho_clo) (cons d_arg nil)) in
    let bindings_live := live indexOf sigma sigmaP ds cs aP in
                                         
    let bindings_popped := poppedBindings_proxy (localBindings boundVars) sigmaP proxy_call in
    let an' := checkS bindings_live bindings_popped an in
    let an'' := checkR x bindings_live an' in

    trans indexOf boundVars 
          (State (Call f arg qs) rho aP sigma sigmaP an)
          (State body rho' aP' sigma' sigmaP' an'')

| TransReturn : forall indexOf boundVars q arg rho aP sigma sigmaP d_arg
                       rho_cloK aP' x body an,
    eval arg rho sigma = Some d_arg ->
    let c := evalK indexOf rho q in
    findCloK sigmaP c aP (ClosureK x body rho_cloK) aP' ->
    let a := Addr.fresh sigma in
    let rho' := map.put rho_cloK x a in
    let sigma' := map.put sigma a d_arg in

    let bindings_live := live indexOf sigma sigmaP (cons d_arg nil) (cons c nil) aP in
    let bindings_local := localBindings boundVars (CallK q arg) rho in
    let bindings_popped := poppedBindings_valueK (localBindings boundVars) sigmaP c aP bindings_local in
    let an' := checkS bindings_live bindings_popped an in
    let an'' := checkR x bindings_live an' in

    trans indexOf boundVars 
          (State (CallK q arg) rho aP sigma sigmaP an)
          (State body rho' aP' sigma' sigmaP an'')
.

