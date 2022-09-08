
(* This file contains the definitions and transition relation for 
   the computable "abstract" semantics.
 *)

Require Import coqutil.Map.Interface.
Definition map := map.map.
Require Import FunInd.
Require Import common.Common.
Require Import Ensembles.

Require Import cps.CPS.
Require Import cps.SemanticsCommon.


(* Abstract addresses *)
Module AAddr : FIN Var.
  Definition t := Var.t.
  Definition eq := Var.eq.
  Definition dec := Var.dec.

  Definition map := Var.map.
  Definition map_ok := Var.map_ok.

  Definition ltb := Var.ltb.
  Definition ltb_antirefl := Var.ltb_antirefl.
  Definition ltb_trans := Var.ltb_trans.
  Definition ltb_total := Var.ltb_total.

  Function alloc (x : Var.t) := x.
End AAddr.

(* Abstract proxy addresses *)
Module AAddrProxy : FIN CPS.Term.

  Definition t := CPS.Term.t.
  Definition eq := CPS.Term.eq.
  Definition dec := CPS.Term.dec.

  Definition map := CPS.Term.map.
  Definition map_ok := CPS.Term.map_ok.

  Definition ltb := CPS.term_ltb.
  Definition ltb_antirefl := CPS.term_ltb_antirefl.
  Definition ltb_trans := CPS.term_ltb_trans.
  Definition ltb_total := CPS.term_ltb_total.

  Function alloc (x : CPS.Term.t) := x.
End AAddrProxy.

Definition aaddr := AAddr.t.
Definition aaddrProxy := AAddrProxy.t.

(* Abstract environments *)
Definition aenv : map.map var aaddr := Var.map aaddr.
Definition aenv_proofs : map.ok aenv := Var.map_ok aaddr.

(* Abstract values, i.e. sets of abstract closures *)
Inductive aclo := AClosure : var -> list varK -> term -> aenv -> aclo.
Definition avalue := Ensemble aclo.

(* Abstract continuation values *)
Inductive avalueK := AClosureK : var -> term -> aenv -> avalueK
                   | AIndex : nat -> avalueK.

(* Abstract proxies. 
   We add an "unknown proxy", which essentially represents the HALT continuation *)
Inductive aproxy := AProxy : term -> aenv -> list avalueK -> aaddrProxy -> aproxy
                  | AUnknownProxy : aproxy.

Definition aproxies := Ensemble aproxy.

(* Abstract stores *)
Definition astore : map aaddr avalue := AAddr.map avalue.
Definition astore_proofs : map.ok astore := AAddr.map_ok avalue.

(* Abstract proxy stores *)
Definition astoreProxy : map aaddrProxy aproxies := AAddrProxy.map aproxies.
Definition astoreProxy_proofs : map.ok astoreProxy := AAddrProxy.map_ok aproxies.

(* Definition of the "join" operator for abstract values and proxies, which is simply the union *)
Definition join_avalue : avalue -> avalue -> avalue := Union aclo.
Definition join_aproxies : aproxies -> aproxies -> aproxies := Union aproxy.

Definition add_join (asigma : astore) (aa : aaddr) (ad : avalue) :=
  match map.get asigma aa with
  | Some ad' => map.put asigma aa (join_avalue ad ad')
  | None => map.put asigma aa ad
  end.
Definition add_joinP (asigmaP : astoreProxy) (aaP : aaddrProxy) (aproxies : aproxies) :=
  match map.get asigmaP aaP with
  | Some aproxies' => map.put asigmaP aaP (join_aproxies aproxies aproxies')
  | None => map.put asigmaP aaP aproxies
  end.


(* Abstract states *)
Inductive astate := AState : term -> aenv -> aaddrProxy -> astore -> astoreProxy -> annotationSet -> astate.

(* Abstract atom evaluation *)
Function aeval (ae : atom) (arho : aenv) (asigma : astore) : option avalue :=
  match ae with
  | Var x => option_bind (fun aa => map.get asigma aa) (map.get arho x)
  | Lam x ks body => Some (Singleton _ (AClosure x ks body arho))
  end.

(* Abstract continuation atom evaluation *)
Function aevalK (indexOf : varK -> nat) (arho : aenv) (q : atomK) : avalueK :=
  match q with
  | VarK k => AIndex (indexOf k)
  | LamK x body => AClosureK x body arho
  end.

(* Abstract proxy auxiliary functions *)
Inductive afindCloK : astoreProxy -> avalueK -> aaddrProxy -> avalueK -> aaddrProxy -> Prop :=
| ImmFindACloK : forall asigmaP x body aenv aaP,
    afindCloK asigmaP (AClosureK x body aenv) aaP (AClosureK x body aenv) aaP
| ChainFindACloK : forall asigmaP i aaP ac_res aaP_res
                         e arho acs ac_i aaP' aproxies,
    
    map.get asigmaP aaP = Some aproxies->
    In _ aproxies (AProxy e arho acs aaP') ->
    nth_opt i acs = Some ac_i->
    afindCloK asigmaP ac_i aaP' ac_res aaP_res ->
    afindCloK asigmaP (AIndex i) aaP ac_res aaP_res
.

Inductive abinding := ABinding : var -> aaddr -> abinding.
Definition abindings := Ensemble abinding.

Inductive apoppedBindings_valueK : (term -> aenv -> var -> aaddr -> Prop) -> astoreProxy -> avalueK -> aaddrProxy -> (var -> aaddr -> Prop) -> var -> aaddr -> Prop :=
| ImmPoppedABindings_valueK : forall alocalBindings asigmaP i aaP x aa (abindings_local : var -> aaddr -> Prop),
    abindings_local x aa -> 
    apoppedBindings_valueK alocalBindings asigmaP (AIndex i) aaP abindings_local x aa
| ChainPoppedABindings_valueK : forall alocalBindings asigmaP i aaP x aa abindings_local
                                    e arho acs aaP' ac_i aproxies,
    map.get asigmaP aaP = Some aproxies->
    In _ aproxies (AProxy e arho acs aaP') ->
    nth_opt i acs = Some ac_i->
    apoppedBindings_valueK alocalBindings asigmaP ac_i aaP' (alocalBindings e arho) x aa ->
    apoppedBindings_valueK alocalBindings asigmaP (AIndex i) aaP abindings_local x aa
.

Inductive apopProxy : astoreProxy -> aproxy -> aproxy -> Prop :=
| ImmPopAProxy : forall asigmaP e arho acs aaP,
    let isCloK ac_i := match ac_i with
                      | AClosureK _ _ _ => True
                      | _ => False
                      end in
    listExists isCloK acs ->
    apopProxy asigmaP (AProxy e arho acs aaP) (AProxy e arho acs aaP)
| ChainPopAProxy : forall asigmaP e arho idxs aaP e' arho' acs' aaP' acs'_fixed aproxy_res aproxies,
    map.get asigmaP aaP = Some aproxies->
    In _ aproxies (AProxy e' arho' acs' aaP') ->
    select_idxs acs' idxs = Some acs'_fixed ->
    apopProxy asigmaP (AProxy e' arho' acs'_fixed aaP') aproxy_res ->
    apopProxy asigmaP (AProxy e arho (List.map AIndex idxs) aaP) aproxy_res
.

Inductive apoppedBindings_proxy : (term -> aenv -> var -> aaddr -> Prop) -> astoreProxy -> aproxy -> var -> aaddr -> Prop :=
| ImmPoppedABindings_proxy : forall (alocalBindings : term -> aenv -> var -> aaddr -> Prop) asigmaP e arho idxs aaP e' arho' acs' aaP' x aa aproxies,
    map.get asigmaP aaP = Some aproxies->
    In _ aproxies (AProxy e' arho' acs' aaP') ->
    alocalBindings e arho x aa ->
    apoppedBindings_proxy alocalBindings asigmaP (AProxy e arho (List.map AIndex idxs) aaP) x aa
| ChainPoppedABindings_proxy : forall alocalBindings asigmaP e arho idxs aaP e' arho' acs' aaP' acs'_fixed x aa aproxies,
    map.get asigmaP aaP = Some aproxies->
    In _ aproxies (AProxy e' arho' acs' aaP') ->
    select_idxs acs' idxs = Some acs'_fixed ->
    apoppedBindings_proxy alocalBindings asigmaP (AProxy e' arho' acs'_fixed aaP') x aa ->
    apoppedBindings_proxy alocalBindings asigmaP (AProxy e arho (List.map AIndex idxs) aaP) x aa
.

(* Abstract liveness *)
Inductive alive_var : astore -> aenv -> var -> var -> aaddr -> Prop :=
| ImmALiveVar : forall asigma arho x aa,
    map.get arho x = Some aa ->
    alive_var asigma arho x x aa
| ChainALiveVar : forall asigma arho y x aa ad,
    aeval (Var y) arho asigma = Some ad ->
    alive_value asigma ad x aa ->
    alive_var asigma arho y x aa
with alive_value : astore -> avalue -> var -> aaddr -> Prop :=
| ChainALiveValue : forall asigma y ks body arho_clo z x aa ad, 
    free_atom (Lam y ks body) z ->
    alive_var asigma arho_clo z x aa ->
    In _ ad (AClosure y ks body arho_clo) ->
    alive_value asigma ad x aa
.

Inductive alive_varK : (varK -> nat) -> astoreProxy -> astore -> varK -> aaddrProxy -> var -> aaddr -> Prop :=
| ALiveVarK : forall indexOf asigmaP asigma k aaP x aa,
    alive_valueK indexOf asigmaP asigma (AIndex (indexOf k)) aaP x aa ->
    alive_varK indexOf asigmaP asigma k aaP x aa
with alive_valueK : (varK -> nat) -> astoreProxy -> astore -> avalueK -> aaddrProxy -> var -> aaddr -> Prop :=
| IndexALiveValueK : forall indexOf asigmaP asigma aaP i x aa e' arho' acs' aaP' ac' aproxies,
    map.get asigmaP aaP = Some aproxies ->
    In _ aproxies (AProxy e' arho' acs' aaP') ->
    nth_opt i acs' = Some ac'->
    alive_valueK indexOf asigmaP asigma ac' aaP' x aa ->
    alive_valueK indexOf asigmaP asigma (AIndex i) aaP x aa
| ClosureVarKALiveValueK : forall indexOf asigmaP asigma aaP y body arho_cloK x aa k,
    freeK_atomK (LamK y body) k ->
    alive_varK indexOf asigmaP asigma k aaP x aa ->
    alive_valueK indexOf asigmaP asigma (AClosureK y body arho_cloK) aaP x aa
| ClosureVarALiveValueK : forall indexOf asigmaP asigma aaP y body arho_cloK x aa z,
    free_atomK (LamK y body) z ->
    alive_var asigma arho_cloK z x aa ->
    alive_valueK indexOf asigmaP asigma (AClosureK y body arho_cloK) aaP x aa
.


Definition alive (indexOf : varK -> nat) (asigma : astore) (asigmaP : astoreProxy) (ads : list avalue) (acs : list avalueK) (aaP : aaddrProxy) (x : var) (aa : aaddr) : Prop := 
  let alive1 := List.fold_right (fun ad acc => alive_value asigma ad x aa \/ acc) False ads in
  let alive2 := List.fold_right (fun ac acc => alive_valueK indexOf asigmaP asigma ac aaP x aa \/ acc) False acs in
  alive1 \/ alive2
.

(* Abtract local bindings associated with a CPS term *)
Definition alocalBindings (boundVars : term -> list var) (e : term) (arho : aenv) (x : var) (aa : aaddr) : Prop :=
  map.get arho x = Some aa /\ listExists (fun y => x = y) (boundVars e).


(* Abstract stack extent check *)
Definition acheckS (alive : var -> aaddr -> Prop) (apopped : var -> aaddr -> Prop) (an : annotationSet) : annotationSet :=
  let kill anno := match anno with
                   | Anno x ExtentS => exists aa, alive x aa /\ apopped x aa
                   | Anno x ExtentR => False
                   end in
  Setminus annotation an kill.

(* Abstract register extent check *)
Definition acheckR (x : var) (alive : var -> aaddr -> Prop) (an : annotationSet) : annotationSet :=
  let kill anno := match anno with
                   | Anno y ExtentR => x = y /\ exists aa, alive x aa
                   | Anno y ExtentS => False
                   end in
  Setminus annotation an kill.

(* Initial abstract state We use the abstract unknown proxy initially, which sets up the halt value. *)
Definition ainitial (e : term) : astate :=
  let aenv0 := map.empty in
  let asigma0 := map.empty in
  let aaP0 := (@AAddrProxy.alloc e) in
  let asigmaP0 := (map.put map.empty aaP0 (Singleton _ AUnknownProxy)) in
  let an0 := (initialAnnotationSet e) in
  AState e aenv0 aaP0 asigma0 asigmaP0 an0.

(* Abstract state transition. This is parameterized over the indexOf
   and boundVars functions - simulation between the concrete and
   abstract holds no matter what the definition for these functions
   are, as long as they are the same between the two. *)
Inductive atrans : (varK -> nat) -> (term -> list var) -> astate -> astate -> Prop :=
| ATransCall : forall indexOf boundVars f arg qs arho aaP asigma asigmaP
                     x body arho_clo ad_f ad_arg aproxy' an ks,

    aeval f arho asigma = Some ad_f ->
    In _ ad_f (AClosure x ks body arho_clo) ->
    aeval arg arho asigma = Some ad_arg ->
    let aa := AAddr.alloc x in
    let arho' := map.put arho_clo x aa in
    let asigma' := add_join asigma aa ad_arg in
    
    let acs := List.map (aevalK indexOf arho) qs in
    let aproxy_call := AProxy (Call f arg qs) arho acs aaP in
    apopProxy asigmaP aproxy_call aproxy' ->
    let aaP' := AAddrProxy.alloc body in
    let asigmaP' := add_joinP asigmaP aaP' (Singleton _ aproxy') in

    let ads := (cons (Singleton _ (AClosure x ks body arho_clo)) (cons ad_arg nil)) in
    let abindings_live := alive indexOf asigma asigmaP ads acs aaP in
                                         
    let abindings_popped := apoppedBindings_proxy (alocalBindings boundVars) asigmaP aproxy_call in
    let an' := acheckS abindings_live abindings_popped an in
    let an'' := acheckR x abindings_live an' in

    atrans indexOf boundVars 
          (AState (Call f arg qs) arho aaP asigma asigmaP an)
          (AState body arho' aaP' asigma' asigmaP' an'')

| ATransReturn : forall indexOf boundVars q arg arho aaP asigma asigmaP ad_arg
                       arho_cloK aaP' x body an,
    aeval arg arho asigma = Some ad_arg ->
    let ac := aevalK indexOf arho q in
    afindCloK asigmaP ac aaP (AClosureK x body arho_cloK) aaP' ->
    let aa := AAddr.alloc x in
    let arho' := map.put arho_cloK x aa in
    let asigma' := add_join asigma aa ad_arg in

    let abindings_live := alive indexOf asigma asigmaP (cons ad_arg nil) (cons ac nil) aaP in
    let abindings_local := alocalBindings boundVars (CallK q arg) arho in
    let abindings_popped := apoppedBindings_valueK (alocalBindings boundVars) asigmaP ac aaP abindings_local in
    let an' := acheckS abindings_live abindings_popped an in
    let an'' := acheckR x abindings_live an' in

    atrans indexOf boundVars 
          (AState (CallK q arg) arho aaP asigma asigmaP an)
          (AState body arho' aaP' asigma' asigmaP an'')
.
