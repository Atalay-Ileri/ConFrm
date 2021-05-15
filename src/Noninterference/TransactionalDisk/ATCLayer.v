Require Import Framework FSParameters.
Require Export AuthenticationLayer TransactionCacheLayer.
Require AuthenticatedDiskLayer.
Require TransactionalDiskRefinement.
Require FileDiskNoninterference.
Import ListNotations.

Set Implicit Arguments.

Definition ATCCore :=  HorizontalComposition AuthenticationOperation TransactionCacheOperation.
Definition ATCLang := Build_Language ATCCore.

Import AuthenticatedDiskLayer.
Import TransactionalDiskRefinement.

Import Refinement.

Definition ATC_valid_state := fun s => FileDiskNoninterference.TC_valid_state (fst s) (snd s).
Definition ATC_related_states u exc := fun s1 s2 : ATCLang.(state) => FileDiskNoninterference.TC_related_states u exc (fst s1) (snd s1) (snd s2).

Definition ATC_reboot_list n := map (fun f => fun s: ATCLang.(state) => (fst s, f (snd s))) (transaction_cache_reboot_list n).

(*
Lemma compile_exec_simulation_finished:
forall u T (p: AuthenticatedDiskLang.(prog) T) o1 o2 (s1: AuthenticatedDiskLang.(state)) (s1a: ATCLang.(state)) s2a r,
exec ATCLang u o2 s1a (compile p) (Finished s2a r) ->
refines (snd s1a) (snd s1) ->
exists s2, 
exec AuthenticatedDiskLang u o1 s1 p (Finished s2 r) /\
refines (snd s2a) (snd s2).
Proof.
    induction p; simpl; intros.
    {
        destruct o.
        {
            destruct o.
            repeat invert_exec.
            eexists; simpl; split; eauto.
            repeat econstructor; eauto.
            admit.
            admit.
        }
        {
            invert_exec.
            destruct o; simpl in *.
            {
                edestruct abstract_oracles_exist_wrt_read.
            2: {
                instantiate (3:= 0); simpl.
                unfold transaction_cache_reboot_list; simpl.
                econstructor; eauto.
            }
            eauto.
            edestruct read_simulation.
            3: {
                instantiate (3:= 0); simpl.
                unfold transaction_cache_reboot_list; simpl.
                econstructor; eauto.
            }
            all: eauto.
            cleanup; simpl in *.
            unfold transactional_disk_reboot_list in *; simpl in *.
            invert_exec; simpl in *.
            eexists; split.
            repeat econstructor; eauto.

            econstructor.

            in H6.
        }
    }
*)


Fixpoint compile {O O1 O2} 
{L1: Language O1}
{LH1: Language (HorizontalComposition O O1)} 
{LH2: Language (HorizontalComposition O O2)}
(compile_core: forall T, O2.(operation) T -> L1.(prog) T) 
{T} (p: LH2.(prog) T) : LH1.(prog) T := 
match p with
| Op _ o =>
    match o with
    | P1 p1 => Op (HorizontalComposition O O1) (P1 p1)
    | P2 p2 => lift_L2 _ (compile_core _ p2)
    end
| Ret v => Ret v
| Bind p1 p2 => Bind (@compile _ _ _ _ LH1 LH2 compile_core  _ p1) 
(fun x => @compile _ _ _ _ LH1 LH2 compile_core _ (p2 x))
end.


Definition HC_valid_state {O1 O2} (valid_state: O1.(Core.state) -> O2.(Core.state) -> Prop) : (HorizontalComposition O1 O2).(Core.state) -> Prop := 
    fun s => valid_state (fst s) (snd s).

Definition HC_related_states {O1 O2} (related_states: O2.(Core.state) -> O2.(Core.state) -> Prop) := 
    fun s1 s2 : (HorizontalComposition O1 O2).(Core.state) => related_states (snd s1) (snd s2).

Definition HC_reboot_list {O1 O2} (get_reboot_list: nat -> list (O2.(Core.state) -> O2.(Core.state))) n := 
    map (fun f => fun s: (HorizontalComposition O1 O2).(Core.state) => (fst s, f (snd s))) (get_reboot_list n).

Lemma HC_exec_compiled_preserves_refinement_finished :
forall T (p2: L_abs.(prog) T) o1 s1 s1' r u,
    () ->
    
  (exists s2, refines s1 s2) ->
  L_imp.(exec) u o1 s1 (compile T p2) (Finished s1' r) ->
  (exists s2', refines s1' s2').

Fixpoint HC_oracle_refines {O O1 O2} {} {T} u -> L_imp.(state) -> L_abs.(prog) T -> (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> L_abs.(oracle) -> Prop;


Definition HC_Refinement O O1 O2 (L1: Language O1) (L2: Language O2)
(LI: Language (HorizontalComposition O O1)) 
(LA: Language (HorizontalComposition O O2))
(RC: CoreRefinement L1 O2) : Refinement LI LA :=
Build_Refinement (compile (@compile_core O1 L1 O2 RC))
(fun si sa => fst si = fst sa /\ RC.(refines) (snd si) (snd sa))
(Oracle ref)
( )

    
Lemma ss_transfer_horizontal_composition:
  forall O O1 O2 (L1: Language O1) (L2: Language O2)
  (LI: Language (HorizontalComposition O O1)) 
  (LA: Language (HorizontalComposition O O2))
  (RC: CoreRefinement L1 O2)
  (R: Refinement L1 L2)
  valid_state related_states cond 
  get_reboot_list transformer u 
  (n: nat) T (p1 p2: LA.(prog) T) rec,

  SelfSimulation u p1 p2 rec 
    valid_state
    related_states cond
    (get_reboot_list n) ->

    abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p1 rec (transformer get_reboot_list n) ->
    abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p2 rec (transformer get_reboot_list n) ->
    
    oracle_refines_same_from_related R u p1 p2 rec (transformer get_reboot_list n) related_states ->


    @SelfSimulation _ LI u _ (compile (@compile_core O1 L1 O2 RC) p1) 
      (compile (@compile_core O1 L1 O2 RC) p2) 
      (compile (@compile_core O1 L1 O2 RC) rec) 
      (fun si => refines_valid R (fun s => valid_state (fst si, s)) (snd si))
      (fun si1 si2 => refines_related R (fun s1 s2 => related_states (fst si1, s1) (fst si2, s2)) (snd si1) (snd si2))
    cond (transformer get_reboot_list n).
    Proof.
        unfold SelfSimulation; intros.
        simpl in *.


    SelfSimulation u p1 p2 rec 
    FileDiskNoninterference.AD_valid_state
    (FileDiskNoninterference.AD_related_states u' ex) (eq u') 
    (authenticated_disk_reboot_list n) ->
      SelfSimulation u (compile p1) (compile p2) (compile rec)
      ATC_valid_state
    (ATC_related_states u' ex) (eq u')
    (ATC_reboot_list n).
    
    
    
    .

  u u' ex n T (p1 p2: AuthenticatedDiskLang.(prog) T) rec,
    SelfSimulation u p1 p2 rec 
    FileDiskNoninterference.AD_valid_state
    (FileDiskNoninterference.AD_related_states u' ex) (eq u') 
    (authenticated_disk_reboot_list n) ->
      SelfSimulation u (compile p1) (compile p2) (compile rec)
      ATC_valid_state
    (ATC_related_states u' ex) (eq u')
    (ATC_reboot_list n).
Proof.


Lemma ss_ATC:
  forall u u' ex n T (p1 p2: AuthenticatedDiskLang.(prog) T) rec,
    SelfSimulation u p1 p2 rec 
    FileDiskNoninterference.AD_valid_state
    (FileDiskNoninterference.AD_related_states u' ex) (eq u') 
    (authenticated_disk_reboot_list n) ->
      SelfSimulation u (compile p1) (compile p2) (compile rec)
      ATC_valid_state
    (ATC_related_states u' ex) (eq u')
    (ATC_reboot_list n).
Proof.
    unfold SelfSimulation; intros.

 Admitted.