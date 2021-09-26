Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer ATCSimulation ATCAOE.
Require Import ATC_ORS_Common.
Import FileDiskLayer.

Lemma ATC_ORS_TD_read:
forall n u a a' R,
oracle_refines_same_from_related ATC_Refinement u
(Op (HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length))
(@P2 _ (TransactionalDiskLayer.TDCore data_length) _
(TransactionalDiskLayer.Read a)))
(Op (HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length))
(@P2 _ (TransactionalDiskLayer.TDCore data_length) _ 
(TransactionalDiskLayer.Read a'))) 
File.recover (ATC_reboot_list n) R. (* (AD_related_states u' None). *)
Proof.
unfold ATC_reboot_list, 
oracle_refines_same_from_related; intros.
destruct n; simpl in *.
{
destruct l_o_imp; simpl in *; cleanup; try tauto.
simpl in *; repeat split_ors; cleanup; eauto;
try destruct l0; simpl in *; try lia.
specialize (H7 ATC_reboot_f).
specialize (H4 ATC_reboot_f).
cleanup.
eapply HC_map_ext_eq in H6; eauto.
subst.
eapply lift2_invert_exec in H2; cleanup.
eapply lift2_invert_exec in H3; cleanup.
repeat apply HC_map_ext_eq in H3; subst.
apply HC_map_ext_eq in H0; eauto; subst.
specialize (H7 tt).
specialize (H10 tt).
repeat split_ors; cleanup; eauto;
repeat unify_execs; cleanup; eauto.
}
{
destruct l_o_imp; simpl in *; cleanup; try tauto.
simpl in *; repeat split_ors; cleanup; eauto;
simpl in *; try lia.
{
specialize (H7 ATC_reboot_f).
specialize (H4 ATC_reboot_f).
cleanup.
specialize (H7 tt).
specialize (H10 tt).
eapply HC_map_ext_eq in H6; eauto.
subst.
eapply lift2_invert_exec in H2; cleanup.
eapply lift2_invert_exec in H3; cleanup.
repeat apply HC_map_ext_eq in H3; subst.
apply HC_map_ext_eq in H0; eauto; subst.
repeat split_ors; cleanup; eauto;
repeat unify_execs; cleanup; eauto.
}
{
eapply HC_map_ext_eq in H7; 
eauto; subst.
specialize (H8 tt).
specialize (H13 tt).
eapply lift2_invert_exec_crashed in H2; cleanup.
eapply lift2_invert_exec_crashed in H3; cleanup.
repeat apply HC_map_ext_eq in H3; subst.
apply HC_map_ext_eq in H2; eauto; subst.
eapply ATC_ORS_recover in H10.
apply H10 in H5; subst.

repeat split_ors; cleanup; eauto;
repeat unify_execs; cleanup; eauto.

{
unfold refines_related, refines_related_reboot,
AD_related_states, AD_related_states_reboot, 
refines_related, refines_related_reboot in *;
simpl in *; cleanup.
unfold HC_refines, HC_refines_reboot in *; simpl in *;
cleanup.
repeat split_ors; cleanup; eauto;
repeat unify_execs; cleanup; eauto.
unfold TransactionToTransactionalDisk.Definitions.refines,
TransactionToTransactionalDisk.Definitions.refines_reboot in *;
simpl in *; cleanup.
unfold Transaction.transaction_rep, 
Transaction.transaction_reboot_rep in *;
simpl in *; cleanup.
do 2 eexists; intuition eauto.
}
}
}
Qed.



Lemma ATC_ORS_ret:
      forall V n u (v v': V) R,
oracle_refines_same_from_related ATC_Refinement u
(@lift_L2 AuthenticationOperation _ TD _ (Ret v))
(@lift_L2 AuthenticationOperation _ TD _ (Ret v'))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n) R. (* (AD_related_states u' ex). *)
Proof.
unfold ATC_reboot_list, oracle_refines_same_from_related; 
intros; destruct n; simpl in *.
{
destruct l_o_imp; simpl in *; cleanup; try tauto.
repeat split_ors; cleanup; simpl in *; try lia; eauto.
specialize (H7 ATC_reboot_f).
specialize (H4 ATC_reboot_f).
repeat split_ors; cleanup; simpl in *; try lia; eauto;
repeat invert_exec.
}
{
destruct l_o_imp; simpl in *; cleanup; try tauto.
repeat split_ors; cleanup; simpl in *; try lia; eauto.
{
  specialize (H7 ATC_reboot_f).
specialize (H4 ATC_reboot_f).
repeat split_ors; cleanup; simpl in *; try lia; eauto;
repeat invert_exec.
}
{
  repeat split_ors; cleanup; simpl in *; try lia; eauto;
repeat invert_exec.
eapply ATC_ORS_recover in H7; eauto.
eapply H7 in H5; subst; eauto.
unfold refines_related, refines_related_reboot in *;
simpl in *;  cleanup.
unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
TransactionToTransactionalDisk.Definitions.refines in * ; simpl.
unfold Transaction.transaction_reboot_rep,
Transaction.transaction_rep in *; simpl; cleanup.
do 2 eexists; repeat (split; eauto).
}
}
Qed.




Lemma ATC_ORS_commit:
forall n u u',
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Commit))
  (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Commit))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a).
Proof.
  Opaque Transaction.commit.
  unfold ATC_reboot_list, 
  oracle_refines_same_from_related; intros.
  destruct n; simpl in *.
  {
  destruct l_o_imp; simpl in *; cleanup; try tauto.
  simpl in *; repeat split_ors; cleanup; eauto;
  try destruct l0; simpl in *; try lia.
  specialize (H7 ATC_reboot_f).
  specialize (H4 ATC_reboot_f).
  cleanup.
  eapply HC_map_ext_eq in H6; eauto.
  subst.
  eapply lift2_invert_exec in H2; cleanup.
  eapply lift2_invert_exec in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H0; eauto; subst.
  specialize (H7 tt).
  specialize (H10 tt).
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  }
  {
  destruct l_o_imp; simpl in *; cleanup; try tauto.
  simpl in *; repeat split_ors; cleanup; eauto;
  simpl in *; try lia.
  {
  specialize (H7 ATC_reboot_f).
  specialize (H4 ATC_reboot_f).
  cleanup.
  eapply HC_map_ext_eq in H6; eauto.
  subst.
  eapply lift2_invert_exec in H2; cleanup.
  eapply lift2_invert_exec in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H0; eauto; subst.
  specialize (H7 tt).
  specialize (H10 tt).
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  }
  {
  eapply HC_map_ext_eq in H7; 
  eauto; subst.
  eapply lift2_invert_exec_crashed in H2; cleanup.
  eapply lift2_invert_exec_crashed in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H2; eauto; subst.
  eapply ATC_ORS_recover in H10.
  apply H10 in H5; subst.
  specialize (H8 tt).
  specialize (H13 tt).
  
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  {
    unfold refines_related, refines_related_reboot,
    AD_related_states, AD_related_states_reboot, 
    refines_related, refines_related_reboot in *;
    simpl in *; cleanup.
    unfold HC_refines, HC_refines_reboot in *; simpl in *;
    cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    TransactionToTransactionalDisk.Definitions.refines_reboot in *;
    simpl in *; cleanup.
    unfold Transaction.transaction_rep, 
    Transaction.transaction_reboot_rep in *;
    simpl in *; cleanup.
    repeat cleanup_pairs; simpl in *; cleanup.
    repeat split_ors; subst; cleanup; eauto.
    all: repeat split_ors; cleanup; try lia;
    apply app_inj_tail in H7; cleanup; congruence.
  }
  {
    unfold refines_related, refines_related_reboot,
    AD_related_states, AD_related_states_reboot, 
    refines_related, refines_related_reboot in *;
    simpl in *; cleanup.
    unfold HC_refines, HC_refines_reboot in *; simpl in *;
    cleanup.
    specialize (H8 tt).
  specialize (H13 tt).
    repeat split_ors; cleanup; eauto;
    repeat unify_execs; cleanup; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    TransactionToTransactionalDisk.Definitions.refines_reboot in *;
    simpl in *; cleanup.
    unfold Transaction.transaction_rep, 
    Transaction.transaction_reboot_rep in *;
    simpl in *; cleanup.
    clear H11 H16.
    repeat split_ors; cleanup; eauto.
    - clear H20.
    repeat unify_execs; cleanup; eauto.
    do 2 eexists; intuition eauto.
    shelve.
    - repeat split_ors; subst; cleanup; eauto.
    all: repeat split_ors; cleanup; try lia.
    apply app_inj_tail in H16; cleanup; congruence.
    - repeat split_ors; subst; cleanup; eauto.
    all: repeat split_ors; cleanup; try lia.
    apply app_inj_tail in H16; cleanup; congruence.
    - clear H20.
    repeat unify_execs; cleanup; eauto.
    eexists (_, (_, (fst (snd (snd x1)), fst (snd (snd x1))))), 
    (_, (_, (fst (snd (snd x3)), fst (snd (snd x3))))); 
    simpl; intuition eauto.
    shelve.
  }
  }
  }
  Unshelve.
  instantiate (1:= fun _ _ => True); simpl; eauto.
  all: simpl; eauto.
  all: exact Empty. 
  Qed.

Lemma ATC_ORS_commit_then_ret:
forall n u u' T (t1 t2: option T),
oracle_refines_same_from_related ATC_Refinement u
  (_ <- (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Commit));
   Ret t1)
  (_ <- (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Commit));
   Ret t2) (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a).
Proof.
  intros.
  eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  2: simpl; intros; apply ATC_ORS_ret; eauto.
  all: try solve [apply oracle_refines_independent_from_reboot_function].
  intros; apply ATC_ORS_commit.
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply HC_map_ext_eq_prefix in H3; eauto; cleanup.
    eapply Transaction.commit_finished_oracle_eq in H2; eauto.
    cleanup; eauto.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_finished in H; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_finished in H0; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
repeat invert_exec; try lia;
simpl in *; cleanup; 
repeat split_ors; cleanup; try congruence;
do 2 eexists; intuition eauto.
all: shelve.
}
{
unfold not; intros.
unfold refines_related in *; cleanup.
simpl in *; repeat invert_exec.
eapply lift2_invert_exec in H; cleanup.
eapply lift2_invert_exec_crashed in H3; cleanup.

apply HC_map_ext_eq in H3; cleanup.
apply HC_map_ext_eq in H; cleanup.
rewrite <- app_nil_r in e1.
apply HC_map_ext_eq_prefix in e1; cleanup.
eapply Transaction.commit_finished_not_crashed; eauto.
}
{
unfold not; intros.
unfold refines_related in *; cleanup.
simpl in *; repeat invert_exec.
eapply lift2_invert_exec in H; cleanup.
eapply lift2_invert_exec_crashed in H3; cleanup.

apply HC_map_ext_eq in H3; cleanup.
apply HC_map_ext_eq in H; cleanup.
rewrite <- app_nil_r in e4.
apply HC_map_ext_eq_prefix in e4; cleanup.
eapply Transaction.commit_finished_not_crashed; eauto.
}
{
  intros; unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_crashed in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_crashed in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  simpl in *.
  unfold refines_related, refines_related_reboot in *;
  simpl in *;  cleanup.
  unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
  do 2 eexists; repeat (split; eauto).
  all: shelve.
}
  Unshelve.
  all: try solve [exact (fun _ _ => True)].
  all: simpl in *; eauto.
  all: intuition eauto.
  all: repeat match goal with 
       | [H: eq_dep _ _ _ _ _ _ |- _] =>
         inversion H
       end.
Qed.





Lemma ATC_ORS_abort:
forall n u R,
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Abort))
  (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Abort))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) R.
Proof.
  Opaque Transaction.abort.
  unfold ATC_reboot_list, 
  oracle_refines_same_from_related; intros.
  destruct n; simpl in *.
  {
  destruct l_o_imp; simpl in *; cleanup; try tauto.
  simpl in *; repeat split_ors; cleanup; eauto;
  try destruct l0; simpl in *; try lia.
  specialize (H7 ATC_reboot_f).
  specialize (H4 ATC_reboot_f).
  cleanup.
  specialize (H7 tt).
  specialize (H10 tt).
  eapply HC_map_ext_eq in H6; eauto.
  subst.
  eapply lift2_invert_exec in H2; cleanup.
  eapply lift2_invert_exec in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H0; eauto; subst.
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  }
  {
  destruct l_o_imp; simpl in *; cleanup; try tauto.
  simpl in *; repeat split_ors; cleanup; eauto;
  simpl in *; try lia.
  {
  specialize (H7 ATC_reboot_f).
  specialize (H4 ATC_reboot_f).
  cleanup.
  
  simpl in *; repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup.
  eapply HC_map_ext_eq in H6; eauto.
  subst.
  eapply lift2_invert_exec in H2; cleanup.
  eapply lift2_invert_exec in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H0; eauto; subst.
  specialize (H7 tt).
  specialize (H10 tt).
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  }
  {
    
  eapply HC_map_ext_eq in H7; 
  eauto; subst.
  eapply lift2_invert_exec_crashed in H2; cleanup.
  eapply lift2_invert_exec_crashed in H3; cleanup.
  repeat apply HC_map_ext_eq in H3; subst.
  apply HC_map_ext_eq in H2; eauto; subst.
  eapply ATC_ORS_recover in H10.
  apply H10 in H5; subst.
  specialize (H8 tt).
  specialize (H13 tt).
  repeat split_ors; cleanup; eauto;
  repeat unify_execs; cleanup; eauto.
  
  {
    unfold refines_related, refines_related_reboot,
    AD_related_states, AD_related_states_reboot, 
    refines_related, refines_related_reboot in *;
    simpl in *; cleanup.
    unfold HC_refines, HC_refines_reboot in *; simpl in *;
    cleanup.
    specialize (H8 tt).
    specialize (H13 tt).
    repeat split_ors; cleanup; eauto;
    repeat unify_execs; cleanup; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    TransactionToTransactionalDisk.Definitions.refines_reboot in *;
    simpl in *; cleanup.
    unfold Transaction.transaction_rep, 
    Transaction.transaction_reboot_rep in *;
    simpl in *; cleanup.
    do 2 eexists; intuition eauto.
  }
  }
  }
  Qed.

Lemma ATC_ORS_abort_then_ret:
forall n u T P,
oracle_refines_same_from_related ATC_Refinement u
  (_ <- (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Abort));
   @Ret _ (option T) None)
  (_ <- (@lift_L2 AuthenticationOperation _ TD _
  (Op (TransactionalDiskLayer.TDCore data_length)
     TransactionalDiskLayer.Abort));
   Ret None) (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) P.
Proof.
  intros.
  eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  2: simpl; intros; apply ATC_ORS_ret; eauto.
  all: try solve [apply oracle_refines_independent_from_reboot_function].
  intros; apply ATC_ORS_abort.
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply HC_map_ext_eq_prefix in H3; eauto; cleanup.
    eapply Transaction.abort_finished_oracle_eq in H2; eauto.
    cleanup; eauto.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_finished in H; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_finished in H0; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
repeat invert_exec; try lia;
simpl in *; cleanup; 
repeat split_ors; cleanup; try congruence;
do 2 eexists; intuition eauto.
all: shelve.
}
{
unfold not; intros.
unfold refines_related in *; cleanup.
simpl in *; repeat invert_exec.
eapply lift2_invert_exec in H; cleanup.
eapply lift2_invert_exec_crashed in H3; cleanup.

apply HC_map_ext_eq in H3; cleanup.
apply HC_map_ext_eq in H; cleanup.
rewrite <- app_nil_r in e1.
apply HC_map_ext_eq_prefix in e1; cleanup.
eapply Transaction.abort_finished_not_crashed; eauto.
}
{
unfold not; intros.
unfold refines_related in *; cleanup.
simpl in *; repeat invert_exec.
eapply lift2_invert_exec in H; cleanup.
eapply lift2_invert_exec_crashed in H3; cleanup.

apply HC_map_ext_eq in H3; cleanup.
apply HC_map_ext_eq in H; cleanup.
rewrite <- app_nil_r in e4.
apply HC_map_ext_eq_prefix in e4; cleanup.
eapply Transaction.abort_finished_not_crashed; eauto.
}
{
  intros; unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_crashed in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_crashed in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  simpl in *.
  unfold refines_related, refines_related_reboot in *;
  simpl in *;  cleanup.
  unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
  do 2 eexists; repeat (split; eauto).
  all: shelve.
}
  Unshelve.
  all: try solve [exact (fun _ _ => True)].
  all: simpl in *; eauto.
  all: intuition eauto.
  all: repeat match goal with 
       | [H: eq_dep _ _ _ _ _ _ |- _] =>
         inversion H
       end.
Qed.


Lemma ATC_ORS_auth:
forall n u u1 u2 R,
oracle_refines_same_from_related ATC_Refinement u 
(Op
  (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) 
  (@P1 AuthenticationOperation _  _ (Auth u1)))
(Op
  (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) 
  (@P1 AuthenticationOperation _  _ (Auth u2))) File.recover 
(ATC_reboot_list n) R.
Proof.
  unfold oracle_refines_same_from_related, ATC_reboot_list;
  intros; destruct n; simpl in *; repeat invert_exec.
  {
    destruct l_o_imp; simpl in *; cleanup; try tauto.
    simpl in *; repeat split_ors; cleanup; try lia.
    specialize (H7 ATC_reboot_f).
    specialize (H4 ATC_reboot_f).
    cleanup; eauto.
  }
  {
    destruct l_o_imp; simpl in *; cleanup; try tauto.
    simpl in *; repeat split_ors; cleanup; eauto;
    simpl in *; try lia.
    {
      specialize (H7 ATC_reboot_f).
      specialize (H4 ATC_reboot_f).
      cleanup; eauto.
    }
    {
      eapply ATC_ORS_recover in H9.
      apply H9 in H5; subst; eauto.
      
      repeat split_ors; cleanup; eauto;
      repeat unify_execs; cleanup; eauto.
      repeat invert_exec; cleanup.
      {
        unfold refines_related, refines_related_reboot,
        AD_related_states, AD_related_states_reboot, 
        refines_related, refines_related_reboot in *;
        simpl in *; cleanup.
        unfold HC_refines, HC_refines_reboot in *; simpl in *;
        cleanup.
        repeat split_ors; cleanup; eauto;
        repeat unify_execs; cleanup; eauto.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        TransactionToTransactionalDisk.Definitions.refines_reboot in *;
        simpl in *; cleanup.
        unfold Transaction.transaction_rep, 
        Transaction.transaction_reboot_rep in *;
        simpl in *; cleanup.
        do 2 eexists; intuition eauto.
      }
    }
  }
Qed.
