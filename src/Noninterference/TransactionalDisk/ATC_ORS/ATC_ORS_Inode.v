Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer ATCSimulation ATCAOE.
Require Import Not_Init HSS ATC_ORS_Common ATC_ORS_TD ATC_ORS_DiskAllocator.
Import FileDiskLayer.



Lemma ATC_ORS_get_inode:
forall n inum u u',
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum))
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) 
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a).
Proof.
  Transparent Inode.get_inode.
  unfold Inode.get_inode; intros.
  simpl; eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  intros; apply ATC_ORS_inode_allocator_read.
  all: try solve [apply oracle_refines_independent_from_reboot_function].
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply map_ext_eq in H; subst.
    eapply Inode.InodeAllocator.read_finished_oracle_eq in H11; eauto.
    cleanup.
    destruct r1, r2; try solve [intuition congruence];
    simpl; apply ATC_ORS_ret; eauto.
    intros; cleanup; intuition congruence.
  }
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply_fresh ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H9; eauto; cleanup.
    eapply lift2_invert_exec in H10; eauto; cleanup.
    
    simpl in *.
    eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
    {
      apply map_ext_eq in Hx; subst.
      2: intros; cleanup; intuition congruence.
      eapply ATC_oracle_refines_impl_eq; eauto.
      2: apply TD_oracle_refines_operation_eq.
      eapply have_same_structure_InodeAllocator_read; eauto.
    }
    apply TD_oracle_refines_operation_eq.
    eapply have_same_structure_InodeAllocator_read; eauto.
    unfold AD_related_states, refines_related in *; cleanup; eauto.
    do 2 eexists; intuition eauto.
    unfold FD_related_states in *.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_InodeAllocator_read.
    apply not_init_InodeAllocator_read.
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
    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_InodeAllocator_read; eauto.
    apply not_init_InodeAllocator_read.
    apply not_init_InodeAllocator_read.
    rewrite <- app_assoc; eauto.
  }
  {
    unfold not; intros.
    unfold refines_related in *; cleanup.

    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_InodeAllocator_read; eauto.
    unfold AD_related_states, refines_related in *; cleanup; eauto.
    do 2 eexists; intuition eauto.
    unfold FD_related_states in *.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_InodeAllocator_read.
    apply not_init_InodeAllocator_read.
    rewrite <- app_assoc; eauto.
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
    unfold refines_related_reboot; simpl in *.
    unfold HC_refines_reboot; simpl.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
  }
  Unshelve.
  all: eauto.
  all: try solve [exact (fun _ _ => True)].
  all: try solve [simpl; eauto].
  all: apply not_init_get_inode.
Qed.

Lemma ATC_ORS_get_owner:
forall n inum u u',
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum))
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) (AD_related_states u' None).
Proof.
  Transparent Inode.get_owner.
  Opaque Inode.get_inode.
  unfold Inode.get_owner; intros.
  simpl; eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  intros; eapply ATC_ORS_equiv_impl.
  intros; apply ATC_ORS_get_inode.
  {
    unfold AD_related_states, refines_related; simpl;
    unfold refines, File.files_rep; 
    intros; cleanup; intuition eauto.
    do 2 eexists; intuition eauto.
    setoid_rewrite H4; eauto.
    setoid_rewrite H2; eauto.
  }
  all: try solve [apply oracle_refines_independent_from_reboot_function].
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply map_ext_eq in H; subst.
    eapply Inode.get_inode_finished_oracle_eq in H9; eauto.
    cleanup.
    destruct r1, r2; try solve [intuition congruence];
    simpl; apply ATC_ORS_ret; eauto.
    intros; cleanup; intuition congruence.
  }
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply_fresh ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H8; eauto; cleanup.
    eapply lift2_invert_exec in H7; eauto; cleanup.

    simpl in *.
    eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
    {
      apply map_ext_eq in Hx; subst.
      2: intros; cleanup; intuition congruence.
      eapply ATC_oracle_refines_impl_eq; eauto.
      2: apply TD_oracle_refines_operation_eq.
      eapply have_same_structure_get_inode; eauto.
      {
        unfold AD_related_states, refines_related in *; simpl in *;
        unfold refines, File.files_rep in *; 
        intros; cleanup; intuition eauto.
        do 2 eexists; intuition eauto.
        setoid_rewrite e2; eauto.
        setoid_rewrite e0; eauto.
      }
    }
    apply TD_oracle_refines_operation_eq.
    eapply have_same_structure_get_inode; eauto.
    {
        unfold AD_related_states, refines_related in *; simpl in *;
        unfold refines, File.files_rep in *; 
        intros; cleanup; intuition eauto.
        do 2 eexists; split.
        setoid_rewrite e0; eauto.
        split.
        setoid_rewrite e2; eauto.
      apply TSCommon.same_for_user_except_symmetry; eauto.
    }
    apply not_init_get_inode.
    apply not_init_get_inode.
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
    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_get_inode; eauto.
    {
        unfold AD_related_states, refines_related in *; simpl in *;
        unfold refines, File.files_rep in *; 
        intros; cleanup; intuition eauto.
        do 2 eexists; intuition eauto.
        setoid_rewrite e2; eauto.
        setoid_rewrite e0; eauto.
    }
    apply not_init_get_inode.
    apply not_init_get_inode.
    rewrite <- app_assoc; eauto.
  }
  {
    unfold not; intros.
    unfold refines_related in *; cleanup.
    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_get_inode; eauto.
    {
        unfold AD_related_states, refines_related in *; simpl in *;
        unfold refines, File.files_rep in *; 
        intros; cleanup; intuition eauto.
        do 2 eexists; split.
        setoid_rewrite e0; eauto.
        split.
        setoid_rewrite e2; eauto.
      apply TSCommon.same_for_user_except_symmetry; eauto.
    }
    apply not_init_get_inode.
    apply not_init_get_inode.
    rewrite <- app_assoc; eauto.
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
    unfold refines_related_reboot; simpl in *.
    unfold HC_refines_reboot; simpl.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
  }
  Unshelve.
  all: eauto.
  all: try solve [exact (fun _ _ => True)].
  all: try solve [simpl; eauto].
  all: apply not_init_get_owner.
Qed.

Lemma ATC_ORS_get_block_number:
forall n inum off u u',
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off))
  (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) 
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a).
Proof.
  Transparent Inode.get_block_number.
  Opaque Inode.get_inode.
  unfold Inode.get_block_number; intros.
  simpl; eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  intros; apply ATC_ORS_get_inode.
  all: try solve [apply oracle_refines_independent_from_reboot_function].
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply map_ext_eq in H; subst.
    eapply Inode.get_inode_finished_oracle_eq in H11; eauto.
    cleanup.
    destruct r1, r2; try solve [intuition congruence];
    simpl; apply ATC_ORS_ret; eauto.
    intros; cleanup; intuition congruence.
  }
  {
    simpl; intros.
    unfold refines_related in *; cleanup.
    eapply_fresh ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H9; eauto; cleanup.
    eapply lift2_invert_exec in H10; eauto; cleanup.

    simpl in *.
    eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
    {
      apply map_ext_eq in Hx; subst.
      2: intros; cleanup; intuition congruence.
      eapply ATC_oracle_refines_impl_eq; eauto.
      2: apply TD_oracle_refines_operation_eq.
      eapply have_same_structure_get_inode; eauto.
    }
    apply TD_oracle_refines_operation_eq.
    eapply have_same_structure_get_inode; eauto.
    do 2 eexists; intuition eauto.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_get_inode.
    apply not_init_get_inode.
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
    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_get_inode; eauto.
    apply not_init_get_inode.
    apply not_init_get_inode.
    rewrite <- app_assoc; eauto.
  }
  {
    unfold not; intros.
    unfold refines_related in *; cleanup.
    simpl in *.
    eapply ATC_oracle_refines_prefix_one_crashed. 
    3: eauto.
    3: eauto.
    all: eauto.
    eapply have_same_structure_get_inode; eauto.
    do 2 eexists; intuition eauto.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_get_inode.
    apply not_init_get_inode.
    rewrite <- app_assoc; eauto.
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
    unfold refines_related_reboot; simpl in *.
    unfold HC_refines_reboot; simpl.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
  }
  Unshelve.
  all: eauto.
  all: try solve [exact (fun _ _ => True)].
  all: try solve [simpl; eauto].
  all: apply not_init_get_block_number.
Qed.