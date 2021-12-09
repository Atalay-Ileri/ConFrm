Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS ATCD_TS_Common ATCD_TS_Recovery ATCD_TS_Transaction.

Import FileDiskLayer.
Set Nested Proofs Allowed.

Opaque File.recover.
Lemma ATCD_TS_InodeAllocator_read:
forall n inum u u' txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum))))
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum))))
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement
 AD_valid_state))
(fun s1 s2 => 
refines_related ATCD_Refinement 
(fun s1 s2 => refines_related ATC_Refinement
 (fun s1 s2  => exists s1a s2a, 
    File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
    File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
    FD_related_states u' None s1a s2a) s1 s2 /\
(forall a, 
 Transaction.get_first (fst (snd s1)) a = None <-> 
 Transaction.get_first (fst (snd s2)) a = None)) s1 s2 /\
 equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
 (forall a, 
 fst (snd (snd s1)) a = None <->
 fst (snd (snd s2)) a = None) /\
 fst (snd (snd s1)) =
Mem.list_upd_batch empty_mem
  (map Log.addr_list txns1)
  (map Log.data_blocks txns1) /\
fst (snd (snd s2)) =
Mem.list_upd_batch empty_mem
  (map Log.addr_list txns2)
  (map Log.data_blocks txns2))
(ATCD_reboot_list n).
Proof.
Transparent Inode.InodeAllocator.read.
unfold Inode.InodeAllocator.read; simpl; intros.
destruct (Compare_dec.lt_dec inum
Inode.InodeAllocatorParams.num_of_blocks).
2: {
  intros; eapply TS_eqv_impl.
  apply ATCD_TS_ret.
  simpl; intuition eauto.
}
{
  eapply ATCD_TS_compositional; simpl.
  intros; eapply TS_eqv_impl.
  unfold Inode.InodeAllocatorParams.bitmap_addr in *.
  pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
  intros; eapply ATCD_TS_Transaction_read.
  lia.
  simpl; intros; cleanup; eauto.
  {
    intros.
    unfold refines_related in *; cleanup.
    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold HC_refines in *; cleanup.

    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.
    unfold Definitions.refines in *; simpl in *.
    rewrite H13, H14.
    unfold LogCache.cached_log_rep in *; cleanup.
    repeat (split; eauto).
  }
  {
    simpl; intros.


    unfold refines_related in *; cleanup.
    edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H.
    }
    all: try solve [simpl in *; eauto].
    shelve.

    edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H0.
    }
    all: try solve [simpl in *; eauto].
    shelve.

    edestruct ATCD_simulation.
    2: apply H13.
    all: eauto.
    2:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.

    edestruct ATCD_simulation.
    2: apply H14.
    all: eauto.
    2:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.

    simpl in *; cleanup; repeat invert_exec.

    eapply_fresh lift2_invert_exec in H30;
    eapply_fresh lift2_invert_exec in H31; cleanup.
    
    unfold refines_related in *; cleanup.
    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.

    eapply Transaction.read_finished in H26; eauto.
    eapply Transaction.read_finished in H24; eauto.

    unfold Inode.InodeAllocatorParams.bitmap_addr in *.
    cleanup; repeat split_ors; cleanup; try lia.
    erewrite InodeTS.inode_allocations_are_same with (s2:= fst (snd (snd x2))); eauto.
    destruct_fresh (nth_error
    (value_to_bits
       (fst (snd (snd x2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
    setoid_rewrite D; simpl.
    2: {
     eapply TS_eqv_impl.
      apply ATCD_TS_ret.
      shelve.
    }
    destruct b; simpl.
    2: {
     eapply TS_eqv_impl.
      apply ATCD_TS_ret.
      shelve.
    }
    eapply ATCD_TS_compositional; simpl.
    2: intros; apply ATCD_TS_ret.
    intros; eapply TS_eqv_impl.
    eapply ATCD_TS_Transaction_read.
    lia.
    shelve.
    intros; shelve.

    destruct (block_allocator_empty inum); 
    rewrite H18;
    eapply TS_eqv_impl;
    try apply ATCD_TS_ret.
    shelve.
    shelve.
  }
  {
    simpl; intros; cleanup; eauto.
    unfold refines_related in *; cleanup.
    edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H.
    }
    all: try solve [simpl in *; eauto].
    shelve.

    edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H0.
    }
    all: try solve [simpl in *; eauto].
    shelve.

    edestruct ATCD_simulation.
    2: apply H13.
    all: eauto.
    2:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.

    edestruct ATCD_simulation.
    2: apply H14.
    all: eauto.
    2:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.

    simpl in *; cleanup; repeat invert_exec.

    eapply_fresh lift2_invert_exec in H30;
    eapply_fresh lift2_invert_exec in H31; cleanup.

    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.

    eapply Transaction.read_finished in H26; eauto.
    eapply Transaction.read_finished in H24; eauto.

    unfold Inode.InodeAllocatorParams.bitmap_addr in *.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
    cleanup; repeat split_ors; cleanup; try lia; eauto.
    
    shelve.
  }
}
Unshelve.
all: 
try match goal with
| [|- not_init _ ] =>
  unfold Transaction.read;
  destruct (Compare_dec.lt_dec Inode.InodeAllocatorParams.bitmap_addr
  data_length); simpl; intuition eauto;
  try destruct (Transaction.get_first t Inode.InodeAllocatorParams.bitmap_addr); 
  simpl; intuition eauto; 
  try match goal with
  | [H: eq_dep _ _ _ _ _ _ |- _] =>
  inversion H
  end
end.
5: instantiate (5 := fun _ _ s0 s3 => 
equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s0 s3 /\
(Transaction.get_first (fst (snd s0)) (inode_blocks_start + S inum) = None <->
 Transaction.get_first (fst (snd s3)) (inode_blocks_start + S inum) = None) /\
(fst (snd (snd s0)) (data_start + (inode_blocks_start + S inum)) = None <->
 fst (snd (snd s3)) (data_start + (inode_blocks_start + S inum)) = None) /\
fst (snd (snd s0)) =
Mem.list_upd_batch empty_mem (map Log.addr_list txns1)
  (map Log.data_blocks txns1) /\
fst (snd (snd s3)) =
Mem.list_upd_batch empty_mem (map Log.addr_list txns2)
  (map Log.data_blocks txns2)); simpl; intuition eauto.
5: simpl; intuition eauto.
9: simpl; intuition eauto.
5: simpl; intuition eauto.
14: simpl; intuition eauto.
10: simpl; intuition eauto.
5: {
  (*
  instantiate (1:= hdr2).
  instantiate (1:= hdr1).
  instantiate (1:= txns2).
  instantiate (1:= txns1).
  *)
  simpl; intuition eauto.
  simpl in *.

  simpl; intros; cleanup; eauto.
  unfold refines_related in *; cleanup.
  edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H18.
    }
    all: try solve [simpl in *; eauto].
    shelve.
    simpl.
    unfold HC_refines; simpl.
    unfold HC_refines; simpl.
    unfold Definitions.refines, LogCache.cached_log_rep.
    unfold Log.log_rep, Log.log_header_rep, Log.log_rep_general.
    unfold equivalent_for_recovery in *; cleanup.
    eexists (_, (_, _)); simpl; intuition eauto.
    eexists; simpl; intuition eauto.

    edestruct ATCD_AOE.
    4: {
      instantiate (1:= RFinished _ _).
      instantiate (6:= []). 
      unfold ATCD_reboot_list; simpl.
      econstructor.
      apply H26.
    }
    all: try solve [simpl in *; eauto].
    shelve.
    simpl.
    unfold HC_refines; simpl.
    unfold HC_refines; simpl.
    unfold Definitions.refines, LogCache.cached_log_rep.
    unfold Log.log_rep, Log.log_header_rep, Log.log_rep_general.
    unfold equivalent_for_recovery in *; cleanup.
    eexists (_, (_, _)); simpl; intuition eauto.
    eexists; simpl; intuition eauto.

    unfold equivalent_for_recovery in *; cleanup.
    edestruct ATCD_simulation.
    2: apply H35.
    all: eauto.
    3:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.
    unfold Simulation.Definitions.refines; simpl.
    unfold HC_refines; simpl.
    unfold HC_refines; simpl.
    unfold Definitions.refines, LogCache.cached_log_rep.
    unfold Log.log_rep, Log.log_header_rep, Log.log_rep_general.
    instantiate (1:= (_, (_, _))); simpl; intuition eauto.
    eexists; simpl; intuition eauto.

    edestruct ATCD_simulation.
    2: apply H44.
    all: eauto.
    3:  unfold ATCD_reboot_list; simpl; econstructor; eauto.
    shelve.
    unfold Simulation.Definitions.refines; simpl.
    unfold HC_refines; simpl.
    unfold HC_refines; simpl.
    unfold Definitions.refines, LogCache.cached_log_rep.
    unfold Log.log_rep, Log.log_header_rep, Log.log_rep_general.
    instantiate (1:= (_, (_, _))); simpl; intuition eauto.
    eexists; simpl; intuition eauto.

    simpl in *; cleanup_no_match; repeat invert_exec.

    repeat invert_lift2.
    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.

    repeat cleanup_pairs.
    (*
    eapply Transaction.read_finished in H80; eauto.
    eapply Transaction.read_finished in H81; eauto.

    cleanup; repeat cleanup_pairs.
    
    repeat match goal with
    |[H: _ \/ _|- _] =>
    clear H
    end.

    unfold HC_refines in *; simpl in *; cleanup.
    unfold Definitions.refines, LogCache.cached_log_rep in *.
    unfold Log.log_rep, Log.log_header_rep, Log.log_rep_general in *.
    cleanup.

    eexists (_, (_, _)), (_, (_, _)); simpl; split.
    intuition eauto.
    do 2 eexists; split.
    eauto.
    *)
    admit.
}
Admitted.


Lemma ATCD_TS_DiskAllocator_read:
    forall n a1 a2 u u' txns1 txns2 hdr1 hdr2,
    (a1 < File.DiskAllocatorParams.num_of_blocks <-> a2 < File.DiskAllocatorParams.num_of_blocks) ->
    (File.DiskAllocatorParams.bitmap_addr + S a1 <
    data_length <->
    File.DiskAllocatorParams.bitmap_addr + S a2 <
    data_length) ->
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
    ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a1))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
    ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a2))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
    ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |))))
        (refines_valid ATCD_Refinement
        (refines_valid ATC_Refinement
       AD_valid_state))
  (fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  refines_related ATCD_Refinement (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a) s1 s2 /\
  (forall a, 
     Transaction.get_first (fst (snd s1)) a = None <-> 
     Transaction.get_first (fst (snd s2)) a = None) /\
  (Transaction.get_first (fst (snd s1)) (File.DiskAllocatorParams.bitmap_addr + S a1) = None <-> 
   Transaction.get_first (fst (snd s2)) (File.DiskAllocatorParams.bitmap_addr + S a2) = None) /\
   nth_error
            (value_to_bits
               (upd_batch (snd (snd s1)) (rev (map fst (fst (snd s1))))
               (rev (map snd (fst (snd s1)))) File.DiskAllocatorParams.bitmap_addr)) a1 =
               nth_error
            (value_to_bits
               (upd_batch (snd (snd s2)) (rev (map fst (fst (snd s2))))
               (rev (map snd (fst (snd s2)))) File.DiskAllocatorParams.bitmap_addr)) a2) s1 s2)
  (ATCD_reboot_list n).
  Proof.
    unfold File.DiskAllocator.read; intros.
    destruct (Compare_dec.lt_dec a1 File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec a2 File.DiskAllocatorParams.num_of_blocks);
    try lia.
    2: intros; eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve].
    simpl.
    eapply ATCD_TS_compositional.

    intros; eapply TS_eqv_impl.
    eapply ATCD_TS_Transaction_read.
    shelve.
    shelve.
    intros; cleanup; eauto.
    2: shelve.
    intros.

    intros; unfold refines_related in *; cleanup.
    intros; unfold refines_related in *; cleanup.
      eapply_fresh ATCD_oracle_refines_finished in H1; eauto.
      eapply_fresh ATCD_oracle_refines_finished in H2; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H2; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply_fresh ATCD_oracle_refines_impl_eq in H14; eauto.
      2: shelve. (* eapply have_same_structure_get_owner; eauto. *)
      2: apply TC_oracle_refines_operation_eq.
      cleanup.

      clear H1 H2.
    repeat invert_lift2; cleanup.
    apply HC_map_ext_eq in H1; subst.
    unfold HC_refines in *; simpl in *; cleanup.

    unfold TransactionToTransactionalDisk.Definitions.refines in *.
    eapply Transaction.read_finished in H18; eauto.
    eapply Transaction.read_finished in H21; eauto.
    cleanup; repeat split_ors; cleanup; try lia.
    unfold Transaction.transaction_rep in *; cleanup.
    setoid_rewrite H9.
    destruct_fresh (nth_error
    (value_to_bits
       (upd_batch (snd (snd x0)) (rev (map fst (fst (snd x0))))
          (rev (map snd (fst (snd x0))))
          File.DiskAllocatorParams.bitmap_addr)) a2); setoid_rewrite D.
          2: intros; eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve].
    {
      destruct b.
      2: intros; eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve].
      eapply ATCD_TS_compositional.
      2: intros; eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve].
      intros; simpl; 
      eapply TS_eqv_impl; [apply ATCD_TS_Transaction_read; eauto | shelve].
      shelve.
    }
    {
      edestruct (block_allocator_empty a1);
      edestruct (block_allocator_empty a2);
      cleanup;  (eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve]).
    }
  Admitted.