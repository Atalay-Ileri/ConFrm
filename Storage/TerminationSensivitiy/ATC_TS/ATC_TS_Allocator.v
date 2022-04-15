Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATC_Simulation ATC_AOE.
Require Import Not_Init HSS ATC_ORS ATC_TS_Common ATC_TS_TC.

Import FileDiskLayer.
Set Nested Proofs Allowed.


Lemma ATC_TS_InodeAllocator_read:
forall n inum u u',
Termination_Sensitive u
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum)))
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum)))
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state)
(fun s1 s2 => refines_related ATC_Refinement
 (fun s1 s2  => exists s1a s2a, 
    File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
    File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
    FD_related_states u' None s1a s2a) s1 s2 /\
(forall a, 
 Transaction.get_first (fst (snd s1)) a = None <-> 
 Transaction.get_first (fst (snd s2)) a = None))
(ATC_reboot_list n).
Proof.
Transparent Inode.InodeAllocator.read.
unfold Inode.InodeAllocator.read; simpl; intros.
destruct (Compare_dec.lt_dec inum
Inode.InodeAllocatorParams.num_of_blocks).
2: intros; apply ATC_TS_ret.
{
  eapply ATC_TS_compositional; simpl.
  intros; eapply TS_eqv_impl.
  unfold Inode.InodeAllocatorParams.bitmap_addr in *.
  pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
  intros; eapply ATC_TS_Transaction_read.
  lia.
  simpl; intros; cleanup; eauto.
  {
    intros.
    eapply_fresh lift2_invert_exec in H;
    eapply_fresh lift2_invert_exec in H0; cleanup.
    
    unfold refines_related in *; cleanup.
    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.

    eapply Transaction.read_finished in H7; eauto.
    eapply Transaction.read_finished in H5; eauto.

    unfold Inode.InodeAllocatorParams.bitmap_addr in *.
    cleanup; repeat split_ors; cleanup; try lia.
    erewrite InodeTS.inode_allocations_are_same with (s2:= fst (snd (snd x2))); eauto.
    destruct_fresh (nth_error
    (value_to_bits
       (fst (snd (snd x2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
    setoid_rewrite D; simpl.
    2: apply ATC_TS_ret.
    destruct b; simpl.
    2: apply ATC_TS_ret.
    eapply ATC_TS_compositional; simpl.
    2: intros; apply ATC_TS_ret.
    intros; eapply ATC_TS_Transaction_read.
    lia.
    intros; shelve.

    destruct (block_allocator_empty inum); 
    rewrite H14; apply ATC_TS_ret.
  }
  {
    simpl; intros; cleanup; eauto.
    eapply_fresh lift2_invert_exec in H;
    eapply_fresh lift2_invert_exec in H0; cleanup.
    
    unfold refines_related in *; cleanup.
    simpl in *; unfold HC_refines in *; cleanup.
    simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.

    eapply Transaction.read_finished in H8; eauto.
    eapply Transaction.read_finished in H6; eauto.

    unfold Inode.InodeAllocatorParams.bitmap_addr in *.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
    cleanup; repeat split_ors; cleanup; try lia; eauto.
  }
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
Qed.