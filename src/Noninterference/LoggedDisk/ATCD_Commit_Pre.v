Require Import Eqdep Lia Lra Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference LoggedDiskRefinement.
Require Import ATC_ORS HSS ATCDLayer ATCD_Simulation ATCD_AOE.
Require Import LogCache_FinishedNotCrashed ATCD_ORS ATCD_HSS.
Import FileDiskLayer.

Lemma disk_allocator_read_exact_txn:
  forall u o s1 s1' r v1,
exec ATCLang u o s1
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
     (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
     (option _)
     (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read v1)))
  (Finished s1' r) ->
     s1' = s1.
     Proof.
      Transparent File.DiskAllocator.read.
      unfold File.DiskAllocator.read.
      intros; cleanup; simpl in *; repeat invert_exec;
      simpl in *; repeat invert_exec; eauto;
      eapply Transaction.read_finished_state in H2; eauto;
      cleanup; eauto; repeat cleanup_pairs;
      try eapply Transaction.read_finished_state in H3; eauto;
      cleanup; eauto.
    destruct s1'; eauto.
      Opaque File.DiskAllocator.read.
    Qed.

Lemma inode_allocator_write_exact_txn:
    forall u o s1 s1' r inum v,
  exec ATCLang u o s1
    (RefinementLift.compile
       (HorizontalComposition AuthenticationOperation
          TransactionCacheOperation)
       (HorizontalComposition AuthenticationOperation
          (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
       (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
       (option _)
       (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.write inum v)))
    (Finished s1' (Some r)) ->
    fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr + S inum, v) :: fst (snd s1) /\
    snd (snd s1') = snd (snd s1).
       Proof.
        Transparent Inode.InodeAllocator.write.
        unfold Inode.InodeAllocator.write.
        intros; cleanup; simpl in *; repeat invert_exec;
        simpl in *; repeat invert_exec; eauto; try congruence.
        eapply Transaction.read_finished_state in H2; eauto;
        cleanup; eauto; repeat cleanup_pairs;
        try eapply Transaction.write_finished_state in H4; eauto;
        cleanup; eauto.
        split_ors; cleanup; try congruence; eauto.
        Opaque Inode.InodeAllocator.write.
      Qed.

Lemma disk_allocator_write_exact_txn:
      forall u o s1 s1' r a v1,
      exec ATCLang u o s1
      (RefinementLift.compile
          (HorizontalComposition AuthenticationOperation
              TransactionCacheOperation)
          (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
          (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
          (option unit)
          (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.write a v1)))
      (Finished s1' (Some r)) ->
          fst (snd s1') = (File.DiskAllocatorParams.bitmap_addr + S a, v1) :: fst (snd s1) /\
          snd (snd s1') = snd (snd s1) /\
          a < File.DiskAllocatorParams.num_of_blocks.
      Proof.
          Transparent File.DiskAllocator.write.
          unfold File.DiskAllocator.write.
          intros; cleanup; simpl in *; repeat invert_exec;
          simpl in *; repeat invert_exec; eauto; try congruence.
          eapply Transaction.read_finished_state in H2; eauto;
          cleanup; eauto; try congruence.
          repeat cleanup_pairs;
          eapply Transaction.write_finished_state in H4; eauto;
          cleanup; eauto; try congruence.
          repeat cleanup_pairs; eauto;
          split_ors; cleanup; try lia.
          simpl; intuition.
      Qed.

(***********)

Lemma get_inode_exact_txn:
forall u o s1 s1' r1 inum,
exec ATCLang u o s1
   (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation
         TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
         (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
      (option Inode.Inode)
      (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum)))
   (Finished s1' r1) ->
   s1 = s1'.
   Proof.
    Transparent Inode.get_inode.
    unfold Inode.get_inode, Inode.InodeAllocator.read.
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    eapply Transaction.read_finished_state in H3; eauto;
    cleanup; eauto;
    repeat cleanup_pairs; eauto.
    eapply Transaction.read_finished_state in H1; eauto;
    cleanup; eauto.
    destruct s1'; eauto.
    Opaque Inode.get_inode.
  Qed.

Lemma inode_get_block_number_exact_txn:
    forall u o s1 s1' r  inum a,
    exec ATCLang u o s1
    (RefinementLift.compile
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
    (option _)
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum a)))
    (Finished s1' r) ->
    s1'= s1.
Proof.
    Transparent Inode.get_block_number.
    Opaque Inode.get_inode.
    unfold Inode.get_block_number.
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    eapply get_inode_exact_txn in H; eauto; cleanup; eauto.
    Opaque Inode.get_block_number.
Qed.

Lemma inode_get_all_block_numbers_exact_txn:
    forall u o s1 s1' r  inum,
    exec ATCLang u o s1
    (RefinementLift.compile
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
    (option _)
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_all_block_numbers inum)))
    (Finished s1' r) ->
    s1'= s1.
Proof.
    Transparent Inode.get_all_block_numbers.
    Opaque Inode.get_inode.
    unfold Inode.get_all_block_numbers.
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    eapply get_inode_exact_txn in H; eauto; cleanup; eauto.
    Opaque Inode.get_all_block_numbers.
Qed.

Lemma inode_extend_exact_txn:
    forall u o s1 s1' r inum a,
    exec ATCLang u o s1
    (RefinementLift.compile
    (HorizontalComposition AuthenticationOperation
    TransactionCacheOperation)
    (HorizontalComposition AuthenticationOperation
    (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
    (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
    (option _)
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.extend inum a)))
    (Finished s1' (Some r)) ->
    exists v,
    fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr + S inum, v) :: fst (snd s1) /\
    snd (snd s1') = snd (snd s1).
Proof.
    Transparent Inode.extend.
    unfold Inode.extend, Inode.set_inode.
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto;
    intros; cleanup; simpl in *; repeat invert_exec;
    simpl in *; repeat invert_exec; eauto; try congruence;
    eapply get_inode_exact_txn in H; eauto; cleanup; eauto;
    eapply inode_allocator_write_exact_txn in H0; eauto; cleanup; eauto.
    Opaque Inode.extend.
    Qed.

Lemma inode_free_exact_txn:
    forall u o s1 s1' r v1,
exec ATCLang u o s1
    (RefinementLift.compile
       (HorizontalComposition AuthenticationOperation
          TransactionCacheOperation)
       (HorizontalComposition AuthenticationOperation
          (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
       (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
       (option unit)
       (@lift_L2 AuthenticationOperation _ TD _ (Inode.free v1)))
    (Finished s1' (Some r)) ->
       (exists new_bitmap, 
       fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr, new_bitmap) :: fst (snd s1) /\
       snd (snd s1') = snd (snd s1)).
       Proof.
        Transparent Inode.free.
        unfold Inode.free, Inode.InodeAllocator.free.
        intros; cleanup; simpl in *; repeat invert_exec;
        simpl in *; repeat invert_exec; eauto;
        try eapply Transaction.read_finished_state in H2; eauto;
        cleanup; eauto.
          eapply Transaction.write_finished_state in H4; eauto;
          cleanup; eauto;
          repeat split_ors; cleanup; try congruence.
          eexists; cleanup.
          setoid_rewrite H4; simpl; eauto.
          repeat cleanup_pairs; intuition eauto.
        Qed.


(***********)

Lemma read_inner_exact_txn:
forall u o s1 s1' r inum a,
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option _)
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner a inum)))
(Finished s1' r) ->
s1' = s1.
Proof.
unfold File.read_inner.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply inode_get_block_number_exact_txn in H; eauto; cleanup; eauto;
eapply disk_allocator_read_exact_txn in H0; eauto; cleanup; eauto.
Qed.

Lemma write_inner_commit_pre':
forall u o s1 s1' r inum a v,
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option _)
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner a v inum)))
(Finished s1' (Some r)) ->
exists a, 
fst (snd s1') = (File.DiskAllocatorParams.bitmap_addr + S a, v) :: fst (snd s1) /\
snd (snd s1') = snd (snd s1) /\
a < File.DiskAllocatorParams.num_of_blocks.
Proof.
unfold File.write_inner.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply inode_get_block_number_exact_txn in H; eauto; cleanup; eauto;
eapply disk_allocator_write_exact_txn in H0; eauto; cleanup; eauto;
repeat cleanup_pairs; intuition eauto.
Qed.

Lemma change_owner_inner_exact_txn:
forall u o s1 s1' r inum u',
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option _)
(@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner u' inum)))
(Finished s1' (Some r)) ->
exists inode, 
fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr + S inum, inode) :: fst (snd s1) /\
snd (snd s1') = snd (snd s1).
Proof.
Transparent Inode.change_owner.
unfold File.change_owner_inner, Inode.change_owner, Inode.set_inode.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply get_inode_exact_txn in H; eauto; cleanup; eauto;
eapply inode_allocator_write_exact_txn in H0; eauto; cleanup; eauto;
repeat cleanup_pairs; intuition eauto.
Qed.

Lemma extend_inner_commit_pre':
forall u o s1 s1' r td1 inum v,
Transaction.transaction_rep (snd s1) td1 ->
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option _)
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v inum)))
(Finished s1' (Some r)) ->
exists new_bitmap a i, 
fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr + S inum, i) :: (File.DiskAllocatorParams.bitmap_addr, new_bitmap) :: (File.DiskAllocatorParams.bitmap_addr + S a, v) :: fst (snd s1) /\
snd (snd s1') = snd (snd s1) /\
a < File.DiskAllocatorParams.num_of_blocks.
Proof.
Opaque File.DiskAllocator.alloc.
unfold File.extend_inner.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply disk_allocator_alloc_exact_txn in H0; eauto; cleanup; eauto;
split_ors; cleanup; try congruence; repeat cleanup_pairs.
eapply inode_extend_exact_txn in H1; simpl; eauto; cleanup; eauto;
repeat cleanup_pairs; cleanup; intuition eauto; try congruence.
do 3 eexists; intuition eauto.
Qed.

Lemma delete_inner_commit_pre':
forall u o s1 s1' r td1 inum im,
Transaction.transaction_rep (snd s1) td1 ->
Inode.inode_rep im (fst (snd td1)) ->
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option _)
(@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)))
(Finished s1' (Some r)) ->
exists l i inode,
im inum = Some inode /\
fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr, i) ::  l ++ fst (snd s1) /\
(map fst l = repeat File.DiskAllocatorParams.bitmap_addr (length (Inode.block_numbers inode)))  /\
snd (snd s1') = snd (snd s1).
Proof.
Opaque File.DiskAllocator.alloc.
unfold File.delete_inner.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply_fresh inode_get_all_block_numbers_exact_txn in H1; eauto; cleanup; eauto;
cleanup; try congruence.

eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto.
2: {
    unfold HC_refines; simpl; eexists (_, _); intuition eauto.
}
cleanup.
eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H1; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
cleanup.
2: {
    simpl.
    unfold HC_refines; simpl; instantiate (1:= (_, _)); intuition eauto.
}

eapply_fresh lift2_invert_exec in H5; cleanup_no_match.
eapply Inode.get_all_block_numbers_finished in H9; eauto.
cleanup; repeat split_ors; try congruence; cleanup.

eapply free_all_blocks_exact_txn in H2; simpl; eauto; cleanup; eauto;
repeat cleanup_pairs; cleanup; intuition eauto; try congruence.
cleanup.
eapply inode_free_exact_txn in H3; cleanup;
repeat cleanup_pairs.
repeat eexists; eauto.
Unshelve.
exact id.
Qed.

(*********)
Lemma refines_related_txn_empty:
    forall s1 s2 u ex,
    refines_related ATC_Refinement (AD_related_states u ex) s1 s2 ->
    (fst (snd s1)) = [] /\ (fst (snd s2)) = [].
    Proof.
    unfold AD_related_states, refines_related; simpl;
    unfold HC_refines; simpl;
    unfold TransactionToTransactionalDisk.Definitions.refines,
    FileToFileDisk.Definitions.refines,
    FD_related_states,
    File.files_rep,
    Transaction.transaction_rep; simpl.
    intros; logic_clean; repeat split_ors; logic_clean; try congruence.
    repeat cleanup_pairs.
    destruct s, s3; simpl in *; try lia; eauto.
    Qed.

Theorem read_inner_commit_pre:
forall u u' off inum (s0 s3 : state ATCLang) (o : oracle' ATCCore)
  (s1' s2' : LayerImplementation.state' ATCCore) 
  (r1 r2 : value),
refines_related ATC_Refinement (AD_related_states u' None) s0 s3 ->
exec ATCLang u o s0
  (Simulation.Definitions.compile ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Finished s1' (Some r1)) ->
exec ATCLang u o s3
  (Simulation.Definitions.compile ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Finished s2' (Some r2)) ->
length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
(Forall (fun a : nat => a < data_length)
   (map fst (fst (snd s1'))) <->
 Forall (fun a : nat => a < data_length)
   (map fst (fst (snd s2')))).
   Proof.
    intros.
    eapply read_inner_exact_txn in H0, H1; subst; eauto.
    eapply refines_related_txn_empty in H; cleanup; 
    simpl; intuition eauto.
   Qed.

   Theorem write_inner_commit_pre:
   forall u u' ex off inum v1 v2 (s0 s3 : state ATCLang) (o : oracle' ATCCore)
     (s1' s2' : LayerImplementation.state' ATCCore) 
     r1 r2,
   refines_related ATC_Refinement (AD_related_states u' ex) s0 s3 ->
   exec ATCLang u o s0
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v1 inum)))
     (Finished s1' (Some r1)) ->
   exec ATCLang u o s3
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v2 inum)))
     (Finished s2' (Some r2)) ->
   length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
   length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
   (Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s1'))) <->
    Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s2')))).
      Proof.
       intros.
       eapply write_inner_commit_pre' in H0, H1; subst; eauto.
       cleanup; simpl.
       eapply refines_related_txn_empty in H; cleanup; 
       repeat cleanup_pairs; eauto.
       pose proof file_blocks_fit_in_disk.
       unfold File.DiskAllocatorParams.bitmap_addr,
       File.DiskAllocatorParams.num_of_blocks in *.
       simpl; intuition eauto;
       repeat constructor; lia.
    Qed.

    Theorem change_owner_inner_commit_pre:
   forall u u' ex inum v1 v2 (s0 s3 : state ATCLang) (o : oracle' ATCCore)
     (s1' s2' : LayerImplementation.state' ATCCore) 
     r1 r2,
   refines_related ATC_Refinement (AD_related_states u' ex) s0 s3 ->
   exec ATCLang u o s0
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v1 inum)))
     (Finished s1' (Some r1)) ->
   exec ATCLang u o s3
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v2 inum)))
     (Finished s2' (Some r2)) ->
   length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
   length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
   (Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s1'))) <->
    Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s2')))).
      Proof.
       intros.
       eapply change_owner_inner_exact_txn in H0, H1; subst; eauto.
       cleanup; simpl.
       eapply refines_related_txn_empty in H; cleanup; 
       repeat cleanup_pairs; eauto.
       pose proof file_blocks_fit_in_disk.
       unfold File.DiskAllocatorParams.bitmap_addr,
       File.DiskAllocatorParams.num_of_blocks in *.
       simpl; intuition eauto;
       repeat constructor; lia.
    Qed.

    Theorem extend_inner_commit_pre:
   forall u u' ex inum v1 v2 (s0 s3 : state ATCLang) (o : oracle' ATCCore)
     (s1' s2' : LayerImplementation.state' ATCCore) 
     r1 r2,
   refines_related ATC_Refinement (AD_related_states u' ex) s0 s3 ->
   exec ATCLang u o s0
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v1 inum)))
     (Finished s1' (Some r1)) ->
   exec ATCLang u o s3
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v2 inum)))
     (Finished s2' (Some r2)) ->
     inum < Inode.InodeAllocatorParams.num_of_blocks ->
   length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
   length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
   (Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s1'))) <->
    Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s2')))).
      Proof.
        Opaque File.extend_inner.
       intros.
       eapply_fresh refines_related_txn_empty in H; cleanup.
       unfold AD_related_states, refines_related in *; simpl in *;
        unfold HC_refines in *; simpl in *;
        unfold TransactionToTransactionalDisk.Definitions.refines in *;
        logic_clean.
       eapply extend_inner_commit_pre' in H0, H1; subst; eauto.
       cleanup; simpl.
       repeat cleanup_pairs; eauto.
       pose proof file_blocks_fit_in_disk.
       pose proof inodes_before_data.
       unfold File.DiskAllocatorParams.bitmap_addr,
       File.DiskAllocatorParams.num_of_blocks,
       Inode.InodeAllocatorParams.bitmap_addr,
       Inode.InodeAllocatorParams.num_of_blocks in *.
       simpl.
       destruct (addr_dec file_blocks_start (file_blocks_start + S x7)); try lia.
       destruct (addr_dec (inode_blocks_start + S inum)
       (file_blocks_start + S x7)); try lia.
       destruct (addr_dec (inode_blocks_start + S inum)
       file_blocks_start); try lia.
       destruct (addr_dec file_blocks_start (file_blocks_start + S x4)); try lia.
       destruct (addr_dec (inode_blocks_start + S inum)
       (file_blocks_start + S x4)); try lia.
       simpl; intuition eauto;
       repeat constructor; lia.
    Qed.


    Lemma rev_repeat:
       forall T n (t: T),
       rev (repeat t n) = repeat t n.
       Proof.
        induction n; simpl; eauto.
        intros; rewrite IHn.
        rewrite repeat_cons; eauto.
        Qed.

        Lemma dedup_last_repeat_length:
        forall n a,
        n = 0 \/ length (dedup_last addr_dec (repeat a n)) = 1.
        Proof.
         induction n; eauto.
         intros.
         edestruct IHn; cleanup; simpl; eauto.
         destruct (in_dec addr_dec a (repeat a n)); eauto.
         destruct n; simpl in *; try tauto.
         Qed.
         

    Theorem delete_inner_commit_pre:
   forall u u' inum (s0 s3 : state ATCLang) (o : oracle' ATCCore)
     (s1' s2' : LayerImplementation.state' ATCCore) 
     r1 r2,
   refines_related ATC_Refinement (AD_related_states u' None) s0 s3 ->
   exec ATCLang u o s0
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)))
     (Finished s1' (Some r1)) ->
   exec ATCLang u o s3
     (Simulation.Definitions.compile ATC_Refinement
        (@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)))
     (Finished s2' (Some r2)) ->
     inum < Inode.InodeAllocatorParams.num_of_blocks ->
   length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
   length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
   (Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s1'))) <->
    Forall (fun a : nat => a < data_length)
      (map fst (fst (snd s2')))).
      Proof.
        Opaque File.extend_inner.
       intros.
       eapply_fresh refines_related_txn_empty in H; cleanup.
       unfold AD_related_states, refines_related in *; simpl in *;
        unfold HC_refines in *; simpl in *;
        unfold TransactionToTransactionalDisk.Definitions.refines,
        FileToFileDisk.Definitions.refines,
        FD_related_states,
        File.files_rep,
        File.files_inner_rep in *;
        logic_clean.
       eapply delete_inner_commit_pre' in H0, H1; subst; eauto.
       cleanup; simpl.
       repeat cleanup_pairs; eauto.
       pose proof file_blocks_fit_in_disk.
       pose proof inodes_before_data.
       unfold File.DiskAllocatorParams.bitmap_addr,
       File.DiskAllocatorParams.num_of_blocks,
       Inode.InodeAllocatorParams.bitmap_addr,
       Inode.InodeAllocatorParams.num_of_blocks in *.
       simpl.
       repeat rewrite app_nil_r; simpl.
       setoid_rewrite H20;
       setoid_rewrite H23.
       repeat rewrite dedup_last_length_not_in_tail_S.
       repeat rewrite rev_repeat.
       assert (A: length (Inode.block_numbers x12) = length (Inode.block_numbers x9)). {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H1;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0;
        eauto; cleanup.
        unfold File.file_map_rep in *; cleanup.
        edestruct H13; eauto.
        edestruct H7; eauto.
        cleanup.
        edestruct H8; logic_clean.
        edestruct H29; eauto.
        lia.
       }
        setoid_rewrite A;
        intuition eauto.
        all: intros Hin; apply in_rev, repeat_spec in Hin; lia.
    Qed.