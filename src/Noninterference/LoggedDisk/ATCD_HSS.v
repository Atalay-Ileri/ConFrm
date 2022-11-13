Require Import Eqdep Lia Lra Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference LoggedDiskRefinement.
Require Import ATC_ORS HSS ATCDLayer ATCD_Simulation ATCD_AOE.
Require Import LogCache_FinishedNotCrashed ATCD_ORS.
Import FileDiskLayer.



Lemma get_inode_compiled_same:
forall u o s1 s1' r1 inum td1,
Transaction.transaction_rep (snd s1) td1 ->
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
    eapply Transaction.read_finished in H4; eauto;
    cleanup; eauto;
    repeat cleanup_pairs; eauto;
    eapply Transaction.read_finished in H2; eauto;
    cleanup; eauto.
    Opaque Inode.get_inode.
  Qed.

Lemma disk_allocator_alloc_exact_txn:
  forall u o s1 s1' r v1 td1,
  Transaction.transaction_rep (snd s1) td1 ->
exec ATCLang u o s1
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
     (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
     (option nat)
     (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.alloc v1)))
  (Finished s1' r) ->
     (r = None) \/ 
     (exists v new_bitmap, 
     r = Some v /\ 
     fst (snd s1') = (File.DiskAllocatorParams.bitmap_addr, new_bitmap) :: (File.DiskAllocatorParams.bitmap_addr + S v, v1) :: fst (snd s1) /\
     snd (snd s1') = snd (snd s1) /\
     v < File.DiskAllocatorParams.num_of_blocks).
     Proof.
      Transparent File.DiskAllocator.alloc.
      unfold File.DiskAllocator.alloc.
      intros; cleanup; simpl in *; repeat invert_exec;
      simpl in *; repeat invert_exec; eauto;
      eapply Transaction.read_finished in H3; eauto;
      cleanup; eauto.
      {
        repeat cleanup_pairs; eauto;
        split_ors; cleanup; try lia.
        eapply Transaction.write_finished in H5; eauto;
        cleanup; eauto;
        repeat split_ors; cleanup; try congruence.
        simpl in *; repeat invert_exec;
        simpl in *;
        eapply Transaction.write_finished in H6; eauto.
        repeat cleanup_pairs; eauto;
        split_ors; cleanup; try lia;
        simpl in *; repeat invert_exec.

        right.
        do 2 eexists; intuition eauto.

        simpl in *; repeat invert_exec.
        repeat cleanup_pairs; eauto.

        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        unfold File.DiskAllocatorParams.bitmap_addr in *; lia.
      }
      {
        simpl in *; repeat invert_exec.
        repeat cleanup_pairs; eauto.
      }
      Opaque File.DiskAllocator.alloc.
    Qed.


Lemma diskallocator_free_exact_txn:
    forall u o s1 s1' r v1 td1,
    Transaction.transaction_rep (snd s1) td1 ->
exec ATCLang u o s1
    (RefinementLift.compile
       (HorizontalComposition AuthenticationOperation
          TransactionCacheOperation)
       (HorizontalComposition AuthenticationOperation
          (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
       (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
       (option unit)
       (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.free v1)))
    (Finished s1' r) ->
       (r = None) \/ 
       (exists new_bitmap, 
       r = Some tt /\ 
       fst (snd s1') = (File.DiskAllocatorParams.bitmap_addr, new_bitmap) :: fst (snd s1) /\
       snd (snd s1') = snd (snd s1)).
       Proof.
        Transparent File.DiskAllocator.free.
        unfold File.DiskAllocator.free.
        intros; cleanup; simpl in *; repeat invert_exec;
        simpl in *; repeat invert_exec; eauto;
        eapply Transaction.read_finished in H3; eauto;
        cleanup; eauto.
        {
          repeat cleanup_pairs; eauto;
          split_ors; cleanup; try lia.
          eapply Transaction.write_finished in H5; eauto;
          cleanup; eauto;
          repeat split_ors; cleanup; try congruence.
          simpl in *; repeat invert_exec;
          simpl in *; eauto.
          eauto.

          pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
          unfold File.DiskAllocatorParams.bitmap_addr in *; lia.
        }
        Opaque File.DiskAllocator.free.
      Qed.


Lemma inode_allocator_alloc_exact_txn:
forall u o s1 s1' r v1 td1,
Transaction.transaction_rep (snd s1) td1 ->
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option nat)
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.alloc v1)))
(Finished s1' r) ->
(r = None) \/ 
(exists v new_bitmap, 
r = Some v /\ 
fst (snd s1') = (Inode.InodeAllocatorParams.bitmap_addr, new_bitmap) :: (Inode.InodeAllocatorParams.bitmap_addr + S v, v1) :: fst (snd s1) /\
snd (snd s1') = snd (snd s1) /\
v < Inode.InodeAllocatorParams.num_of_blocks).
Proof.
Transparent Inode.InodeAllocator.alloc.
unfold Inode.InodeAllocator.alloc.
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto;
eapply Transaction.read_finished in H3; eauto;
cleanup; eauto.
{
repeat cleanup_pairs; eauto;
split_ors; cleanup; try lia.
eapply Transaction.write_finished in H5; eauto;
cleanup; eauto;
repeat split_ors; cleanup; try congruence.
simpl in *; repeat invert_exec;
simpl in *;
eapply Transaction.write_finished in H6; eauto.
repeat cleanup_pairs; eauto;
split_ors; cleanup; try lia;
simpl in *; repeat invert_exec.

right.
do 2 eexists; intuition eauto.

simpl in *; repeat invert_exec.
repeat cleanup_pairs; eauto.

pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
unfold Inode.InodeAllocatorParams.bitmap_addr in *; lia.
}
{
simpl in *; repeat invert_exec.
repeat cleanup_pairs; eauto.
}
Opaque Inode.InodeAllocator.alloc.
Qed.


Lemma free_all_blocks_exact_txn:
forall u l o s1 s1' r td1,
Transaction.transaction_rep (snd s1) td1 ->
exec ATCLang u o s1
(RefinementLift.compile
(HorizontalComposition AuthenticationOperation
TransactionCacheOperation)
(HorizontalComposition AuthenticationOperation
(TransactionalDiskLayer.TDCore data_length)) ATCLang AD
(HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
(option unit)
(@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l)))
(Finished s1' r) ->
(r = None) \/ 
(exists l', 
r = Some tt /\ 
fst (snd s1') = l' ++ fst (snd s1) /\
snd (snd s1') = snd (snd s1) /\
length l' = length l /\
map fst l' = repeat File.DiskAllocatorParams.bitmap_addr (length l)).
Proof.
  induction l; 
intros; cleanup; simpl in *; repeat invert_exec;
simpl in *; repeat invert_exec; eauto.
right; exists []; intuition eauto.

eapply_fresh diskallocator_free_exact_txn in H0; eauto.
eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0; eauto.
cleanup.
eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H0; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
cleanup.
unfold Simulation.Definitions.refines in *; simpl in *.
unfold HC_refines in *; simpl in *.
unfold TransactionToTransactionalDisk.Definitions.refines in *; cleanup.

split_ors; cleanup; try congruence.
eapply IHl in H1; eauto.
split_ors; cleanup; eauto.
right; exists (x5 ++ [(File.DiskAllocatorParams.bitmap_addr, x4)]);
intuition eauto.
rewrite <- app_assoc; eauto.
rewrite app_length; simpl; eauto.
lia.

repeat rewrite map_app.
rewrite repeat_cons.
simpl; eauto.
rewrite H9; eauto.

simpl.
instantiate (1:= (_,_)).
unfold HC_refines in *; simpl in *.
unfold TransactionToTransactionalDisk.Definitions.refines in *; cleanup.
intuition eauto.
eexists (_, _).
unfold HC_refines in *; simpl in *.
unfold TransactionToTransactionalDisk.Definitions.refines in *; cleanup.
intuition eauto.
Unshelve.
exact id.
Qed.

(**XXXXXXXXX**)

Theorem ATC_HSS_transaction_recover:
forall u s1 s2 o1 o2 o3 o4,
((exists s1' s2' r1 r2,
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Finished s1' r1) /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Finished s2' r2)) \/
(exists s1' s2',
exec ATCLang u o1 s1 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Crashed s1') /\
exec ATCLang u o2 s2 (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) (Crashed s2'))) ->
o1 ++ o3 = o2 ++ o4 -> 
ATC_have_same_structure
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover)
  (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ Transaction.recover) u s1 s2.
Proof.
  unfold Transaction.recover; intros.
  split_ors; cleanup.
  {
    repeat (repeat invert_exec; cleanup).
    all: try solve [simpl in *; cleanup].
    {
      repeat rewrite map_app;
      do 4 eexists; intuition eauto.
    }
  }
  {
    repeat (repeat invert_exec; simpl in *; cleanup);
    simpl; intuition eauto;
    repeat invert_exec; simpl in *; cleanup;
    simpl; eauto.
  }
Qed.

Theorem ATC_HSS_transaction_commit:
forall u s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.commit)) in
let p2 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.commit)) in
(length (dedup_last addr_dec (rev (map fst (fst (snd s1))))) =
length (dedup_last addr_dec (rev (map fst (fst (snd s2)))))) ->
(Forall (fun a : nat => a < data_length) (map fst (fst (snd s1))) <->
Forall (fun a : nat => a < data_length) (map fst (fst (snd s2)))) ->
ATC_have_same_structure p1 p2 u s1 s2.
Proof.
  unfold Transaction.commit; simpl; intros; cleanup.
  simpl in *; cleanup; intuition eauto;
  repeat invert_exec.
  eauto.
  repeat rewrite <- dedup_last_dedup_by_list_length_le; eauto;
  repeat rewrite rev_length, map_length; eauto.
  eapply Transaction.dedup_last_NoDup.
  eapply Transaction.dedup_last_NoDup.
  eapply Forall_forall; intros.
  apply Transaction.dedup_last_in, in_rev in H0.
  eapply Forall_forall in H1; eauto.
  eapply Forall_forall; intros.
  eapply in_rev, Transaction.dedup_last_in in H5.
  eapply Forall_forall in H4; eauto.

  eapply Forall_forall; intros.
  apply Transaction.dedup_last_in, in_rev in H0.
  eapply Forall_forall in H2; eauto.
  eapply Forall_forall; intros.
  eapply in_rev, Transaction.dedup_last_in in H5.
  eapply Forall_forall in H4; eauto.
Qed.

Theorem ATC_HSS_transaction_abort:
forall u s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.abort)) in
let p2 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.abort)) in
ATC_have_same_structure p1 p2 u s1 s2.
Proof.
  unfold Transaction.commit; simpl; intros; cleanup.
  simpl in *; cleanup; intuition eauto;
  repeat invert_exec.
Qed.


Theorem ATC_HSS_transaction_read:
forall u s1 s2 a a0,
let p1 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a)) in
let p2 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.read a0)) in
(a < data_length <-> a0 < data_length) ->
(Transaction.get_first (fst (snd s1)) a = None <->  
Transaction.get_first (fst (snd s2)) a0 = None) -> 
ATC_have_same_structure p1 p2 u s1 s2.
Proof.
  unfold Transaction.read; simpl; intros; cleanup.
  destruct (Compare_dec.lt_dec a data_length); 
  destruct (Compare_dec.lt_dec a0 data_length); 
  simpl; eauto; try lia.
  simpl in *; cleanup; intuition eauto.
  repeat invert_exec.
  destruct_fresh (Transaction.get_first (fst (snd s1)) a);
  destruct_fresh (Transaction.get_first (fst (snd s2)) a0);
  simpl; try solve [intuition congruence];
  setoid_rewrite D; setoid_rewrite D0; simpl; intuition eauto.
Qed.

Theorem ATC_HSS_transaction_write:
forall u s1 s2 a a0 v v0, 
let p1 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a v)) in
let p2 := (@lift_L2 AuthenticationOperation _ TransactionCacheLang _ (Transaction.write a0 v0)) in
(a < data_length <-> a0 < data_length) ->
((length (addr_list_to_blocks (map fst (fst (snd s1)) ++ [a])) +
 length (map snd (fst (snd s1)) ++ [v])) <= log_length <->  
 (length (addr_list_to_blocks (map fst (fst (snd s2)) ++ [a0])) +
  length (map snd (fst (snd s2)) ++ [v0])) <= log_length) -> 
ATC_have_same_structure p1 p2 u s1 s2.
Proof.
  unfold Transaction.write; simpl; intros; cleanup.
  destruct (Compare_dec.lt_dec a data_length); 
  destruct (Compare_dec.lt_dec a0 data_length); 
  simpl; eauto; try lia.
  simpl in *; cleanup; intuition eauto.
  repeat invert_exec.
  destruct_fresh (Compare_dec.le_dec
  (length (addr_list_to_blocks (map fst (fst (snd s1)) ++ [a])) +
   length (map snd (fst (snd s1)) ++ [v])) log_length);
  destruct_fresh (Compare_dec.le_dec
  (length (addr_list_to_blocks (map fst (fst (snd s2)) ++ [a0])) +
   length (map snd (fst (snd s2)) ++ [v0])) log_length);
  simpl; try solve [intuition lia];
  setoid_rewrite D; setoid_rewrite D0; simpl; intuition eauto.
Qed.

Theorem ATC_HSS_inodeallocator_read:
forall u inum s1 s2 td1 td2 im1 im2 fm1 fm2 u' ex bm1 bm2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.read inum)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.read inum)) in
(Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
None <->
Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
None) ->
(Transaction.get_first (fst (snd s1)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
None <->
Transaction.get_first (fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
None) ->

Inode.inode_rep im1 (fst (snd td1)) ->
Inode.inode_rep im2 (fst (snd td2)) ->
File.file_map_rep fm1 im1 bm1 ->
File.file_map_rep fm2 im2 bm2 ->
same_for_user_except u' ex fm1 fm2 ->
Transaction.transaction_rep (snd s1) td1 ->
Transaction.transaction_rep (snd s2) td2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  unfold Inode.InodeAllocator.read; simpl; intros; cleanup.
  destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); 
  simpl; eauto.
  simpl in *; cleanup; intuition eauto.
  eapply ATC_HSS_transaction_read; try solve [intuition eauto].
  eapply lift2_invert_exec in H0, H11; cleanup.
  unfold  refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *.
  eapply Transaction.read_finished in H13, H15; eauto.
  cleanup; repeat split_ors; cleanup; try lia.
  
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  erewrite BlockAllocatorExistence.inode_allocations_are_same_2; eauto.
  destruct_fresh (test_bit inum
  (value_to_bits
     (fst (snd td2) Inode.InodeAllocatorParams.bitmap_addr))).

  simpl.

  simpl in *; cleanup; intuition eauto.
  eapply ATC_HSS_transaction_read; try solve [intuition eauto].
  repeat cleanup_pairs; simpl; intuition eauto.
  simpl; intuition eauto.
  repeat rewrite block_allocator_empty; simpl; eauto.
  Unshelve.
Qed.

Set Nested Proofs Allowed.
Lemma refines_related_get_first_none:
  forall u' ex s1 s2 i1 i2,
  refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
  Transaction.get_first (fst (snd s1)) i1 = None <->
  Transaction.get_first (fst (snd s2)) i2 = None.
Proof.
  unfold refines_related in *; simpl in *.
unfold HC_refines in *; simpl in *.
unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *.
intros.
unfold Transaction.transaction_rep in *; simpl in *.

unfold AD_related_states, FD_related_states,
refines_related in *; simpl in *.
unfold FileToFileDisk.Definitions.refines,
File.files_rep, File.files_inner_rep in *;
logic_clean.
repeat cleanup_pairs.
repeat split_ors; cleanup; try congruence.
repeat rewrite map_length in *;
destruct s, s0; simpl in *; eauto; try lia.
intuition eauto.
Qed.

  Theorem ATC_HSS_diskallocator_read:
  forall u u' ex (s1 s2: state ATCLang) a a0,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read a)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read a0)) in
  (a < File.DiskAllocatorParams.num_of_blocks <-> 
  a0 < File.DiskAllocatorParams.num_of_blocks) ->
  test_bit a
            (value_to_bits
               ((snd (snd s1)) File.DiskAllocatorParams.bitmap_addr)) =
  test_bit a0
            (value_to_bits
               ((snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) ->
  refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold File.DiskAllocator.read; simpl; intros; cleanup.
    destruct (Compare_dec.lt_dec a File.DiskAllocatorParams.num_of_blocks); 
    destruct (Compare_dec.lt_dec a0 File.DiskAllocatorParams.num_of_blocks); 
    try lia; simpl; eauto.
    simpl in *; cleanup; intuition eauto.
    eapply ATC_HSS_transaction_read; try solve [intuition eauto].
    eapply refines_related_get_first_none; eauto.

    eapply lift2_invert_exec in H3, H4; cleanup.
    unfold  refines_related in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *.
    logic_clean.
    eapply Transaction.read_finished in H6, H8; eauto.
    cleanup; repeat split_ors; cleanup; try lia.
    repeat cleanup_pairs; cleanup.

    unfold Transaction.transaction_rep in *; simpl in *.
    
    unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
    simpl in *; cleanup.
    destruct_fresh (test_bit a0
            (value_to_bits
               (snd (snd s0) File.DiskAllocatorParams.bitmap_addr)));
    simpl in *; cleanup; eauto.
    repeat split; eauto.
    eapply ATC_HSS_transaction_read; try solve [intuition eauto].
    pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
    unfold File.DiskAllocatorParams.bitmap_addr,
    File.DiskAllocatorParams.num_of_blocks in *; 
    lia.

    simpl; repeat split_ors; cleanup; try congruence.
    repeat rewrite map_length in *; destruct s2, s4;
    simpl in *; try lia.
    intuition eauto.
    repeat rewrite block_allocator_empty; simpl; eauto.
    Unshelve.
    Qed.


    Theorem ATC_HSS_inodeallocator_alloc:
    forall u u' ex (s1 s2: state ATCLang) v v0,
    let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.alloc v)) in
    let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.alloc v0)) in
    refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
    ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
    (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
    Proof.
      Transparent Inode.InodeAllocator.alloc.
      unfold Inode.InodeAllocator.alloc; simpl; intros; cleanup.
      simpl in *; cleanup; intuition eauto.
      eapply ATC_HSS_transaction_read; try solve [intuition eauto].
      eapply refines_related_get_first_none; eauto.

      eapply lift2_invert_exec in H0, H1; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
      cleanup.
      eapply Transaction.read_finished in H3, H5; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      2: { pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
      unfold Inode.InodeAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.num_of_blocks in *; 
      lia. 
      }
      repeat cleanup_pairs; cleanup.
      
      unfold AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      unfold FileToFileDisk.Definitions.refines,
      File.files_rep in *;
      logic_clean.
      simpl in *; cleanup.
      eapply_fresh BlockAllocatorExistence.free_block_exists_iff_inode in H4; eauto.
      destruct (Compare_dec.lt_dec
      (get_first_zero_index
         (value_to_bits (snd (snd s3) Inode.InodeAllocatorParams.bitmap_addr)))
         Inode.InodeAllocatorParams.num_of_blocks);
      destruct (Compare_dec.lt_dec
      (get_first_zero_index
         (value_to_bits (snd (snd s0) Inode.InodeAllocatorParams.bitmap_addr)))
         Inode.InodeAllocatorParams.num_of_blocks);
      try lia.

      assert (A: length
      (addr_list_to_blocks
         (map fst (fst s4) ++
          [Inode.InodeAllocatorParams.bitmap_addr +
           S
             (get_first_zero_index
                (value_to_bits (snd (snd s3) Inode.InodeAllocatorParams.bitmap_addr)))])) +
    length (map snd (fst s4) ++ [v]) <= log_length <->
    length
      (addr_list_to_blocks
         (map fst (fst s5) ++
          [Inode.InodeAllocatorParams.bitmap_addr +
           S
             (get_first_zero_index
                (value_to_bits (snd (snd s0) Inode.InodeAllocatorParams.bitmap_addr)))])) +
    length (map snd (fst s5) ++ [v0]) <= log_length). {
        simpl.
        repeat cleanup_pairs; simpl in *.
        unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
        refines_related in *; simpl in *.
        repeat cleanup_pairs; simpl in *.
        
        unfold Transaction.transaction_rep in *;
        logic_clean; simpl in *.
        repeat cleanup_pairs; simpl in *.

        repeat rewrite map_length in *;
        destruct s0, s2; simpl in *; 
        repeat split_ors; 
        cleanup; try congruence; try lia.
        {
          erewrite addr_list_to_blocks_length_eq with (l_b := ([Inode.InodeAllocatorParams.bitmap_addr +
          S (get_first_zero_index (value_to_bits (s1 Inode.InodeAllocatorParams.bitmap_addr)))])).
          intuition eauto.
          simpl; eauto. 
        }
      }

      simpl; intuition eauto.
      eapply ATC_HSS_transaction_write.
      {
        repeat cleanup_pairs; simpl in *.
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
        unfold Inode.InodeAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.num_of_blocks in *; 
        lia.
      }
      {
        simpl; intuition eauto.
      }

      eapply lift2_invert_exec in H11, H15; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      eapply Transaction.write_finished in H17, H19; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      {
        simpl; intuition eauto.
        eapply ATC_HSS_transaction_write.
        intuition.
        {
          repeat cleanup_pairs; simpl in *.
          unfold Transaction.transaction_rep in *;
          logic_clean; simpl in *.
          repeat cleanup_pairs; simpl in *.

          repeat (split_ors; cleanup; try congruence; try lia).
          repeat rewrite map_length in *;
          destruct s, s2; simpl in *; try lia.
          {
              erewrite addr_list_to_blocks_length_eq with (l_b := ([Inode.InodeAllocatorParams.bitmap_addr +
              S
                (get_first_zero_index
                  (value_to_bits (s4 Inode.InodeAllocatorParams.bitmap_addr)));
                  Inode.InodeAllocatorParams.bitmap_addr])).
              intuition eauto.
              simpl; eauto. 
          }
        }
        destruct r1, r2;
        try destruct u0;
        try destruct u1; simpl; eauto.
      }
      {
        split_ors; cleanup.
        
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
        unfold Inode.InodeAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.num_of_blocks in *; 
        lia.

        exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
      }
      {
        split_ors; cleanup.
        
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
        unfold Inode.InodeAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.num_of_blocks in *; 
        lia.

        exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
      }
      simpl; eauto.
      simpl; eauto.
      Unshelve.
      Opaque Inode.InodeAllocator.alloc.
    Qed.


    Theorem ATC_HSS_diskallocator_alloc:
    forall u u' ex (s1 s2: state ATCLang) v v0,
    let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.alloc v)) in
    let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.alloc v0)) in
    refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
    ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
    (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
    Proof.
      Transparent File.DiskAllocator.alloc.
      unfold File.DiskAllocator.alloc; simpl; intros; cleanup.
      simpl in *; cleanup; intuition eauto.
      eapply ATC_HSS_transaction_read; try solve [intuition eauto].
      eapply refines_related_get_first_none; eauto.

      eapply lift2_invert_exec in H0, H1; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
      cleanup.
      eapply Transaction.read_finished in H3, H5; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      2: { pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
      unfold File.DiskAllocatorParams.bitmap_addr,
      File.DiskAllocatorParams.num_of_blocks in *; 
      lia. 
      }
      repeat cleanup_pairs; cleanup.
      
      unfold AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      unfold FileToFileDisk.Definitions.refines,
      File.files_rep in *;
      logic_clean.
      simpl in *; cleanup.
      eapply_fresh BlockAllocatorExistence.free_block_exists_iff in H4; eauto.
      destruct (Compare_dec.lt_dec
      (get_first_zero_index
         (value_to_bits (snd (snd s3) File.DiskAllocatorParams.bitmap_addr)))
      File.DiskAllocatorParams.num_of_blocks);
      destruct (Compare_dec.lt_dec
      (get_first_zero_index
         (value_to_bits (snd (snd s0) File.DiskAllocatorParams.bitmap_addr)))
      File.DiskAllocatorParams.num_of_blocks);
      try lia.

      assert (A: length
      (addr_list_to_blocks
         (map fst (fst s4) ++
          [File.DiskAllocatorParams.bitmap_addr +
           S
             (get_first_zero_index
                (value_to_bits (snd (snd s3) File.DiskAllocatorParams.bitmap_addr)))])) +
    length (map snd (fst s4) ++ [v]) <= log_length <->
    length
      (addr_list_to_blocks
         (map fst (fst s5) ++
          [File.DiskAllocatorParams.bitmap_addr +
           S
             (get_first_zero_index
                (value_to_bits (snd (snd s0) File.DiskAllocatorParams.bitmap_addr)))])) +
    length (map snd (fst s5) ++ [v0]) <= log_length). {
        simpl.
        repeat cleanup_pairs; simpl in *.
        unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
        refines_related in *; simpl in *.
        repeat cleanup_pairs; simpl in *.
        
        unfold Transaction.transaction_rep in *;
        logic_clean; simpl in *.
        repeat cleanup_pairs; simpl in *.

        repeat rewrite map_length in *;
        destruct s0, s2; simpl in *; 
        repeat split_ors; 
        cleanup; try congruence; try lia.
        {
          erewrite addr_list_to_blocks_length_eq with (l_b := ([File.DiskAllocatorParams.bitmap_addr +
          S (get_first_zero_index (value_to_bits (s1 File.DiskAllocatorParams.bitmap_addr)))])).
          intuition eauto.
          simpl; eauto. 
        }
      }

      simpl; intuition eauto.
      eapply ATC_HSS_transaction_write.
      {
        repeat cleanup_pairs; simpl in *.
        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        unfold File.DiskAllocatorParams.bitmap_addr,
        File.DiskAllocatorParams.num_of_blocks in *; 
        lia.
      }
      {
        simpl; intuition eauto.
      }

      eapply lift2_invert_exec in H11, H15; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      eapply Transaction.write_finished in H17, H19; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      {
        simpl; intuition eauto.
        eapply ATC_HSS_transaction_write.
        intuition.
        {
          repeat cleanup_pairs; simpl in *.
          unfold Transaction.transaction_rep in *;
          logic_clean; simpl in *.
          repeat cleanup_pairs; simpl in *.

          repeat (split_ors; cleanup; try congruence; try lia).
          repeat rewrite map_length in *;
          destruct s, s2; simpl in *; try lia.
          {
              erewrite addr_list_to_blocks_length_eq with (l_b := ([File.DiskAllocatorParams.bitmap_addr +
              S
                (get_first_zero_index
                  (value_to_bits (s4 File.DiskAllocatorParams.bitmap_addr)));
            File.DiskAllocatorParams.bitmap_addr])).
              intuition eauto.
              simpl; eauto. 
          }
        }
        destruct r1, r2;
        try destruct u0;
        try destruct u1; simpl; eauto.
      }
      {
        split_ors; cleanup.
        
        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        unfold File.DiskAllocatorParams.bitmap_addr,
        File.DiskAllocatorParams.num_of_blocks in *; 
        lia.

        exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
      }
      {
        split_ors; cleanup.
        
        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        unfold File.DiskAllocatorParams.bitmap_addr,
        File.DiskAllocatorParams.num_of_blocks in *; 
        lia.

        exfalso; eapply PeanoNat.Nat.lt_nge; eauto.
      }
      simpl; eauto.
      simpl; eauto.
      Unshelve.
      Opaque File.DiskAllocator.alloc.
    Qed.

    Theorem ATC_HSS_inodeallocator_write:
    forall u (s1 s2: state ATCLang) a v v0 td1 td2,
    let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.write a v)) in
    let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.write a v0)) in
    (Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
    None <->
    Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
    None) ->
    test_bit a
              (value_to_bits
                 ((fst (snd td1)) Inode.InodeAllocatorParams.bitmap_addr)) =
    test_bit a
              (value_to_bits
                 ((fst (snd td2)) Inode.InodeAllocatorParams.bitmap_addr)) ->
    Transaction.transaction_rep (snd s1) td1 ->
    Transaction.transaction_rep (snd s2) td2 ->
    (length
    (addr_list_to_blocks
       (map fst (fst (snd s1)) ++
        [Inode.InodeAllocatorParams.bitmap_addr + S a])) +
  length (map snd (fst (snd s1)) ++ [v]) <= log_length <->
  length
    (addr_list_to_blocks
       (map fst (fst (snd s2)) ++
        [Inode.InodeAllocatorParams.bitmap_addr + S a])) +
  length (map snd (fst (snd s2)) ++ [v0]) <= log_length) ->
    ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
    (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
    Proof.
      unfold Inode.InodeAllocator.write; simpl; intros; cleanup.
      destruct (Compare_dec.lt_dec a Inode.InodeAllocatorParams.num_of_blocks); 
      try lia; simpl; eauto.
      simpl in *; cleanup; intuition eauto.
      eapply ATC_HSS_transaction_read; try solve [intuition eauto].
      eapply lift2_invert_exec in H3, H7; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      eapply Transaction.read_finished in H9, H11; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      setoid_rewrite H0.
      destruct_fresh (test_bit a
              (value_to_bits
                 (fst (snd td2) Inode.InodeAllocatorParams.bitmap_addr)));
      setoid_rewrite D;
      simpl in *; cleanup; eauto.
      repeat split; eauto.
      eapply ATC_HSS_transaction_write; try solve [intuition eauto].
      repeat cleanup_pairs; intuition eauto.
      repeat rewrite block_allocator_empty; simpl; eauto.
      Unshelve.
      Qed.



    Theorem ATC_HSS_diskallocator_write:
    forall u (s1 s2: state ATCLang) a a0 v v0 td1 td2,
    let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.write a v)) in
    let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.write a0 v0)) in
    (a < File.DiskAllocatorParams.num_of_blocks <-> 
    a0 < File.DiskAllocatorParams.num_of_blocks) ->
    test_bit a
              (value_to_bits
                 ((fst (snd td1)) File.DiskAllocatorParams.bitmap_addr)) =
    test_bit a0
              (value_to_bits
                 ((fst (snd td2)) File.DiskAllocatorParams.bitmap_addr)) ->
    (Transaction.get_first (fst (snd s1)) File.DiskAllocatorParams.bitmap_addr =
    None <->
    Transaction.get_first (fst (snd s2)) File.DiskAllocatorParams.bitmap_addr =
    None) ->
    (length
    (addr_list_to_blocks
       (map fst (fst (snd s1)) ++ [File.DiskAllocatorParams.bitmap_addr + S a])) +
  length (map snd (fst (snd s1)) ++ [v]) <= log_length <->
  length
    (addr_list_to_blocks
       (map fst (fst (snd s2)) ++ [File.DiskAllocatorParams.bitmap_addr + S a0])) +
  length (map snd (fst (snd s2)) ++ [v0]) <= log_length) ->
    Transaction.transaction_rep (snd s1) td1 ->
    Transaction.transaction_rep (snd s2) td2 ->
    ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
    (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
    Proof.
      unfold File.DiskAllocator.write; simpl; intros; cleanup.
      destruct (Compare_dec.lt_dec a File.DiskAllocatorParams.num_of_blocks); 
      destruct (Compare_dec.lt_dec a0 File.DiskAllocatorParams.num_of_blocks); 
      try lia; simpl; eauto.
      simpl in *; cleanup; intuition eauto.
      eapply ATC_HSS_transaction_read; try solve [intuition eauto].

      eapply lift2_invert_exec in H6, H9; cleanup.
      unfold refines_related in *; simpl in *.
      unfold HC_refines in *; simpl in *.
      eapply Transaction.read_finished in H11, H13; eauto.
      cleanup; repeat split_ors; cleanup; try lia.
      repeat cleanup_pairs; cleanup.
      simpl; cleanup.
      cleanup.
      destruct_fresh (test_bit a0
              (value_to_bits
                 (v2 File.DiskAllocatorParams.bitmap_addr)));
      simpl in *; cleanup; eauto.
      repeat split; eauto.
      eapply ATC_HSS_transaction_write; try solve [intuition eauto].
      pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
      unfold File.DiskAllocatorParams.bitmap_addr,
      File.DiskAllocatorParams.num_of_blocks in *; 
      lia.
      repeat rewrite block_allocator_empty; simpl; eauto.
      Unshelve.
      Qed.

Theorem ATC_HSS_diskallocator_free:
forall u (s1 s2: state ATCLang) a a0 td1 td2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.free a)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.free a0)) in
(a < File.DiskAllocatorParams.num_of_blocks <-> 
a0 < File.DiskAllocatorParams.num_of_blocks) ->
test_bit a
          (value_to_bits
              ((fst (snd td1)) File.DiskAllocatorParams.bitmap_addr)) =
test_bit a0
          (value_to_bits
              ((fst (snd td2)) File.DiskAllocatorParams.bitmap_addr)) ->
(Transaction.get_first (fst (snd s1)) File.DiskAllocatorParams.bitmap_addr =
None <->
Transaction.get_first (fst (snd s2)) File.DiskAllocatorParams.bitmap_addr =
None) ->
Transaction.transaction_rep (snd s1) td1 ->
Transaction.transaction_rep (snd s2) td2 ->
length (fst (snd s1)) = length (fst (snd s2)) ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  Transparent File.DiskAllocator.free.
  unfold File.DiskAllocator.free; simpl; intros; cleanup.
  destruct (Compare_dec.lt_dec a File.DiskAllocatorParams.num_of_blocks); 
  destruct (Compare_dec.lt_dec a0 File.DiskAllocatorParams.num_of_blocks); 
  try lia; simpl; eauto.
  simpl in *; cleanup; intuition eauto.
  eapply ATC_HSS_transaction_read; try solve [intuition eauto].

  eapply lift2_invert_exec in H6, H8; cleanup.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  eapply Transaction.read_finished in H10, H12; eauto.
  cleanup; repeat split_ors; cleanup; try lia.
  repeat cleanup_pairs; cleanup.
  simpl; cleanup.
  cleanup.
  destruct_fresh (test_bit a0
          (value_to_bits
              (v0 File.DiskAllocatorParams.bitmap_addr)));
  simpl in *; cleanup; eauto.
  repeat split; eauto.
  eapply ATC_HSS_transaction_write; try solve [intuition eauto].
  {
    simpl.
    repeat rewrite app_length, map_length; simpl.
    erewrite addr_list_to_blocks_length_eq.
    setoid_rewrite H4; intuition eauto.
    repeat rewrite app_length, map_length; simpl; eauto.
  }
  repeat rewrite block_allocator_empty; simpl; eauto.
  Unshelve.
  Opaque File.DiskAllocator.free.
  Qed.
        

  Theorem ATC_HSS_inodeallocator_free:
  forall u (s1 s2: state ATCLang) a a0 td1 td2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.free a)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.free a0)) in
  (a < Inode.InodeAllocatorParams.num_of_blocks <-> 
  a0 < Inode.InodeAllocatorParams.num_of_blocks) ->
  test_bit a
            (value_to_bits
                ((fst (snd td1)) Inode.InodeAllocatorParams.bitmap_addr)) =
  test_bit a0
            (value_to_bits
                ((fst (snd td2)) Inode.InodeAllocatorParams.bitmap_addr)) ->
  (Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
  None <->
  Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
  None) ->
  Transaction.transaction_rep (snd s1) td1 ->
  Transaction.transaction_rep (snd s2) td2 ->
  length (fst (snd s1)) = length (fst (snd s2)) ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold Inode.InodeAllocator.free; simpl; intros; cleanup.
    destruct (Compare_dec.lt_dec a Inode.InodeAllocatorParams.num_of_blocks); 
    destruct (Compare_dec.lt_dec a0 Inode.InodeAllocatorParams.num_of_blocks); 
    try lia; simpl; eauto.
    simpl in *; cleanup; intuition eauto.
    eapply ATC_HSS_transaction_read; try solve [intuition eauto].
  
    eapply lift2_invert_exec in H6, H8; cleanup.
    unfold refines_related in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    eapply Transaction.read_finished in H10, H12; eauto.
    cleanup; repeat split_ors; cleanup; try lia.
    repeat cleanup_pairs; cleanup.
    simpl; cleanup.
    cleanup.
    destruct_fresh (test_bit a0
            (value_to_bits
                (v0 Inode.InodeAllocatorParams.bitmap_addr)));
    simpl in *; cleanup; eauto.
    repeat split; eauto.
    eapply ATC_HSS_transaction_write; try solve [intuition eauto].
    {
      simpl.
      repeat rewrite app_length, map_length; simpl.
      erewrite addr_list_to_blocks_length_eq.
      setoid_rewrite H4; intuition eauto.
      repeat rewrite app_length, map_length; simpl; eauto.
    }
    repeat rewrite block_allocator_empty; simpl; eauto.
    Unshelve.
    Qed.


  Theorem ATC_HSS_inode_get_inode:
  forall u inum s1 s2 td1 td2 im1 im2 fm1 fm2 u' ex bm1 bm2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum)) in
  
  (Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
  None <->
  Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
  None) ->
  (Transaction.get_first (fst (snd s1)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
  None <->
  Transaction.get_first (fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
  None) ->
  Inode.inode_rep im1 (fst (snd td1)) ->
  Inode.inode_rep im2 (fst (snd td2)) ->
  File.file_map_rep fm1 im1 bm1 ->
  File.file_map_rep fm2 im2 bm2 ->
  same_for_user_except u' ex fm1 fm2 ->
  Transaction.transaction_rep (snd s1) td1 ->
  Transaction.transaction_rep (snd s2) td2 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    Transparent Inode.get_inode.
    unfold Inode.get_inode; simpl; intros; cleanup.
    intuition eauto.
    eapply ATC_HSS_inodeallocator_read. 
    8: eauto.
    8: eauto.
    8: eauto.
    all: try solve [intuition eauto].
    destruct r1, r2; simpl; eauto.
    Opaque Inode.get_inode.
  Qed.


  Theorem ATC_HSS_inode_set_inode:
  forall u inum s1 s2 td1 td2 i1 i2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.set_inode inum i1)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.set_inode inum i2)) in
  
  (Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
  None <->
  Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
  None) ->
  test_bit inum
            (value_to_bits
                ((fst (snd td1)) Inode.InodeAllocatorParams.bitmap_addr)) =
  test_bit inum
            (value_to_bits
                ((fst (snd td2)) Inode.InodeAllocatorParams.bitmap_addr)) ->
  (length
  (addr_list_to_blocks
     (map fst (fst (snd s1)) ++
      [Inode.InodeAllocatorParams.bitmap_addr + S inum])) +
length (map snd (fst (snd s1)) ++ [Inode.encode_inode i1]) <= log_length <->
length
  (addr_list_to_blocks
     (map fst (fst (snd s2)) ++
      [Inode.InodeAllocatorParams.bitmap_addr + S inum])) +
length (map snd (fst (snd s2)) ++ [Inode.encode_inode i2]) <= log_length) ->
  Transaction.transaction_rep (snd s1) td1 ->
  Transaction.transaction_rep (snd s2) td2 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold Inode.set_inode; simpl; intros; cleanup.
    eapply ATC_HSS_inodeallocator_write. 
    3: eauto.
    3: eauto.
    all: try solve [intuition eauto].
    Opaque Inode.set_inode.
  Qed.


  Theorem ATC_HSS_inode_extend:
  forall u inum s1 s2 td1 td2 im1 im2 fm1 fm2 u' ex bm1 bm2 bn1 bn2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.extend inum bn1)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.extend inum bn2)) in
  
  (Transaction.get_first (fst (snd s1)) Inode.InodeAllocatorParams.bitmap_addr =
  None <->
  Transaction.get_first (fst (snd s2)) Inode.InodeAllocatorParams.bitmap_addr =
  None) ->
  (Transaction.get_first (fst (snd s1)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
  None <->
  Transaction.get_first (fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum) =
  None) ->
  Inode.inode_rep im1 (fst (snd td1)) ->
  Inode.inode_rep im2 (fst (snd td2)) ->
  File.file_map_rep fm1 im1 bm1 ->
  File.file_map_rep fm2 im2 bm2 ->
  same_for_user_except u' ex fm1 fm2 ->
  Transaction.transaction_rep (snd s1) td1 ->
  Transaction.transaction_rep (snd s2) td2 ->
  length (fst (snd s1)) = length (fst (snd s2)) -> 
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    Transparent Inode.extend.
    unfold Inode.extend; simpl; intros; cleanup.
    intuition eauto.
    eapply ATC_HSS_inode_get_inode.
    8: eauto. 
    8: eauto. 
    8: eauto.
    all: try solve [intuition eauto].
    unfold refines_related in *; simpl in *.
    cleanup.
    eapply_fresh get_inode_compiled_same in H0;
    eapply_fresh get_inode_compiled_same in H12; eauto; cleanup.

    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H12; eauto.
    cleanup.
    eapply ATC_Simulation.ATC_exec_lift_finished in H0, H12; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.
    all: try instantiate (1:= (_, _)); simpl; unfold HC_refines; simpl;
    unfold TransactionToTransactionalDisk.Definitions.refines; 
    try split; eauto; try solve [eexists (_, _); intuition eauto].

    eapply lift2_invert_exec in H0; cleanup.
    eapply lift2_invert_exec in H12; cleanup.
    unfold AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
    eapply Inode.get_inode_finished_precise in H18; eauto.
    eapply Inode.get_inode_finished_precise in H19; eauto.
    cleanup.
    repeat split_ors; cleanup.
    repeat cleanup_pairs.
    eapply ATC_HSS_inode_set_inode.
    4: eauto.
    4: eauto.
    all: simpl; eauto.
    {
      unfold HC_refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      intuition eauto.
    }
    {
      eapply BlockAllocatorExistence.inode_allocations_are_same; eauto.
      destruct H5.
      unfold File.file_map_rep in *; logic_clean.
      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    }
    {
      repeat rewrite app_length, map_length; simpl.
      erewrite addr_list_to_blocks_length_eq.
      rewrite H8; intuition eauto.
      repeat rewrite app_length, map_length; simpl; lia.
    }
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H19; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H21; eauto.
        cleanup.
        edestruct H5.
        edestruct H18.
        intuition; eauto.
        exfalso; eapply H23; intuition eauto.
        congruence.
      }
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H20; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H19; eauto.
        cleanup.
        edestruct H5.
        edestruct H18.
        intuition; eauto.
        exfalso; eapply H22; intuition eauto.
        congruence.
      }
      Unshelve.
      all: exact id.
      Opaque Inode.extend.
    Qed.

Theorem ATC_HSS_inode_get_block_number:
forall u u' ex inum off s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)) in

refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  Transparent Inode.get_block_number.
  unfold Inode.get_block_number; simpl; intros; cleanup.
  intuition eauto.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  logic_clean.
  simpl in *; cleanup.
  repeat cleanup_pairs.
  eapply ATC_HSS_inode_get_inode.
  7: eauto.
  7: eauto.
  7: eauto.
  all: eauto.
  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  destruct r1, r2; simpl; eauto.
  Opaque Inode.get_block_number.
Qed.


Theorem ATC_HSS_inode_get_all_block_numbers:
forall u u' ex inum s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_all_block_numbers inum)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_all_block_numbers inum)) in

refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  Transparent Inode.get_all_block_numbers.
  unfold Inode.get_all_block_numbers; simpl; intros; cleanup.
  intuition eauto.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  logic_clean.
  simpl in *; cleanup.
  repeat cleanup_pairs.
  eapply ATC_HSS_inode_get_inode.
  7: eauto.
  7: eauto.
  7: eauto.
  all: eauto.
  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  destruct r1, r2; simpl; eauto.
  Opaque Inode.get_all_block_numbers.
Qed.

Theorem ATC_HSS_inode_get_owner:
forall u u' ex inum s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum )) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum )) in

refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  Transparent Inode.get_owner.
  unfold Inode.get_owner; simpl; intros; cleanup.
  intuition eauto.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  logic_clean.
  simpl in *; cleanup.
  repeat cleanup_pairs.
  eapply ATC_HSS_inode_get_inode.
  7: eauto.
  7: eauto.
  7: eauto.
  all: eauto.
  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  eapply refines_related_get_first_none.
  unfold refines_related in *; simpl in *.
  unfold HC_refines in *; simpl in *.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *;
  cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  simpl in *; cleanup.
  eexists (_, _), (_, _).
  intuition eauto.
  simpl; do 2 eexists; intuition eauto.

  destruct r1, r2; simpl; eauto.
  Opaque Inode.get_owner.
Qed.

Theorem ATC_HSS_read_inner:
forall u u' ex inum off s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)) in

refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  simpl; intros; cleanup.
  intuition eauto.
  eapply ATC_HSS_inode_get_block_number; eauto.
  unfold refines_related in *; simpl in *.
  cleanup.

  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0;
  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto.
  cleanup.

  eapply ATC_Simulation.ATC_exec_lift_finished in H0, H1; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

  eapply lift2_invert_exec in H0; cleanup.
  eapply lift2_invert_exec in H1; cleanup.
  unfold AD_related_states, FD_related_states,
  refines_related in *; simpl in *.
  unfold FileToFileDisk.Definitions.refines,
  File.files_rep, File.files_inner_rep in *;
  logic_clean.
  eapply Inode.get_block_number_finished_precise in H9; eauto.
  eapply Inode.get_block_number_finished_precise in H10; eauto.
  cleanup.
  destruct H9, H10; cleanup; try congruence; try lia.
  unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
  unfold TransactionToTransactionalDisk.Definitions.refines,
  refines_related in *; simpl in *.
  intuition eauto.
   eapply ATC_HSS_diskallocator_read; eauto.
   {
      repeat cleanup_pairs; simpl in *.
      eapply SameRetType.all_block_numbers_in_bound in H23, H25; eauto.
      intuition.
      eapply Forall_forall in H23; eauto.
      apply in_seln; eauto.
      eapply Forall_forall in H25; eauto.
      apply in_seln; eauto.
    }
    {
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      destruct H1, H8, H22, H24; logic_clean; try congruence. 
      repeat erewrite BlockAllocatorExistence.used_blocks_are_allocated_2.
      eauto.
      4: eauto.
      8: eauto.
      all: eauto.
      all: try rewrite <-H16; 
      try rewrite <- H3; eauto.
    }
    {
      unfold refines_related in *; simpl in *.
      unfold AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      unfold FileToFileDisk.Definitions.refines,
      File.files_rep, File.files_inner_rep in *.
      unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      refines_related in *; simpl in *.
      eexists (_, _), (_, _).
      simpl; intuition eauto.
      repeat cleanup_pairs.
      do 2 eexists; intuition eauto.
    }
    destruct r1, r2; simpl; eauto.
    {
      repeat split_ors; cleanup; try lia.
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H24; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H10; eauto.
        cleanup.
        edestruct H11.
        edestruct H23.
        intuition; eauto.
        exfalso; eapply H25; intuition eauto.
        congruence.
      }
      {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H24; eauto.
        cleanup.
        edestruct H11; cleanup.
        eapply_fresh H28 in H23; eauto; cleanup.
        unfold File.file_map_rep in *; logic_clean.
        eapply H31 in H25;
        eapply H33 in H23;
        eauto.
        unfold File.file_rep in *; cleanup.
        lia.
      }
    }
    {
      repeat split_ors; cleanup; try lia.
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H23; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H9; eauto.
        cleanup.
        edestruct H11.
        edestruct H23.
        intuition; eauto.
        exfalso; eapply H26; intuition eauto.
        congruence.
      }
      {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H9;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto.
        cleanup.
        edestruct H11; cleanup.
        eapply_fresh H28 in H24; eauto; cleanup.
        unfold File.file_map_rep in *; logic_clean.
        eapply H31 in H24;
        eapply H33 in H25;
        eauto.
        unfold File.file_rep in *; cleanup.
        lia.
      }
    }
    simpl; eauto.
    Unshelve.
    all: exact id.
Qed.

  Theorem ATC_HSS_write_inner:
  forall u u' ex inum off v1 v2 s1 s2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v1 inum)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v2 inum)) in
  
  refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    simpl; intros; cleanup.
    intuition eauto.
    eapply ATC_HSS_inode_get_block_number; eauto.
    unfold refines_related in *; simpl in *.
    cleanup.

    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto.
    cleanup.
    eapply ATC_Simulation.ATC_exec_lift_finished in H0, H1; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

    eapply lift2_invert_exec in H0; cleanup.
    eapply lift2_invert_exec in H1; cleanup.
    unfold AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      unfold FileToFileDisk.Definitions.refines,
      File.files_rep, File.files_inner_rep in *;
      logic_clean.
    eapply Inode.get_block_number_finished in H9; eauto.
    eapply Inode.get_block_number_finished in H10; eauto.
    cleanup.
    destruct H9, H10; cleanup; try congruence; try lia.
    unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    refines_related in *; simpl in *.
    eapply ATC_HSS_diskallocator_write; eauto.
    {
      repeat cleanup_pairs; simpl in *.
      eapply SameRetType.all_block_numbers_in_bound in H29, H31; eauto.
      intuition.
      eapply Forall_forall in H29; eauto.
      apply in_seln; eauto.
      eapply Forall_forall in H31; eauto.
      apply in_seln; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
    }
    {
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat cleanup_pairs; simpl in *.
      repeat erewrite BlockAllocatorExistence.used_blocks_are_allocated_2; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
    }
    {
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat cleanup_pairs; simpl in *.
      eauto.
      repeat split_ors; cleanup; try congruence.
      repeat rewrite map_length in *;
      destruct s, s0; simpl in *; try lia.
      intuition eauto.
    }
    {
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat cleanup_pairs; simpl in *.
      eauto.
      repeat split_ors; cleanup; try congruence.
      repeat rewrite map_length in *;
      destruct s, s0; simpl in *; try lia.
      erewrite addr_list_to_blocks_length_eq with (l_b := [File.DiskAllocatorParams.bitmap_addr +
      S (seln (Inode.block_numbers x11) off 0)]); simpl; eauto.
      intuition eauto.
    }
    {
      repeat split_ors; cleanup; try lia.
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H30; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H10; eauto.
        cleanup.
        edestruct H11.
        edestruct H29.
        intuition; eauto.
        exfalso; eapply H31; intuition eauto.
        congruence.
      }
      {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H10;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H30; eauto.
        cleanup.
        edestruct H11; cleanup.
        eapply_fresh H34 in H29; eauto; cleanup.
        unfold File.file_map_rep in *; logic_clean.
        eapply H37 in H31;
        eapply H39 in H29;
        eauto.
        unfold File.file_rep in *; cleanup.
        lia.
      }
    }
    {
      repeat split_ors; cleanup; try lia.
      {
        eapply FileInnerSpecs.inode_exists_then_file_exists in H29; eauto.
        eapply FileInnerSpecs.inode_missing_then_file_missing in H9; eauto.
        cleanup.
        edestruct H11.
        edestruct H29.
        intuition; eauto.
        exfalso; eapply H32; intuition eauto.
        congruence.
      }
      {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H9;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H29; eauto.
        cleanup.
        edestruct H11; cleanup.
        eapply_fresh H34 in H30; eauto; cleanup.
        unfold File.file_map_rep in *; logic_clean.
        eapply H37 in H30;
        eapply H39 in H31;
        eauto.
        unfold File.file_rep in *; cleanup.
        lia.
      }
    }
    simpl; eauto.
    Unshelve.
    all: exact id.
Qed.

Theorem ATC_HSS_change_owner_inner:
forall u u' ex inum off s1 s2,
let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner off inum)) in
let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner off inum)) in

refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
(ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
Proof.
  Transparent Inode.change_owner.
  unfold File.change_owner_inner, Inode.change_owner; simpl; intros; cleanup.
  intuition eauto.
  eapply ATC_HSS_inode_get_block_number; eauto.
  unfold refines_related in *; simpl in *.
  cleanup.

  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0;
  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto.
  cleanup.
  eapply ATC_Simulation.ATC_exec_lift_finished in H0, H1; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  cleanup.

  eapply lift2_invert_exec in H0; cleanup.
  eapply lift2_invert_exec in H1; cleanup.
  unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
  eapply Inode.get_inode_finished_precise in H9; eauto.
  eapply Inode.get_inode_finished_precise in H10; eauto.
  cleanup.
  destruct H9, H10; cleanup; try congruence; try lia.
  unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
  unfold TransactionToTransactionalDisk.Definitions.refines,
  refines_related in *; simpl in *.
  eapply ATC_HSS_inode_set_inode. 
  4: eauto. 
  4: eauto. 
  all: eauto.
  {
    repeat cleanup_pairs; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    repeat cleanup_pairs; simpl in *.
    
    unfold Transaction.transaction_rep in *;
    logic_clean; simpl in *.
    repeat split_ors; logic_clean; try congruence.
    repeat rewrite map_length in *.
    destruct s0, s3; simpl in *.
    destruct s0, s3; simpl in *; eauto; try lia.
    intuition eauto.
  }
  {
    unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    repeat cleanup_pairs; simpl in *.
    
    unfold Transaction.transaction_rep in *;
    logic_clean; simpl in *.
    repeat split_ors; logic_clean; try congruence.
    eapply BlockAllocatorExistence.inode_allocations_are_same; eauto.
    destruct H11.
    unfold File.file_map_rep in *; logic_clean.
    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    repeat cleanup_pairs; simpl in *.
    
    unfold Transaction.transaction_rep in *;
    logic_clean; simpl in *.
    repeat split_ors; logic_clean; try congruence.
    repeat rewrite map_length in *.
    destruct s0, s3; simpl in *.
    destruct s0, s3; simpl in *; eauto; try lia.
  }
  {
    eapply FileInnerSpecs.inode_exists_then_file_exists in H23; eauto.
    eapply FileInnerSpecs.inode_missing_then_file_missing in H22; eauto.
    cleanup.
    edestruct H11.
    edestruct H10.
    intuition; eauto.
    exfalso; eapply H25; intuition eauto.
    congruence.
  }
  {
    eapply FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
    eapply FileInnerSpecs.inode_missing_then_file_missing in H24; eauto.
    cleanup.
    edestruct H11.
    edestruct H10.
    intuition; eauto.
    exfalso; eapply H26; intuition eauto.
    congruence.
  }
  simpl; eauto.
  Unshelve.
  all: exact id.
Qed.


Opaque File.DiskAllocator.alloc.

Theorem ATC_HSS_extend_inner:
  forall u u' ex inum v1 v2 s1 s2 x x0,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v1 inum)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v2 inum)) in
  
  @HC_refines _ _ _ Definitions.imp ATCLang _ Definitions.TDCoreRefinement s1 x ->
  @HC_refines _ _ _ Definitions.imp ATCLang _  Definitions.TDCoreRefinement s2 x0 ->
  AD_related_states u' ex x x0 ->
  have_same_structure p1 p2 u x x0 ->
  inum < Inode.InodeAllocatorParams.num_of_blocks ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold File.extend_inner; intros; cleanup.
    simpl; intuition eauto.

    eapply ATC_HSS_diskallocator_alloc; eauto.
    unfold refines_related in *; simpl in *; 
    unfold HC_refines in *; simpl in *.
    do 2 eexists; intuition eauto.
    cleanup.

    unfold refines_related in *; simpl in *; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H4;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H5; eauto.
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H4;
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H5; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

    eapply_fresh ATC_oracle_refines_impl_eq in H7.
    4: eauto.
    4: eauto.
    all: eauto.
    2: apply TD_oracle_refines_operation_eq.

    cleanup.
    eapply_fresh lift2_invert_exec in H9; cleanup.
    eapply_fresh lift2_invert_exec in H10; cleanup.
    apply HC_map_ext_eq in H13; subst.
    eapply_fresh File.DiskAllocator.alloc_finished_oracle_eq in H15; eauto.
    cleanup.
    unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
    eapply File.DiskAllocator.alloc_finished in H15; eauto.
    eapply File.DiskAllocator.alloc_finished in H17; eauto.
    cleanup.
    destruct H15, H17; cleanup; try congruence; try lia; try solve [intuition congruence].
    unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    refines_related in *; simpl in *.
    repeat cleanup_pairs.
    eapply disk_allocator_alloc_exact_txn in H4; eauto.
    eapply disk_allocator_alloc_exact_txn in H5; eauto.
    repeat split_ors; cleanup; try congruence; simpl in *.
    eapply ATC_HSS_inode_extend.
    7: eauto.
    7: eauto.
    7: eauto.
    all: try solve [simpl; eauto].
    {
      simpl; cleanup.
      setoid_rewrite H11;
      setoid_rewrite H1.
      simpl in *.
      destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
      File.DiskAllocatorParams.bitmap_addr); try intuition congruence.
      destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
      (File.DiskAllocatorParams.bitmap_addr + S x3));
      destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
      (File.DiskAllocatorParams.bitmap_addr + S x)); try intuition congruence.
      pose proof inodes_before_data.
      unfold File.DiskAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.bitmap_addr in *; lia.
      pose proof inodes_before_data.
      unfold File.DiskAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.bitmap_addr in *; lia.

      clear H15 H17.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *;
      destruct s6, s9; simpl in *.
      destruct s0, s3; simpl in *; try lia.
      intuition eauto.
    }
    {
      simpl; cleanup.
      setoid_rewrite H11;
      setoid_rewrite H1.
      simpl in *.
      destruct (addr_eq_dec (Inode.InodeAllocatorParams.bitmap_addr + S inum)
      File.DiskAllocatorParams.bitmap_addr); try intuition congruence.
      destruct (addr_eq_dec (Inode.InodeAllocatorParams.bitmap_addr + S inum)
      (File.DiskAllocatorParams.bitmap_addr + S x3));
      destruct (addr_eq_dec (Inode.InodeAllocatorParams.bitmap_addr + S inum)
      (File.DiskAllocatorParams.bitmap_addr + S x)); try intuition congruence.
      pose proof inodes_before_data.
      unfold File.DiskAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.num_of_blocks in *; lia.
      pose proof inodes_before_data.
      unfold File.DiskAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.num_of_blocks in *; lia.

      clear H15 H17.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *;
      destruct s6, s9; simpl in *.
      destruct s0, s3; simpl in *; try lia.
      intuition eauto.
    }
    {
      unfold Inode.inode_rep in *; simpl in *;
      logic_clean.
      eexists; intuition eauto.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
    }
    {
      unfold Inode.inode_rep in *; simpl in *;
      logic_clean.
      eexists; intuition eauto.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; repeat FileInnerSpecs.solve_bounds.
    }
    {
      simpl; cleanup.
      setoid_rewrite H11;
      setoid_rewrite H1.
      simpl in *.
      clear H15 H17.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *;
      destruct s6, s9; simpl in *.
      destruct s0, s3; simpl in *; try lia.
    }
    Unshelve.
    all: eauto; exact id.
Qed.

Opaque Transaction.commit.
Theorem ATC_HSS_create:
  forall u u' u'' ex s1 s2 x x0,
  let p1 := (File.create u'') in
  let p2 := (File.create u'') in
  @HC_refines _ _ _ Definitions.imp ATCLang _ Definitions.TDCoreRefinement s1 x ->
  @HC_refines _ _ _ Definitions.imp ATCLang _  Definitions.TDCoreRefinement s2 x0 ->
  AD_related_states u' ex x x0 ->
  have_same_structure p1 p2 u x x0 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold File.create; intros; cleanup.
    simpl; intuition eauto.
    unfold refines_related in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines in *.
    cleanup.

    eapply ATC_HSS_inodeallocator_alloc; eauto.
    unfold refines_related in *; simpl in *; 
    unfold HC_refines in *; simpl in *.
    do 2 eexists; intuition eauto.
    cleanup.

    unfold refines_related in *; simpl in *; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H3;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H4; eauto.
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H3;
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H4; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

    eapply_fresh ATC_oracle_refines_impl_eq in H6.
    4: eauto.
    4: eauto.
    all: eauto.
    2: apply TD_oracle_refines_operation_eq.

    cleanup.
    eapply_fresh H7 in H9; eauto.

    eapply_fresh lift2_invert_exec in H8; cleanup_no_match.
    eapply_fresh lift2_invert_exec in H9; cleanup_no_match.
    unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
    eapply_fresh Inode.alloc_finished in H14; eauto.
    eapply_fresh Inode.alloc_finished in H16; eauto.
    cleanup_no_match.
    destruct H26, H29; cleanup; simpl in *; try congruence; try lia;
    try solve [intuition congruence].
    simpl; intuition eauto; try congruence.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; logic_clean.
    eapply inode_allocator_alloc_exact_txn in H3, H4; eauto.
    repeat split_ors; try logic_clean; try congruence.
    eapply ATC_HSS_transaction_commit.
    {
      cleanup.
      setoid_rewrite H50;
      setoid_rewrite H53.
      simpl.
      clear H46 H47.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat cleanup_pairs.
      repeat rewrite map_length in *;
      destruct s1, s4; simpl in *; try lia.
      destruct (addr_dec Inode.InodeAllocatorParams.bitmap_addr
      (Inode.InodeAllocatorParams.bitmap_addr + S x11));
      destruct (addr_dec Inode.InodeAllocatorParams.bitmap_addr
      (Inode.InodeAllocatorParams.bitmap_addr + S x12)); try lia.
      simpl; eauto.
    }
    {
      cleanup.
      setoid_rewrite H50;
      setoid_rewrite H53.
      simpl.
      clear H46 H47.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat cleanup_pairs.
      repeat rewrite map_length in *;
      destruct s1, s4; simpl in *; try lia.
      pose proof inodes_fit_in_disk.
      unfold Inode.InodeAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.num_of_blocks in *;
      intuition; repeat constructor.
    }
    Unshelve.
    all: eauto; constructor.
Qed.


Theorem ATC_HSS_free_all_blocks:
  forall u l1 l2 s1 s2 td1 td2 dh1 dh2,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l1)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l2)) in
  Forall2 (fun a1 a2 => a1 < File.DiskAllocatorParams.num_of_blocks <->
  a2 < File.DiskAllocatorParams.num_of_blocks) l1 l2 ->
  Forall (fun a1 => test_bit a1 (value_to_bits (fst (snd (snd td1)) File.DiskAllocatorParams.bitmap_addr)) = true) l1 ->
  Forall (fun a1 => test_bit a1 (value_to_bits (fst (snd (snd td2)) File.DiskAllocatorParams.bitmap_addr)) = true) l2 ->
  NoDup l1 ->
  NoDup l2 ->
  (Transaction.get_first (fst (snd s1)) File.DiskAllocatorParams.bitmap_addr =
  None <->
  Transaction.get_first (fst (snd s2)) File.DiskAllocatorParams.bitmap_addr =
  None) ->
  @HC_refines _ _ _ Definitions.imp ATCLang AD Definitions.TDCoreRefinement s1 td1 ->
  @HC_refines _ _ _ Definitions.imp ATCLang AD  Definitions.TDCoreRefinement s2 td2 ->
  File.DiskAllocator.block_allocator_rep dh1 (fst (snd (snd td1))) ->
  File.DiskAllocator.block_allocator_rep dh2 (fst (snd (snd td2))) ->
  length (fst (snd s1)) = length (fst (snd s2)) ->
  have_same_structure p1 p2 u td1 td2 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
  induction l1; destruct l2; simpl in *; intros; eauto; 
  inversion H; inversion H0; 
  inversion H1; inversion H2; 
  inversion H3; cleanup; try lia.
  intuition eauto.
  eapply ATC_HSS_diskallocator_free; eauto.
  intuition eauto.
  intuition eauto.

  unfold HC_refines in *; cleanup; eauto.
  unfold HC_refines in *; cleanup; eauto.

  unfold refines_related in *; simpl in *; cleanup.
  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H13;
  eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H14; eauto.
  cleanup.
  eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H13;
  eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H14; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  cleanup.

  eapply_fresh ATC_oracle_refines_impl_eq in H34.
  4: eauto.
  4: eauto.
  all: eauto.
  2: apply TD_oracle_refines_operation_eq.
  cleanup.
  eapply_fresh H35 in H21; eauto.
  
  eapply_fresh lift2_invert_exec in H18; logic_clean.
  eapply_fresh lift2_invert_exec in H21; logic_clean.
  unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
  eapply File.DiskAllocator.free_finished in H30; eauto.
  eapply File.DiskAllocator.free_finished in H37; eauto.
  eapply diskallocator_free_exact_txn in H13, H14; eauto.
  cleanup_no_match; repeat split_ors; cleanup_no_match; simpl in *; try tauto.
  unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
  unfold TransactionToTransactionalDisk.Definitions.refines,
  refines_related in *; simpl in *.
  repeat cleanup_pairs.

  eapply IHl1; simpl; eauto.
  all: simpl; eauto.
  {
    eapply Forall_forall; intros.
    unfold File.DiskAllocator.block_allocator_rep in *; simpl in *; logic_clean.
    destruct  (Compare_dec.lt_dec x1 (length x5)).
    {
      eapply File.DiskAllocator.valid_bits_extract in H22; eauto.
      eapply File.DiskAllocator.valid_bits_extract with (n := x1)in H45; eauto.
      logic_clean.
      repeat split_ors; cleanup; eauto.
      eapply Forall_forall in H20; eauto; try congruence.
      rewrite delete_ne in H50; eauto; try congruence.
      all: lia.
    }
    {
      destruct (H47 x1).
      lia.
      eapply Forall_forall in H20; eauto; try congruence.
    }
  }
  {
    eapply Forall_forall; intros.
    unfold File.DiskAllocator.block_allocator_rep in *; simpl in *; logic_clean.
    destruct  (Compare_dec.lt_dec x1 (length x7)).
    {
      eapply File.DiskAllocator.valid_bits_extract in H30; eauto.
      eapply File.DiskAllocator.valid_bits_extract with (n := x1) in H41; eauto.
      logic_clean.
      repeat split_ors; cleanup; eauto.
      eapply Forall_forall in H24; eauto; try congruence.
      rewrite delete_ne in H50; eauto; try congruence.
      all: lia.
    }
    {
      destruct (H44 x1).
      lia.
      eapply Forall_forall in H24; eauto; try congruence.
    }
  }
  {
    destruct (addr_eq_dec File.DiskAllocatorParams.bitmap_addr
    File.DiskAllocatorParams.bitmap_addr); try lia; intuition congruence.
  }
  {
    destruct l1; simpl in *; eauto.
  }
  {
    destruct l2; simpl in *; eauto.
  }
  Unshelve.
  all: try exact id; constructor.
  Qed.



Theorem ATC_HSS_delete_inner:
  forall u u' ex inum s1 s2 x x0,
  let p1 := (@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)) in
  let p2 := (@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)) in
  
  @HC_refines _ _ _ Definitions.imp ATCLang _ Definitions.TDCoreRefinement s1 x ->
  @HC_refines _ _ _ Definitions.imp ATCLang _  Definitions.TDCoreRefinement s2 x0 ->
  AD_related_states u' ex x x0 ->
  have_same_structure p1 p2 u x x0 ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) p1) 
  (ATC_Refinement.(Simulation.Definitions.compile) p2) u s1 s2.
  Proof.
    unfold File.delete_inner; intros; cleanup.
    simpl; intuition eauto.
    unfold refines_related in *; simpl in *.
    unfold HC_refines in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines in *.
    cleanup.

    eapply ATC_HSS_inode_get_all_block_numbers; eauto.
    unfold refines_related in *; simpl in *; 
    unfold HC_refines in *; simpl in *.
    do 2 eexists; intuition eauto.
    
    unfold refines_related in *; simpl in *; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H3;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H4; eauto.
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H3;
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H4; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

    eapply_fresh ATC_oracle_refines_impl_eq in H6.
    4: eauto.
    4: eauto.
    all: eauto.
    2: apply TD_oracle_refines_operation_eq.

    cleanup.
    eapply_fresh H7 in H9; eauto.

    eapply_fresh lift2_invert_exec in H8; cleanup.
    eapply_fresh lift2_invert_exec in H9; cleanup.
    unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
    eapply Inode.get_all_block_numbers_finished_precise in H14; eauto.
    eapply Inode.get_all_block_numbers_finished_precise in H16; eauto.
    cleanup.
    destruct H14, H16; simpl in *; cleanup; try congruence; try lia.
    intuition eauto.

    eapply ATC_HSS_free_all_blocks.
    7: eauto.
    7: eauto.
    all: try solve [simpl; eauto].
    {
      eapply forall_forall2.
      eapply Forall_forall; intros.
      destruct x13.
      simpl; intuition.
      eapply in_combine_r in H14.
      eapply SameRetType.all_block_numbers_in_bound in H33; eauto.
      eapply Forall_forall in H33; eauto.
      apply in_combine_l in H14.
      eapply SameRetType.all_block_numbers_in_bound in H17; eauto.
      eapply Forall_forall in H17; eauto.

      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17;
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H33; eauto.
     logic_clean.
      edestruct H22; logic_clean.
      eapply_fresh H36 in H16; eauto; logic_clean.

      unfold File.file_map_rep in *; logic_clean.
      eapply H41 in H17;
      eapply H39 in H33;
      eauto.
      unfold File.file_rep in *; logic_clean.
      setoid_rewrite <- H43;
      setoid_rewrite <- H45; lia.
    }
    {
      eapply Forall_forall; intros.
      eapply in_seln_exists in H14; cleanup.
      unfold HC_refines in *; simpl in *; cleanup; eauto.
      repeat cleanup_pairs.
      rewrite <- H16.
      eapply BlockAllocatorExistence.used_blocks_are_allocated_2; eauto.
    }
    {
      eapply Forall_forall; intros.
      eapply in_seln_exists in H14; cleanup.
      unfold HC_refines in *; simpl in *; cleanup; eauto.
      repeat cleanup_pairs.
      rewrite <- H16.
      eapply BlockAllocatorExistence.used_blocks_are_allocated_2; eauto.
    }
    {
      unfold Inode.inode_rep, Inode.inode_map_rep,
      Inode.inode_map_valid  in *;
      logic_clean.
      eapply H36 in H17.
      unfold Inode.inode_valid in *; logic_clean; eauto.
    }
    {
      unfold Inode.inode_rep, Inode.inode_map_rep,
      Inode.inode_map_valid  in *;
      logic_clean.
      eapply H24 in H33.
      unfold Inode.inode_valid in *; logic_clean; eauto.
    }
    { 
      unfold HC_refines in *; simpl in *; cleanup; eauto.
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *; destruct s0, s5; simpl in *.
      destruct s0, s3; simpl in *; try lia.
      intuition eauto.
    }
    {
      repeat cleanup_pairs; eauto. 
    }
    {
      repeat cleanup_pairs; eauto. 
    }
    { 
      unfold HC_refines in *; simpl in *; cleanup; eauto.
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *; destruct s0, s5; simpl in *.
      destruct s0, s3; simpl in *; try lia.
    }
    {
      unfold refines_related in *; simpl in *; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H14;
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H16; eauto.
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H14;
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H16; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      cleanup.

      eapply_fresh ATC_oracle_refines_impl_eq in H19. 
      4: eauto.
      4: eauto.
      all: eauto.
      2: apply TD_oracle_refines_operation_eq.

      cleanup.
      eapply_fresh H20 in H36; eauto.

      eapply_fresh lift2_invert_exec in H36; cleanup_no_match.
      eapply_fresh lift2_invert_exec in H37; cleanup_no_match.
      repeat cleanup_pairs; simpl in *.
      eapply FileInnerSpecs.free_all_blocks_finished in H42; eauto.
      eapply FileInnerSpecs.free_all_blocks_finished in H44; eauto.
      cleanup_no_match.
      destruct H1, H13; simpl in *; cleanup; try congruence; try lia; simpl in *; eauto.
      Transparent Inode.free.
      unfold Inode.free, Inode.InodeAllocator.free  in *; simpl in *; 
      cleanup; try tauto.
      unfold Inode.free, Inode.InodeAllocator.free  in *; simpl in *; 
      cleanup; try tauto.
      Opaque Inode.free.

      unfold HC_refines  in *; simpl in *; cleanup.
      eapply ATC_HSS_inodeallocator_free. 
      4: eauto.
      4: eauto.
      all: eauto.
      intuition eauto.
      {
        eapply BlockAllocatorExistence.inode_allocations_are_same; eauto.
        repeat cleanup_pairs.
        unfold Inode.inode_rep in *; logic_clean.
        eexists; split.
        eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
        apply b.
        intros; FileInnerSpecs.solve_bounds.
        eauto.

        repeat cleanup_pairs.
        unfold Inode.inode_rep in *; logic_clean.
        eexists; split.
        eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
        apply b0.
        intros; FileInnerSpecs.solve_bounds.
        eauto.
        
        destruct H22.
        unfold File.file_map_rep in *; logic_clean.
        eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
        eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
        eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      }
      {
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      eapply free_all_blocks_exact_txn in H14, H16; eauto.
      repeat split_ors; cleanup; try congruence.
      simpl in *; cleanup.

      Lemma get_first_none_not_in_rev:
      forall (l : list (addr * value)) (a : addr),
      ~ In a (map fst l) -> Transaction.get_first l a = None.
      Proof.
        induction l; simpl in *; eauto.
        intuition; simpl in *.
        destruct (addr_eq_dec a a0); eauto; lia.
      Qed.
      repeat rewrite get_first_none_not_in_rev; eauto.
      intuition.
      rewrite map_app; intros Hin.
      apply in_app_iff in Hin; split_ors.
      rewrite H14 in H.
      apply repeat_spec in H.
      pose proof inodes_before_data.
      unfold Inode.InodeAllocatorParams.bitmap_addr,
      File.DiskAllocatorParams.bitmap_addr in *; lia.
      
      clear H13 H32 H41 H43.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *.
      destruct s0;  simpl in *.
      destruct s0; simpl in *; try lia.


      rewrite map_app; intros Hin.
      apply in_app_iff in Hin; split_ors.
      rewrite H48 in H.
      apply repeat_spec in H.
      pose proof inodes_before_data.
      unfold Inode.InodeAllocatorParams.bitmap_addr,
      File.DiskAllocatorParams.bitmap_addr in *; lia.
      
      clear H13 H32 H41 H43.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *.
      destruct s5;  simpl in *.
      destruct s3; simpl in *; try lia.
      }
      {
      unfold TransactionToTransactionalDisk.Definitions.refines, AD_related_states, FD_related_states,
      refines_related in *; simpl in *.
      repeat cleanup_pairs; simpl in *.
      
      eapply free_all_blocks_exact_txn in H14, H16; eauto.
      repeat split_ors; cleanup; try congruence.
      simpl in *; cleanup.
      repeat rewrite app_length.
      
      clear H13 H32 H41 H43.
      unfold Transaction.transaction_rep in *;
      logic_clean; simpl in *.
      repeat split_ors; logic_clean; try congruence.
      repeat rewrite map_length in *.
      destruct s0, s5;  simpl in *.
      destruct s0, s5; simpl in *; try lia.


      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17;
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H33; eauto.
       logic_clean.
        edestruct H22; logic_clean.
        eapply_fresh H67 in H64; eauto; logic_clean.

        unfold File.file_map_rep in *; logic_clean.
        eapply H72 in H17;
        eapply H70 in H33;
        eauto.
        unfold File.file_rep in *; logic_clean.
        rewrite H11, H47. 
        setoid_rewrite <- H74;
        setoid_rewrite <- H76; lia.
      }
    }
    Unshelve.
    all: eauto; constructor.
    Qed.

Theorem ATC_HSS_auth_then_exec:
  forall u u' T (p1 p2 : addr -> @prog _  TD (option T)) ex inum s1 s2 x x0,
  let px := (fun inum => @lift_L2 AuthenticationOperation _ TD _ (p1 inum)) in
  let py := (fun inum => @lift_L2 AuthenticationOperation _ TD _ (p2 inum)) in

  (forall s1 s2 x x0,
  @HC_refines _ _ _ Definitions.imp ATCLang _ Definitions.TDCoreRefinement s1 x ->
  @HC_refines _ _ _ Definitions.imp ATCLang _  Definitions.TDCoreRefinement s2 x0 ->
  AD_related_states u' ex x x0 ->
  have_same_structure (px inum) (py inum) u x x0 ->
  inum < Inode.InodeAllocatorParams.num_of_blocks ->
  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) (px inum)) 
  (ATC_Refinement.(Simulation.Definitions.compile) (py inum)) u s1 s2) ->

  
  (forall s1 s2 o s1' s2' r1 r2, 
  refines_related ATC_Refinement (AD_related_states u' ex) s1 s2 ->
  exec ATCLang u o s1 (ATC_Refinement.(Simulation.Definitions.compile) (px inum)) (Finished s1' (Some r1)) ->
  exec ATCLang u o s2 (ATC_Refinement.(Simulation.Definitions.compile) (py inum)) (Finished s2' (Some r2)) ->
  inum < Inode.InodeAllocatorParams.num_of_blocks ->
  length (dedup_last addr_dec (rev (map fst (fst (snd s1'))))) =
  length (dedup_last addr_dec (rev (map fst (fst (snd s2'))))) /\
  (Forall (fun a : nat => a < data_length) (map fst (fst (snd s1'))) <->
  Forall (fun a : nat => a < data_length) (map fst (fst (snd s2'))))) ->


  @HC_refines _ _ _ Definitions.imp ATCLang _ Definitions.TDCoreRefinement s1 x ->
  @HC_refines _ _ _ Definitions.imp ATCLang _  Definitions.TDCoreRefinement s2 x0 ->
  AD_related_states u' ex x x0 ->
  have_same_structure (File.auth_then_exec inum p1) (File.auth_then_exec inum p2) u x x0 ->

  ATC_have_same_structure (ATC_Refinement.(Simulation.Definitions.compile) (File.auth_then_exec inum p1)) 
  (ATC_Refinement.(Simulation.Definitions.compile) (File.auth_then_exec inum p2)) u s1 s2.
  Proof.
    unfold File.auth_then_exec; simpl; intros.
    intuition eauto.
    eapply ATC_HSS_inode_get_owner; eauto.
    unfold refines_related in *; simpl in *; cleanup.
    do 2 eexists; intuition eauto.

    unfold refines_related in *; simpl in *; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H7;
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H9; eauto.
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H7;
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    cleanup.

    eapply_fresh ATC_oracle_refines_impl_eq in H6.
    4: eauto.
    4: eauto.
    all: eauto.
    2: apply TD_oracle_refines_operation_eq.
    cleanup.

    eapply_fresh lift2_invert_exec in H10; cleanup.
    eapply_fresh lift2_invert_exec in H11; cleanup.
    eapply H8 in H10; eauto.

    unfold AD_related_states, FD_related_states,
    refines_related in *; simpl in *.
    unfold FileToFileDisk.Definitions.refines,
    File.files_rep, File.files_inner_rep in *;
    logic_clean.
    eapply Inode.get_owner_finished_precise in H16; eauto.
    eapply Inode.get_owner_finished_precise in H18; eauto.
    cleanup_no_match.
    destruct H16, H18; cleanup; simpl in *; 
    cleanup; try tauto; try congruence; try lia.
    {
      unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; logic_clean.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      refines_related in *; simpl in *.
      intuition eauto.
      assert (
        exists o s1' s2' , exec AD u o x4
      (Op (HorizontalComposition AuthenticationOperation
            (TransactionalDiskLayer.TDCore data_length))
         ( @P1 AuthenticationOperation _ _ (Auth (Inode.owner x11)) )) (Finished s1' r1) /\
         exec AD u o x3
      (Op (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore data_length))
              ( @P1 AuthenticationOperation _ _ (Auth (Inode.owner x12)) )) (Finished s2' r2)). {
          repeat invert_exec; try congruence;
          do 3 eexists; split; repeat econstructor; eauto.
         }
      logic_clean.
      eapply_fresh H33 in H38; eauto.
      repeat invert_exec_no_match;  cleanup;
      simpl in *; cleanup; eauto; try tauto; try congruence.
      assert (A: inum < Inode.InodeAllocatorParams.num_of_blocks). {
        destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); eauto.
          unfold Inode.inode_rep, Inode.inode_map_rep, 
          Inode.InodeAllocator.block_allocator_rep in *; logic_clean.
          edestruct (H44 inum); try lia.
          rewrite H26, H50 in H32.
          simpl in *;  congruence.
      }
      {
        simpl in *; intuition eauto.
        {
          eapply H. 
          4: eauto. 
          all: simpl in *; eauto.
          all: repeat cleanup_pairs; simpl in *; eauto.
          do 2 eexists; intuition eauto.
        }

        eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H17.
        eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H38; eauto.
        cleanup.
        eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H17; eauto.
        eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H38; eauto;
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
        cleanup.
        all: try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished].

        eapply_fresh ATC_oracle_refines_impl_eq in H39.
        6: eauto.
        6: eauto.
        all: eauto.
        4: apply TD_oracle_refines_operation_eq.
        cleanup.

        eapply_fresh lift2_invert_exec in e; cleanup.
        eapply_fresh lift2_invert_exec in H44; cleanup.
        eapply H40 in e; eauto.
        cleanup; simpl in *; cleanup; eauto; try tauto.
        intuition eauto.

        edestruct H0; eauto.
        eexists (_, _), (_, _); intuition eauto.
        do 2 eexists; simpl; intuition eauto.
        repeat cleanup_pairs; simpl; eauto.
        repeat cleanup_pairs; simpl; eauto.

        eapply ATC_HSS_transaction_commit; eauto.
        all: simpl; unfold HC_refines  in *; simpl in *;
        unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup; eauto.
      }
      {
        erewrite <- SameRetType.inode_owners_are_same_3 in H43.
        exfalso; eauto.
        6: eauto.
        6: eauto.
        3: eauto.
        all: eauto.
        eapply same_for_user_except_symmetry; eauto.
      }
      {
        erewrite <- SameRetType.inode_owners_are_same_3 in H47.
        exfalso; eauto.
        6: eauto.
        6: eauto.
        3: eauto.
        all: eauto.
      }
    }
    Unshelve.
    all: eauto; constructor.
  Qed.
