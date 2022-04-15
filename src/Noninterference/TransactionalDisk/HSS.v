Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs BlockAllocatorExistence.

Import FileDiskLayer.
    
    
Definition TD_have_same_structure {T T'} (p1: TransactionalDiskLayer.transactional_disk_prog T) (p2: TransactionalDiskLayer.transactional_disk_prog T') :=
  match p1, p2 with
  | TransactionalDiskLayer.Read _, TransactionalDiskLayer.Read _ => True
  | TransactionalDiskLayer.Write _ _, TransactionalDiskLayer.Write _ _ => True
  | TransactionalDiskLayer.Commit, TransactionalDiskLayer.Commit => True
  | TransactionalDiskLayer.Abort, TransactionalDiskLayer.Abort => True
  | TransactionalDiskLayer.Recover, TransactionalDiskLayer.Recover => True
  | TransactionalDiskLayer.Init _, TransactionalDiskLayer.Init _ => True
  | _, _ => False
  end.

Fixpoint have_same_structure {T T'} (p1: AD.(prog) T) (p2: AD.(prog) T') u s1 s2 :=
  match p1, p2 with
  | Op _ o1, Op _ o2 =>
    match o1, o2 with
    | P1 _, P1 _ => True (*It can only be auth*)
    | P2 t1, P2 t2 =>
      TD_have_same_structure t1 t2
    | _, _ => False
    end
  | Ret _, Ret _ => True
  | @Bind _ T1_1 T1_2 p1_1 p1_2, @Bind _ T2_1 T2_2 p2_1 p2_2 =>
    T1_1 = T2_1 /\
    T1_2 = T2_2 /\
    have_same_structure p1_1 p2_1 u s1 s2 /\
    (forall o s1' r1 s2' r2,
    exec AD u o s1 p1_1 (Finished s1' r1) ->
    exec AD u o s2 p2_1 (Finished s2' r2) ->
    have_same_structure (p1_2 r1) (p2_2 r2) u s1' s2')
  | _, _ => False
  end.

  Lemma have_same_structure_sym:
  forall u T (p1: AD.(prog) T) T' (p2: AD.(prog) T') s1 s2,
  have_same_structure p1 p2 u s1 s2 ->
  have_same_structure p2 p1 u s2 s1.
  Proof.
    induction p1; simpl; intros; 
    destruct p2; 
    simpl in *; cleanup; try tauto.
    destruct o1, o2; simpl in *; cleanup; try tauto.
    intuition eauto.
  Qed.



  
  Lemma block_allocator_empty:
  forall bn,
  nth_error (value_to_bits value0) bn = Some false \/
  nth_error (value_to_bits value0) bn = None.
  Proof.
  intros.
  rewrite value_to_bits_value0.
  unfold zero_bitlist.
  destruct_fresh (nth_error (repeat false block_size) bn); eauto.
  eapply_fresh nth_error_length in D.
  eapply_fresh nth_error_nth in D.
  rewrite <- nth_seln_eq in Hx0.
  rewrite repeat_seln' in Hx0; 
  subst; eauto.
  Qed.


  Lemma have_same_structure_InodeAllocator_read:
  forall inum u u' s1 s2 ex,
  (fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
  have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.read inum))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.read inum)) u s1 s2.
Proof.
unfold Inode.InodeAllocator.read; simpl; intros.
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); 
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
erewrite inode_allocations_are_same; eauto.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct_fresh (nth_error (value_to_bits value0) inum). 
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
Qed.

Lemma have_same_structure_InodeAllocator_write:
forall inum u u' s1 s2 v1 v2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.write inum v1))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.write inum v2)) u s1 s2.
Proof.
unfold Inode.InodeAllocator.write; simpl; intros.
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); 
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep, File.files_inner_rep  in *; cleanup.
erewrite inode_allocations_are_same_2 in *; eauto.
destruct_fresh (nth_error
(value_to_bits
   (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty inum); 
cleanup; eauto;
simpl; intuition eauto.
Qed.

Lemma have_same_structure_InodeAllocator_alloc:
forall u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->

(get_first_zero_index
   (firstn Inode.InodeAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s1))
         Inode.InodeAllocatorParams.bitmap_addr)))
 < Inode.InodeAllocatorParams.num_of_blocks <-> 
 get_first_zero_index
 (firstn Inode.InodeAllocatorParams.num_of_blocks
    (value_to_bits
       (fst (snd (snd s2))
       Inode.InodeAllocatorParams.bitmap_addr)))
< Inode.InodeAllocatorParams.num_of_blocks) ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.alloc v1))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.alloc v2)) u s1 s2.
Proof.
unfold Inode.InodeAllocator.alloc; simpl; intros.
simpl; intuition eauto.

repeat invert_exec; try lia.
cleanup.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
destruct (Compare_dec.lt_dec
(get_first_zero_index
   (firstn
   Inode.InodeAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s1))
         Inode.InodeAllocatorParams.bitmap_addr)))));
destruct (Compare_dec.lt_dec
(get_first_zero_index
   (firstn
   Inode.InodeAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s2))
         Inode.InodeAllocatorParams.bitmap_addr))))); try lia.


simpl; intuition eauto.
repeat invert_exec; try lia; cleanup.
simpl; intuition eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
destruct u0, u1; try solve [intuition congruence];
simpl; eauto.
destruct u0; try solve [intuition congruence];
simpl; eauto.
destruct u0; try solve [intuition congruence];
simpl; eauto.
{
  pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
  pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
  unfold Inode.InodeAllocatorParams.bitmap_addr,
  Inode.InodeAllocatorParams.num_of_blocks in *.
  assert (S (get_first_zero_index
  (firstn inode_count (value_to_bits (fst (snd (snd s2)) inode_blocks_start)))) <=
inode_count).
lia.

exfalso; eapply Lt.le_not_lt.
2: apply H1.
eapply PeanoNat.Nat.le_trans; eauto.
}
try solve [intuition congruence];
simpl; eauto.
{
  pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
  pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
  unfold Inode.InodeAllocatorParams.bitmap_addr,
  Inode.InodeAllocatorParams.num_of_blocks in *.
  assert (S (get_first_zero_index
  (firstn inode_count (value_to_bits (fst (snd (snd s1)) inode_blocks_start)))) <=
inode_count).
lia.

exfalso; eapply Lt.le_not_lt.
2: apply H1.
eapply PeanoNat.Nat.le_trans; eauto.
}
try solve [intuition congruence];
simpl; eauto.
try solve [intuition congruence];
simpl; eauto.
{
  pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
  pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
  unfold Inode.InodeAllocatorParams.bitmap_addr,
  Inode.InodeAllocatorParams.num_of_blocks in *; lia.
}
Qed.

Lemma addrs_match_exactly_sym:
  forall A AEQ V1 V2 (m1: @mem A AEQ V1) (m2: @mem A AEQ V2),
  addrs_match_exactly m1 m2 ->
  addrs_match_exactly m2 m1.
Proof.
  unfold addrs_match_exactly; intros; cleanup.
  specialize (H a).
  intuition eauto; try congruence.
Qed.

Lemma addrs_match_exactly_trans:
  forall A AEQ V1 V2 V3 (m1: @mem A AEQ V1) (m2: @mem A AEQ V2) 
  (m3: @mem A AEQ V3),
  addrs_match_exactly m1 m2 ->
  addrs_match_exactly m2 m3 ->
  addrs_match_exactly m1 m3.
Proof.
  unfold addrs_match_exactly; intros; cleanup.
  specialize (H a).
  specialize (H0 a).
  intuition eauto; try congruence.
Qed.

Lemma addrs_match_exactly_missing_1:
  forall A AEQ V1 V2 (fm: @mem A AEQ V1) (im: @mem A AEQ V2) inum,
  addrs_match_exactly fm im ->
  im inum = None ->
  fm inum = None.
Proof.
  intros; cleanup.
  destruct_fresh (fm inum); eauto.
  edestruct H; exfalso.
  apply H1; eauto; congruence.
Qed.

Lemma addrs_match_exactly_exists_1:
  forall A AEQ V1 V2 (fm: @mem A AEQ V1) (im: @mem A AEQ V2) inum inode,
  addrs_match_exactly fm im ->
  im inum = Some inode ->
  exists f, fm inum = Some f.
Proof.
  intros; cleanup.
  destruct_fresh (fm inum); eauto.
  edestruct H; exfalso.
  apply H2; eauto; congruence.
Qed.

Lemma inode_allocations_are_same_2:
forall im1 im2  s1 s2 inum,
Inode.inode_rep im1 s1 ->
Inode.inode_rep im2 s2 ->
addrs_match_exactly im1 im2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (s1 Inode.InodeAllocatorParams.bitmap_addr))
inum =
nth_error
  (value_to_bits (s2 Inode.InodeAllocatorParams.bitmap_addr)) inum.
Proof.
  unfold refines, File.files_rep, 
  File.files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (im2 inum).
  {
    eapply_fresh addrs_match_exactly_exists_1 in D; eauto.
    cleanup.
    unfold Inode.inode_rep, 
    Inode.inode_map_rep,
    Inode.InodeAllocator.block_allocator_rep in *.
    cleanup.
    eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H11.
    cleanup; split_ors; cleanup; try congruence.
    rewrite H9, H11 in H3; simpl in *; congruence.
    rewrite nth_seln_eq in H.
    repeat erewrite nth_error_nth'.

    eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H6.
    cleanup; split_ors; cleanup; try congruence.
    rewrite H4, H15 in D; simpl in *; congruence.
    rewrite nth_seln_eq in H14, H0.
    rewrite H0, H14; eauto.
    all: try rewrite value_to_bits_length;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
  {

    eapply_fresh addrs_match_exactly_missing_1 in D; eauto.
    cleanup.

    unfold Inode.inode_rep, 
    Inode.inode_map_rep,
    Inode.InodeAllocator.block_allocator_rep in *.
    cleanup.
    eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10.
    cleanup; split_ors; cleanup; try congruence.
    rewrite nth_seln_eq in H0.
    repeat erewrite nth_error_nth'.

    eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H5.
    cleanup; split_ors; cleanup; try congruence.
    rewrite nth_seln_eq in H13.
    rewrite H0, H13; eauto.
    rewrite H3, H14 in D; simpl in *; congruence.
    all: try rewrite value_to_bits_length;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
    rewrite H8, H10 in Hx; simpl in *; congruence.
    }
Qed.

Lemma have_same_structure_InodeAllocator_free:
forall inum u s1 s2,
(fun s1 s2  => exists im1 im2, 
Inode.inode_rep im1 (fst (snd (snd s1))) /\ 
Inode.inode_rep im2 (fst (snd (snd s2))) /\ 
addrs_match_exactly im1 im2) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.free inum))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.free inum)) u s1 s2.
Proof.
unfold Inode.InodeAllocator.free; simpl; intros.
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks);
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep, File.files_inner_rep in *; cleanup.
erewrite inode_allocations_are_same_2 in *; eauto.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty inum); 
cleanup; eauto;
simpl; intuition eauto.
Qed.



(************** DiskAllocator ******************)

Lemma have_same_structure_DiskAllocator_read:
forall bn1 bn2 u u' s1 s2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
(bn1 < File.DiskAllocatorParams.num_of_blocks <->
bn2 < File.DiskAllocatorParams.num_of_blocks) ->
(nth_error
(value_to_bits
   (fst (snd (snd s1))
      File.DiskAllocatorParams.bitmap_addr)) bn1 = nth_error
      (value_to_bits
         (fst (snd (snd s2))
            File.DiskAllocatorParams.bitmap_addr)) bn2) ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read bn1))
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read bn2)) u s1 s2.
Proof.
unfold File.DiskAllocator.read; simpl; intros.
destruct (Compare_dec.lt_dec bn1 File.DiskAllocatorParams.num_of_blocks); 
destruct (Compare_dec.lt_dec bn2 File.DiskAllocatorParams.num_of_blocks); 
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
setoid_rewrite H1.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) bn2);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty bn1); 
destruct (block_allocator_empty bn2); 
cleanup; eauto;
simpl; intuition eauto.
Qed.


Lemma have_same_structure_DiskAllocator_write:
forall bn1 bn2 u u' s1 s2 v1 v2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
(bn1 < File.DiskAllocatorParams.num_of_blocks <->
bn2 < File.DiskAllocatorParams.num_of_blocks) ->
(nth_error
(value_to_bits
   (fst (snd (snd s1))
      File.DiskAllocatorParams.bitmap_addr)) bn1 = nth_error
      (value_to_bits
         (fst (snd (snd s2))
            File.DiskAllocatorParams.bitmap_addr)) bn2) ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.write bn1 v1))
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.write bn2 v2)) u s1 s2.
Proof.
unfold File.DiskAllocator.write; simpl; intros.
destruct (Compare_dec.lt_dec bn1 File.DiskAllocatorParams.num_of_blocks); 
destruct (Compare_dec.lt_dec bn2 File.DiskAllocatorParams.num_of_blocks); 
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
setoid_rewrite H1.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) bn2);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty bn1); 
destruct (block_allocator_empty bn2); 
cleanup; eauto;
simpl; intuition eauto.
Qed.

Lemma have_same_structure_DiskAllocator_free:
forall bn1 bn2 u s1 s2,
(fun s1 s2  => (exists file_block_map : disk value,
File.DiskAllocator.block_allocator_rep
  file_block_map (fst (snd (snd s1)))) /\ 
(exists file_block_map : disk value,
  File.DiskAllocator.block_allocator_rep
    file_block_map (fst (snd (snd s2))))) s1 s2 ->
(bn1 < File.DiskAllocatorParams.num_of_blocks <->
bn2 < File.DiskAllocatorParams.num_of_blocks) ->
(nth_error
(value_to_bits
   (fst (snd (snd s1))
      File.DiskAllocatorParams.bitmap_addr)) bn1 = nth_error
      (value_to_bits
         (fst (snd (snd s2))
            File.DiskAllocatorParams.bitmap_addr)) bn2) ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.free bn1))
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.free bn2)) u s1 s2.
Proof.
unfold File.DiskAllocator.free; simpl; intros.
destruct (Compare_dec.lt_dec bn1 File.DiskAllocatorParams.num_of_blocks); 
destruct (Compare_dec.lt_dec bn2 File.DiskAllocatorParams.num_of_blocks); 
simpl; intuition eauto.

repeat invert_exec; try lia.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
setoid_rewrite H1.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) bn2);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty bn1); 
destruct (block_allocator_empty bn2); 
cleanup; eauto;
simpl; intuition eauto.
Qed.


Lemma have_same_structure_DiskAllocator_alloc:
forall u u' s1 s2 v1 v2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->

(get_first_zero_index
   (firstn File.DiskAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s1))
            File.DiskAllocatorParams.bitmap_addr)))
 < File.DiskAllocatorParams.num_of_blocks <-> 
 get_first_zero_index
 (firstn File.DiskAllocatorParams.num_of_blocks
    (value_to_bits
       (fst (snd (snd s2))
          File.DiskAllocatorParams.bitmap_addr)))
< File.DiskAllocatorParams.num_of_blocks) ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.alloc v1))
(@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.alloc v2)) u s1 s2.
Proof.
unfold File.DiskAllocator.alloc; simpl; intros.
simpl; intuition eauto.

repeat invert_exec; try lia.
cleanup.
unfold AD_related_states, refines_related in *; cleanup; simpl in *.
unfold refines, File.files_rep in *; cleanup.
destruct (Compare_dec.lt_dec
(get_first_zero_index
   (firstn
      File.DiskAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s1))
            File.DiskAllocatorParams.bitmap_addr)))));
destruct (Compare_dec.lt_dec
(get_first_zero_index
   (firstn
      File.DiskAllocatorParams.num_of_blocks
      (value_to_bits
         (fst (snd (snd s2))
            File.DiskAllocatorParams.bitmap_addr))))); try lia.


simpl; intuition eauto.
repeat invert_exec; try lia; cleanup.
simpl; intuition eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
destruct u0, u1; try solve [intuition congruence];
simpl; eauto.
destruct u0; try solve [intuition congruence];
simpl; eauto.
destruct u0; try solve [intuition congruence];
simpl; eauto.
{
  pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
  pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
  unfold File.DiskAllocatorParams.bitmap_addr,
  File.DiskAllocatorParams.num_of_blocks in *.
  assert (S (get_first_zero_index
  (firstn file_blocks_count (value_to_bits (fst (snd (snd s2)) file_blocks_start)))) <=
file_blocks_count).
lia.

exfalso; eapply Lt.le_not_lt.
2: apply H1.
eapply PeanoNat.Nat.le_trans; eauto.
eapply PeanoNat.Nat.add_le_mono; eauto.
}
try solve [intuition congruence];
simpl; eauto.
{
  pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
  pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
  unfold File.DiskAllocatorParams.bitmap_addr,
  File.DiskAllocatorParams.num_of_blocks in *.
  assert (S (get_first_zero_index
  (firstn file_blocks_count (value_to_bits (fst (snd (snd s1)) file_blocks_start)))) <=
file_blocks_count).
lia.

exfalso; eapply Lt.le_not_lt.
2: apply H1.
eapply PeanoNat.Nat.le_trans; eauto.
eapply PeanoNat.Nat.add_le_mono; eauto.
}
try solve [intuition congruence];
simpl; eauto.
try solve [intuition congruence];
simpl; eauto.
{
  pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
  pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
  unfold File.DiskAllocatorParams.bitmap_addr,
  File.DiskAllocatorParams.num_of_blocks in *; lia.
}
Qed.

(************* Inode **********************)
Lemma have_same_structure_get_inode:
forall inum u u' s1 s2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_inode inum)) u s1 s2.
Proof.
unfold Inode.get_inode; simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_InodeAllocator_read; eauto.
eapply lift2_invert_exec in H0; cleanup.
eapply lift2_invert_exec in H1; cleanup.
eapply map_ext_eq in H0.
2: intros; cleanup; intuition congruence.
subst.
eapply Inode.InodeAllocator.read_finished_oracle_eq in H3; eauto.
cleanup.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
Unshelve.
all: eauto.
Qed.

Lemma have_same_structure_set_inode:
forall inum in1 in2 u u' s1 s2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.set_inode inum in1))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.set_inode inum in2)) u s1 s2.
Proof.
unfold Inode.set_inode; simpl; intros.
simpl; intuition eauto.
eapply have_same_structure_InodeAllocator_write; eauto.
Qed.

Lemma have_same_structure_get_owner:
forall inum u u' s1 s2 ex,
AD_related_states u' ex s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum)) u s1 s2.
Proof.
Transparent Inode.get_owner.
Opaque Inode.get_inode.
unfold Inode.get_owner; simpl; intros.
simpl; intuition eauto.

unfold AD_related_states, refines_related in *; cleanup;
simpl in *.
unfold refines, File.files_rep in *; cleanup.
eapply have_same_structure_get_inode; eauto.
do 2 eexists; intuition eauto.
setoid_rewrite H4; eauto.
setoid_rewrite H2; eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
Unshelve.
all: eauto.
Qed.


Lemma have_same_structure_get_block_number:
forall inum off u u' s1 s2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)) u s1 s2.
Proof.
Transparent Inode.get_block_number.
Opaque Inode.get_inode.
unfold Inode.get_block_number; simpl; intros.
simpl; intuition eauto.

unfold AD_related_states, refines_related in *; cleanup;
simpl in *.
unfold refines, File.files_rep in *; cleanup.
eapply have_same_structure_get_inode; eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
Qed.

Lemma have_same_structure_get_all_block_numbers:
forall inum u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_all_block_numbers inum ))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.get_all_block_numbers inum )) u s1 s2.
Proof.
Transparent Inode.get_all_block_numbers.
Opaque Inode.get_inode.
unfold Inode.get_all_block_numbers; simpl; intros.
simpl; intuition eauto.

unfold AD_related_states, refines_related in *; cleanup;
simpl in *.
unfold refines, File.files_rep in *; cleanup.
eapply have_same_structure_get_inode; eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
Unshelve.
all: eauto.
Qed.


Lemma have_same_structure_Inode_extend:
forall inum v1 v2 u u' s1 s2 ex,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.extend inum v1))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.extend inum v2)) u s1 s2.
Proof.
Transparent Inode.extend.
Opaque Inode.get_inode.
unfold Inode.extend; simpl; intros.
simpl; intuition eauto.

unfold AD_related_states, refines_related in *; cleanup;
simpl in *.
unfold refines, File.files_rep in *; cleanup.
eapply have_same_structure_get_inode; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
eapply_fresh Inode.get_inode_finished_oracle_eq in H5; eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
eapply have_same_structure_set_inode.
unfold File.files_inner_rep in *; cleanup.
eapply Inode.get_inode_finished in H5; eauto.
eapply Inode.get_inode_finished in H3; eauto.
cleanup.
clear H H5.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.
Unshelve.
all: eauto.
Qed.

Lemma have_same_structure_Inode_change_owner:
forall inum v1 v2 u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' (Some inum) s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (Inode.change_owner inum v1))
(@lift_L2 AuthenticationOperation _ TD _ (Inode.change_owner inum v2)) u s1 s2.
Proof.
Transparent Inode.change_owner.
Opaque Inode.get_inode.
unfold Inode.change_owner; simpl; intros.
simpl; intuition eauto.

unfold AD_related_states, refines_related in *; cleanup;
simpl in *.
unfold refines, File.files_rep in *; cleanup.
eapply have_same_structure_get_inode; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
eapply_fresh Inode.get_inode_finished_oracle_eq in H5; eauto.
destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
eapply have_same_structure_set_inode.
unfold File.files_inner_rep in *; cleanup.
eapply Inode.get_inode_finished in H5; eauto.
eapply Inode.get_inode_finished in H3; eauto.
cleanup.
clear H H5.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.
Unshelve.
all: eauto.
Qed.


Lemma have_same_structure_read_inner:
forall inum off u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)) u s1 s2.
Proof.
Transparent File.read_inner.
Opaque Inode.get_block_number.
unfold File.read_inner; simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_get_block_number; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply map_ext_eq in H1; subst.
2: intros; cleanup; intuition congruence.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh Inode.get_block_number_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
intuition.
eapply Inode.get_block_number_finished in H5; eauto.
eapply Inode.get_block_number_finished in H3; eauto.
repeat split_ors; cleanup.

eapply have_same_structure_DiskAllocator_read; eauto.
clear H3 H5.
do 2 eexists; intuition eauto.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

{
  repeat split_ors; cleanup.
  shelve.
}
{
  repeat split_ors; cleanup.
  shelve.
}

destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
shelve.
Unshelve.
all: eauto.
{
  intuition eauto.
  eapply SameRetType.all_block_numbers_in_bound in H21.
  3: eauto.
  all: eauto.
  eapply Forall_forall in H21; eauto.
  apply in_seln; eauto.

  eapply SameRetType.all_block_numbers_in_bound in H23.
  2: eauto.
  all: eauto.
  eapply Forall_forall in H23; eauto.
  apply in_seln; eauto.

  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; FileInnerSpecs.solve_bounds.
}
2: {
  intros.
  match goal with
   | [H: _ ?inum = Some _,
      H0: _ ?inum = Some _ |- _] =>
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
   end.
   unfold FD_related_states,
   same_for_user_except in *; cleanup.
   match goal with
   | [H: ?fm1 ?inum = Some _,
      H0: ?fm2 ?inum = Some _,
      H1: forall (_: addr) (_ _: File), 
       ?fm1 _ = Some _ ->
       ?fm2 _ = Some _ ->
       _ = _ /\ _ = _ |- _] =>
       eapply_fresh H1 in H; eauto; cleanup
  end.
   unfold File.file_map_rep in *; cleanup.
   match goal with
   | [H: ?x1 ?inum = Some _,
      H0: ?x2 ?inum = Some _,
      H1: forall (_: Inode.Inum) _ _, 
      ?x1 _ = Some _ ->
      _ _ = Some _ -> _,
      H2: forall (_: Inode.Inum) _ _, 
      ?x2 _ = Some _ ->
      _ _ = Some _ -> _ |- _] =>
      eapply H1 in H; eauto; cleanup;
      eapply H2 in H0; eauto; cleanup
   end.
   unfold File.file_rep in *; cleanup; eauto.
}
{
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
- repeat erewrite used_blocks_are_allocated_2; eauto.
all: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; FileInnerSpecs.solve_bounds.
- unfold Inode.inode_rep, Inode.inode_map_rep,
Inode.inode_map_valid,
Inode.inode_valid,
Inode.InodeAllocator.block_allocator_rep in *; cleanup.

rewrite H34, H39 in *; 
simpl in *; try lia; try congruence.
}
Qed.


Lemma have_same_structure_write_inner:
forall inum off u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v2 inum)) u s1 s2.
Proof.
Transparent File.write_inner.
Opaque Inode.get_block_number.
unfold File.read_inner; simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_get_block_number; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply map_ext_eq in H1; subst.
2: intros; cleanup; intuition congruence.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh Inode.get_block_number_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
intuition.
eapply Inode.get_block_number_finished in H5; eauto.
eapply Inode.get_block_number_finished in H3; eauto.
repeat split_ors; cleanup.

eapply have_same_structure_DiskAllocator_write; eauto.
clear H3 H5.
do 2 eexists; intuition eauto.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

{
  repeat split_ors; cleanup.
  shelve.
}
{
  repeat split_ors; cleanup.
  shelve.
}
{
  intros.
  match goal with
   | [H: _ ?inum = Some _,
      H0: _ ?inum = Some _ |- _] =>
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
   end.
   unfold FD_related_states,
   same_for_user_except in *; cleanup.
   match goal with
   | [H: ?fm1 ?inum = Some _,
      H0: ?fm2 ?inum = Some _,
      H1: forall (_: addr) (_ _: File), 
       ?fm1 _ = Some _ ->
       ?fm2 _ = Some _ ->
       _ = _ /\ _ = _ |- _] =>
       eapply_fresh H1 in H; eauto; cleanup
  end.
   unfold File.file_map_rep in *; cleanup.
   match goal with
   | [H: ?x1 ?inum = Some _,
      H0: ?x2 ?inum = Some _,
      H1: forall (_: Inode.Inum) _ _, 
      ?x1 _ = Some _ ->
      _ _ = Some _ -> _,
      H2: forall (_: Inode.Inum) _ _, 
      ?x2 _ = Some _ ->
      _ _ = Some _ -> _ |- _] =>
      eapply H1 in H; eauto; cleanup;
      eapply H2 in H0; eauto; cleanup
   end.
   unfold File.file_rep in *; cleanup; eauto.
}

Unshelve.
all: eauto.
{
  intuition eauto.
  eapply SameRetType.all_block_numbers_in_bound in H21.
  3: eauto.
  all: eauto.
  eapply Forall_forall in H21; eauto.
  apply in_seln; eauto.

  eapply SameRetType.all_block_numbers_in_bound in H23.
  2: eauto.
  all: eauto.
  eapply Forall_forall in H23; eauto.
  apply in_seln; eauto.

  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; FileInnerSpecs.solve_bounds.
}
{
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
- repeat erewrite used_blocks_are_allocated_2; eauto.
all: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; FileInnerSpecs.solve_bounds.
- unfold Inode.inode_rep, Inode.inode_map_rep,
Inode.inode_map_valid,
Inode.inode_valid,
Inode.InodeAllocator.block_allocator_rep in *; cleanup.

rewrite H34, H39 in *; 
simpl in *; try lia; try congruence.
}
Qed.


Lemma have_same_structure_write_inner_input:
forall inum off u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' (Some inum) s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v2 inum)) u s1 s2.
Proof.
Transparent File.write_inner.
Opaque Inode.get_block_number.
unfold File.write_inner; simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_get_block_number; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply map_ext_eq in H1; subst.
2: intros; cleanup; intuition congruence.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh Inode.get_block_number_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
intuition.
eapply Inode.get_block_number_finished in H5; eauto.
eapply Inode.get_block_number_finished in H3; eauto.
repeat split_ors; cleanup.

eapply have_same_structure_DiskAllocator_write; eauto.
clear H3 H5.
do 2 eexists; intuition eauto.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.

{
  repeat split_ors; cleanup.
  shelve.
}
{
  repeat split_ors; cleanup.
  shelve.
}
{
  intros.
  match goal with
   | [H: _ ?inum = Some _,
      H0: _ ?inum = Some _ |- _] =>
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
   eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
   end.
   unfold FD_related_states,
   same_for_user_except in *; cleanup.
   match goal with
   | [H: ?fm1 ?inum = Some _,
      H0: ?fm2 ?inum = Some _,
      H1: forall (_: addr) (_ _: File), 
       ?fm1 _ = Some _ ->
       ?fm2 _ = Some _ ->
       _ = _ /\ _ = _ |- _] =>
       eapply_fresh H1 in H; eauto; cleanup
  end.
   unfold File.file_map_rep in *; cleanup.
   match goal with
   | [H: ?x1 ?inum = Some _,
      H0: ?x2 ?inum = Some _,
      H1: forall (_: Inode.Inum) _ _, 
      ?x1 _ = Some _ ->
      _ _ = Some _ -> _,
      H2: forall (_: Inode.Inum) _ _, 
      ?x2 _ = Some _ ->
      _ _ = Some _ -> _ |- _] =>
      eapply H1 in H; eauto; cleanup;
      eapply H2 in H0; eauto; cleanup
   end.
   unfold File.file_rep in *; cleanup; eauto.
}

Unshelve.
all: eauto.
{
  intuition eauto.
  eapply SameRetType.all_block_numbers_in_bound in H21.
  3: eauto.
  all: eauto.
  eapply Forall_forall in H21; eauto.
  apply in_seln; eauto.

  eapply SameRetType.all_block_numbers_in_bound in H23.
  2: eauto.
  all: eauto.
  eapply Forall_forall in H23; eauto.
  apply in_seln; eauto.

  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; FileInnerSpecs.solve_bounds.
}
{
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
- repeat erewrite used_blocks_are_allocated_2; eauto.
all: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
intros; FileInnerSpecs.solve_bounds.
- unfold Inode.inode_rep, Inode.inode_map_rep,
Inode.inode_map_valid,
Inode.inode_valid,
Inode.InodeAllocator.block_allocator_rep in *; cleanup.

rewrite H34, H39 in *; 
simpl in *; try lia; try congruence.
}
Qed.

Lemma have_same_structure_extend_inner:
forall inum u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v2 inum)) u s1 s2.
Proof.
Transparent File.extend_inner.
Opaque Inode.get_block_number Inode.extend File.DiskAllocator.alloc.
unfold File.extend_inner. simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_DiskAllocator_alloc; eauto.
cleanup; eapply free_block_exists_iff; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
unfold File.files_inner_rep, Inode.inode_rep in *; cleanup.
eapply_fresh File.DiskAllocator.alloc_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
eapply have_same_structure_Inode_extend; eauto.

eapply File.DiskAllocator.alloc_finished in H3; eauto.
eapply File.DiskAllocator.alloc_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.

unfold File.files_inner_rep, Inode.inode_rep in *; cleanup;
do 2 eexists; intuition eauto.
eexists; intuition eauto.
eexists; split.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
apply H.
eauto; intros; FileInnerSpecs.solve_bounds.
eauto.
eexists; intuition eauto.
{
  unfold File.file_map_rep in *; cleanup; intuition eauto.
  eapply_fresh H10 in H13; eauto.
  unfold File.file_rep in *; cleanup.
  intuition eauto.
  erewrite Mem.upd_ne; eauto.

  intuition; cleanup.
  unfold Inode.inode_map_rep,
  Inode.inode_map_valid,
  Inode.inode_valid in *; cleanup.
  eapply H26 in H27; cleanup.
}

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.
eexists; intuition eauto.
{
  unfold File.file_map_rep in *; cleanup; intuition eauto.
  eapply_fresh H5 in H13; eauto.
  unfold File.file_rep in *; cleanup.
  intuition eauto.
  erewrite Mem.upd_ne; eauto.

  intuition; cleanup.
  unfold Inode.inode_map_rep,
  Inode.inode_map_valid,
  Inode.inode_valid in *; cleanup.
  eapply H26 in H27; cleanup.
}

Unshelve.
all: eauto.
Qed.

Lemma have_same_structure_extend_inner_input:
forall inum u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' (Some inum) s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v2 inum)) u s1 s2.
Proof.
Transparent File.extend_inner.
Opaque Inode.get_block_number Inode.extend File.DiskAllocator.alloc.
unfold File.extend_inner. simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_DiskAllocator_alloc; eauto.
cleanup; eapply free_block_exists_iff; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
unfold File.files_inner_rep, Inode.inode_rep in *; cleanup.
eapply_fresh File.DiskAllocator.alloc_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
eapply have_same_structure_Inode_extend; eauto.

eapply File.DiskAllocator.alloc_finished in H3; eauto.
eapply File.DiskAllocator.alloc_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.

unfold File.files_inner_rep, Inode.inode_rep in *; cleanup;
do 2 eexists; intuition eauto.
eexists; intuition eauto.
eexists; split.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
apply H.
eauto; intros; FileInnerSpecs.solve_bounds.
eauto.
eexists; intuition eauto.
{
  unfold File.file_map_rep in *; cleanup; intuition eauto.
  eapply_fresh H10 in H13; eauto.
  unfold File.file_rep in *; cleanup.
  intuition eauto.
  erewrite Mem.upd_ne; eauto.

  intuition; cleanup.
  unfold Inode.inode_map_rep,
  Inode.inode_map_valid,
  Inode.inode_valid in *; cleanup.
  eapply H26 in H27; cleanup.
}

unfold File.files_inner_rep; 
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; 
eauto; intros; FileInnerSpecs.solve_bounds.
eexists; intuition eauto.
{
  unfold File.file_map_rep in *; cleanup; intuition eauto.
  eapply_fresh H5 in H13; eauto.
  unfold File.file_rep in *; cleanup.
  intuition eauto.
  erewrite Mem.upd_ne; eauto.

  intuition; cleanup.
  unfold Inode.inode_map_rep,
  Inode.inode_map_valid,
  Inode.inode_valid in *; cleanup.
  eapply H26 in H27; cleanup.
}

Unshelve.
all: eauto.
Qed.

Lemma have_same_structure_change_owner_inner:
forall inum u u' s1 s2 v1 v2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' (Some inum) s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v2 inum)) u s1 s2.
Proof.
Transparent File.change_owner_inner.
Opaque Inode.change_owner.
unfold File.change_owner_inner. simpl; intros.
eapply have_same_structure_Inode_change_owner; eauto.
Qed.


Lemma have_same_structure_free_all_blocks:
forall l1 l2 u s1 s2,
length l1 = length l2 ->
Forall (fun bn1 => bn1 < File.DiskAllocatorParams.num_of_blocks) l1 ->
Forall (fun bn1 => bn1 < File.DiskAllocatorParams.num_of_blocks) l2 ->
Forall (fun a => nth_error (value_to_bits (fst (snd (snd s1)) File.DiskAllocatorParams.bitmap_addr)) a = Some true) l1 ->
Forall (fun a => nth_error (value_to_bits (fst (snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) a = Some true) l2 ->
NoDup l1 ->
NoDup l2 ->
(fun s1 s2  => 
(exists file_block_map : disk value,
        File.DiskAllocator.block_allocator_rep
          file_block_map (fst (snd (snd s1)))) /\ 
(exists file_block_map : disk value,
          File.DiskAllocator.block_allocator_rep
            file_block_map (fst (snd (snd s2))))) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l1))
(@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l2)) u s1 s2.
Proof.
  induction l1; destruct l2; simpl in *; intros; 
  eauto; try lia; inversion H0; inversion H1; inversion H2; 
  inversion H3; inversion H4.
  intuition eauto; cleanup.
  eapply have_same_structure_DiskAllocator_free; eauto.
  intuition eauto.
  setoid_rewrite H17.
  setoid_rewrite H21.
  eauto.

  eapply lift2_invert_exec in H6.
eapply lift2_invert_exec in H29; cleanup.
apply HC_map_ext_eq in H7; subst.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh File.DiskAllocator.free_finished_oracle_eq in H15; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
destruct u0, u1; try solve [intuition congruence];
simpl; eauto.

eapply File.DiskAllocator.free_finished in H11; eauto.
eapply File.DiskAllocator.free_finished in H15; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.
simpl in *; eapply IHl1; eauto.
simpl.

{
  eapply Forall_forall; intros.
  eapply Forall_forall in H18; eauto.
  eapply Forall_forall in H10; eauto.

  eapply_fresh nth_error_nth in H18.
  rewrite <- nth_seln_eq in Hx.

  unfold File.DiskAllocator.block_allocator_rep in H27; cleanup.
  eapply File.DiskAllocator.valid_bits_extract in v; eauto.
  cleanup; split_ors; cleanup; eauto.
  rewrite Hx in H11; congruence.

  unfold File.DiskAllocator.block_allocator_rep in H23; cleanup.
  eapply File.DiskAllocator.valid_bits_extract in H20.
  cleanup; split_ors; cleanup; eauto.

  rewrite delete_ne in H20.
  rewrite H12 in H20; congruence.
  intuition subst; eauto.

  erewrite nth_error_nth'.
  rewrite <- nth_seln_eq.
  rewrite H16; eauto.
  {
    rewrite value_to_bits_length.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
  rewrite H23; eauto.
  {
    rewrite value_to_bits_length.
    rewrite H23; eauto.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
  rewrite e0; eauto.
  {
    rewrite value_to_bits_length.
    rewrite e0; eauto.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
}
{
  eapply Forall_forall; intros.
  eapply Forall_forall in H22; eauto.
  eapply Forall_forall in H14; eauto.

  eapply_fresh nth_error_nth in H22.
  rewrite <- nth_seln_eq in Hx.

  unfold File.DiskAllocator.block_allocator_rep in H28; cleanup.
  eapply File.DiskAllocator.valid_bits_extract in v; eauto.
  cleanup; split_ors; cleanup; eauto.
  rewrite Hx in H11; congruence.

  unfold File.DiskAllocator.block_allocator_rep in H24; cleanup.
  eapply File.DiskAllocator.valid_bits_extract in H20.
  cleanup; split_ors; cleanup; eauto.

  rewrite delete_ne in H20.
  rewrite H12 in H20; congruence.
  inversion H5; intuition subst; eauto.

  erewrite nth_error_nth'.
  rewrite <- nth_seln_eq.
  simpl; rewrite H16; eauto.
  {
    rewrite value_to_bits_length.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
  rewrite H24; eauto.
  {
    rewrite value_to_bits_length.
    rewrite H24; eauto.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
  rewrite e0; eauto.
  {
    rewrite value_to_bits_length.
    rewrite e0; eauto.
    pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
    unfold File.DiskAllocatorParams.num_of_blocks in *; lia.
  }
}
inversion H5; eauto.
Unshelve.
all: eauto.
Qed.



Lemma have_same_structure_delete_inner:
forall inum u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)) u s1 s2.
Proof.
Transparent File.delete_inner.
Opaque Inode.get_all_block_numbers.
unfold File.delete_inner. simpl; intros.
simpl; intuition eauto.

eapply have_same_structure_get_all_block_numbers; eauto.
eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.

intuition eauto.
eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.
eapply have_same_structure_free_all_blocks.

{
  edestruct FileInnerSpecs.inode_exists_then_file_exists; eauto.
  edestruct FileInnerSpecs.inode_exists_then_file_exists.
  2: apply H20.
  eauto.

  unfold File.file_map_rep in *; cleanup.
  eapply_fresh H5 in H2; eauto.
  eapply_fresh H9 in H3; eauto.
  unfold File.file_rep in *; cleanup.
  unfold FD_related_states, same_for_user_except in *; cleanup.
  eapply H25 in H2; eauto; cleanup; eauto.
}
eapply SameRetType.all_block_numbers_in_bound; eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; FileInnerSpecs.solve_bounds.

eapply SameRetType.all_block_numbers_in_bound.
4: eauto.
all: eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; FileInnerSpecs.solve_bounds.

{
  eapply Forall_forall; intros.
  eapply in_seln_exists in H2; cleanup.
  simpl; rewrite <- H3.
  eapply used_blocks_are_allocated_2; eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; FileInnerSpecs.solve_bounds.
}

{
  eapply Forall_forall; intros.
  eapply in_seln_exists in H2; cleanup.
  simpl; rewrite <- H3.
  eapply used_blocks_are_allocated_2; eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; FileInnerSpecs.solve_bounds.
}

{
  unfold Inode.inode_rep, Inode.inode_map_rep,
  Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
  eapply H24 in H20; cleanup; eauto.
}
{
  unfold Inode.inode_rep, Inode.inode_map_rep,
  Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
  eapply H19 in H21; cleanup; eauto.
}

simpl; split; eexists; eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.


eapply lift2_invert_exec in H11.
eapply lift2_invert_exec in H13; cleanup.
apply HC_map_ext_eq in H13; subst.
eapply_fresh SameRetType.free_all_blocks_finished_oracle_eq in H17; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
destruct u0, u1; try solve [intuition congruence];
simpl; eauto.

eapply FileInnerSpecs.free_all_blocks_finished in H15; eauto.
eapply FileInnerSpecs.free_all_blocks_finished in H17; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.
eapply have_same_structure_InodeAllocator_free.

2: {
  eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.
}
2: {
  eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.
}
eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
repeat cleanup_pairs.
unfold File.files_inner_rep, Inode.inode_rep in *; cleanup;
do 2 eexists; intuition eauto.
eexists; intuition eauto.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
simpl; intros; FileInnerSpecs.solve_bounds]; eauto.
eexists; split.
eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
simpl; intros; FileInnerSpecs.solve_bounds]; eauto.
eauto.
unfold File.file_map_rep, FD_related_states, same_for_user_except in *; cleanup.
eapply addrs_match_exactly_trans; eauto.
eapply addrs_match_exactly_trans; eauto.
eapply addrs_match_exactly_sym; eauto.

eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
eapply SameRetType.all_block_numbers_in_bound.
4: eauto.
all: eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.

eapply Inode.get_all_block_numbers_finished in H3; eauto.
eapply Inode.get_all_block_numbers_finished in H5; eauto.
repeat (repeat split_ors; cleanup).
eapply SameRetType.all_block_numbers_in_bound.
4: eauto.
all: eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
intros; FileInnerSpecs.solve_bounds]; eauto.

Unshelve.
all: eauto.
Qed.





Lemma get_owner_related_ret_eq:
forall u u' ex s1 s2 o s1' s2' r1 r2 inum, 
AD_related_states u' ex s1 s2 ->
exec TD u o (snd s1) (Inode.get_owner inum) (Finished s1' r1) ->
exec TD u o (snd s2) (Inode.get_owner inum) (Finished s2' r2) ->
r1 = r2.
Proof.
  unfold AD_related_states, refines_related, FD_related_states; simpl;
  intros; cleanup.
  unfold refines, File.files_rep, File.files_inner_rep in *.
  cleanup.
  rewrite <- H8, <- H4 in *.
  eapply Inode.get_owner_finished in H0; eauto.
  eapply Inode.get_owner_finished in H1; eauto.
  cleanup; repeat split_ors; cleanup; try lia; eauto.
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H20; eauto.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto.
    cleanup.
    unfold File.file_map_rep in *; cleanup.
    eapply_fresh H22 in H1; eauto.
    eapply_fresh H23 in H0; eauto.
    destruct H3; cleanup.
    eapply H25 in H0; eauto; cleanup.
    unfold File.file_rep in *; cleanup; eauto.
  }
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H20; eauto.
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in H21; eauto.
    cleanup.
    destruct H3; cleanup.
    edestruct H1. 
    exfalso; eapply H24; eauto. congruence.
  }
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto.
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in H20; eauto.
    cleanup.
    destruct H3; cleanup.
    edestruct H1. 
    exfalso; eapply H23; eauto. congruence.
  }
Qed.


Lemma have_same_structure_auth_then_exec:
forall T (p1 p2: _ -> TD.(prog) (option T)) inum u u' s1 s2 ex,
(forall s1 s2, 
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' ex s1a s2a) s1 s2 ->

have_same_structure
(@lift_L2 AuthenticationOperation _ TD _ (p1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (p2 inum)) u s1 s2) ->

(forall (fm1 fm2 : disk File)
(o : oracle' (TransactionalDiskLayer.TDCore data_length))
(o' o1
 o2 : list
        (Layer.token' (TransactionalDiskLayer.TDCore data_length)))
(s1 : LayerImplementation.state' (TransactionalDiskLayer.TDCore data_length))
(s2 : txn_state * (total_mem * total_mem))
(s1'
 s2' : LayerImplementation.state' (TransactionalDiskLayer.TDCore data_length))
(r1 r2 : option T) (inum : nat),
exec TD u o s1 (p1 inum) (Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
File.files_inner_rep fm1 (fst (snd s1)) ->
File.files_inner_rep fm2 (fst (snd s2)) ->
same_for_user_except u' ex fm1 fm2 ->
exec TD u o' s2 (p2 inum) (Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None)) ->

AD_related_states u' ex s1 s2 ->
have_same_structure (File.auth_then_exec inum p1) (File.auth_then_exec inum p2) u s1 s2.
Proof.
  Opaque Inode.get_owner.
  unfold File.auth_then_exec.
  intros; simpl.
  intuition eauto.
  eapply have_same_structure_get_owner; eauto.

  eapply lift2_invert_exec in H2.
eapply lift2_invert_exec in H3; cleanup.
apply HC_map_ext_eq in H3; subst.
eapply_fresh get_owner_related_ret_eq in H5; eauto.

unfold AD_related_states, refines_related in *; 
simpl in *; cleanup.

unfold refines, File.files_rep in *; cleanup.
rewrite <- H8, <- H10 in *; clear H8 H10.
unfold File.files_inner_rep in *; cleanup.
eapply Inode.get_owner_finished in H7; eauto.
eapply Inode.get_owner_finished in H5; eauto.
repeat split_ors; cleanup.

clear H5 H7. destruct r2; simpl; intuition eauto.
repeat invert_exec; intuition.
simpl; intuition eauto.
apply H; eauto.
do 2 eexists; intuition eauto.

unfold File.files_inner_rep; eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; SameRetType.solve_bounds.

unfold File.files_inner_rep; eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; SameRetType.solve_bounds.

eapply lift2_invert_exec in H5.
eapply lift2_invert_exec in H7; cleanup.
apply HC_map_ext_eq in H7; subst.
unfold FD_related_states  in *.

eapply H0 in H23. 
2: eapply H26. 
all: eauto.
cleanup. 
destruct r1, r2; simpl; intuition congruence.

unfold File.files_inner_rep; eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; SameRetType.solve_bounds.

unfold File.files_inner_rep; eexists; intuition eauto.
eexists; intuition eauto.
eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
intros; SameRetType.solve_bounds.

simpl; intuition eauto.
Unshelve.
eauto.
Qed.


(************* HSS for syscalls **************)
Lemma have_same_structure_read:
forall inum off u u' s1 s2,
AD_related_states u' None s1 s2 ->
have_same_structure (File.read inum off) (File.read inum off) u s1 s2.
Proof.
  unfold File.read; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_read_inner; eauto.
 intros; eapply SameRetType.read_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_write:
forall inum off u u' s1 s2 v1 v2,
AD_related_states u' None s1 s2 ->
have_same_structure (File.write inum off v1) (File.write inum off v2) u s1 s2.
Proof.
  unfold File.write; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_write_inner; eauto.
 intros; eapply SameRetType.write_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_write_input:
forall inum off u u' s1 s2 v1 v2,
AD_related_states u' (Some inum) s1 s2 ->
have_same_structure (File.write inum off v1) (File.write inum off v2) u s1 s2.
Proof.
  unfold File.write; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_write_inner_input; eauto.
 intros; eapply SameRetType.write_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_extend:
forall inum u u' s1 s2 v1 v2,
AD_related_states u' None s1 s2 ->
have_same_structure (File.extend inum v1) (File.extend inum v2) u s1 s2.
Proof.
  unfold File.extend; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_extend_inner; eauto.
 intros; eapply SameRetType.extend_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_extend_input:
forall inum u u' s1 s2 v1 v2,
AD_related_states u' (Some inum) s1 s2 ->
have_same_structure (File.extend inum v1) (File.extend inum v2) u s1 s2.
Proof.
  unfold File.extend; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_extend_inner_input; eauto.
 intros; eapply SameRetType.extend_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_change_owner:
forall inum u u' s1 s2 v1 v2,
AD_related_states u' (Some inum) s1 s2 ->
have_same_structure (File.change_owner inum v1) (File.change_owner inum v2) u s1 s2.
Proof.
  unfold File.change_owner; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_change_owner_inner; eauto.
 intros; eapply SameRetType.change_owner_inner_finished_oracle_eq; eauto. 
Qed.


Lemma have_same_structure_delete:
forall inum u u' s1 s2,
AD_related_states u' None s1 s2 ->
have_same_structure (File.delete inum) (File.delete inum) u s1 s2.
Proof.
  unfold File.delete; intros.
  eapply have_same_structure_auth_then_exec; eauto.
  intros; eapply have_same_structure_delete_inner; eauto.
 intros; eapply SameRetType.delete_inner_finished_oracle_eq; eauto. 
Qed.

Lemma have_same_structure_create:
forall u u' s1 s2 v,
AD_related_states u' None s1 s2 ->
have_same_structure (File.create v) (File.create v) u s1 s2.
Proof.
  unfold File.create; intros.
  simpl; intuition eauto.

  unfold AD_related_states, refines_related in *; cleanup; simpl in *.
  unfold refines, File.files_rep in *; simpl in *; logic_clean.
  clear H2 H4.
  eapply have_same_structure_InodeAllocator_alloc; eauto.
  eapply free_block_exists_iff_inode; eauto.
  
  eapply lift2_invert_exec in H0.
eapply lift2_invert_exec in H1; cleanup.
apply HC_map_ext_eq in H1; subst.
unfold File.files_inner_rep in *; cleanup.
eapply_fresh Inode.alloc_finished_oracle_eq in H5; eauto.
cleanup; destruct r1,r2; try solve [intuition congruence];
simpl; eauto.

Unshelve.
all: eauto.
Qed.