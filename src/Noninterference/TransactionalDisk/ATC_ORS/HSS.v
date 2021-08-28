Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs.

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

  Lemma block_allocations_are_same:
  forall (u : user) (fm1 fm2 : disk File) (s1 s2 : total_mem) 
  (bn1 bn2 : nat) (ex : option addr),
  File.files_inner_rep fm1 s1 ->
  File.files_inner_rep fm2 s2 ->
  same_for_user_except u ex fm1 fm2 ->
  bn1 < File.DiskAllocatorParams.num_of_blocks ->
  bn2 < File.DiskAllocatorParams.num_of_blocks ->
  nth_error (value_to_bits (s1 File.DiskAllocatorParams.bitmap_addr)) bn1 =
  nth_error (value_to_bits (s2 File.DiskAllocatorParams.bitmap_addr)) bn2.
  Proof. Admitted.
  
  Lemma block_allocator_empty:
  forall bn,
  nth_error (value_to_bits value0) bn = Some false \/
  nth_error (value_to_bits value0) bn = None.
  Proof. Admitted.


  Lemma have_same_structure_InodeAllocator_read:
  forall inum u u' s1 s2,
  (fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
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
erewrite InodeTS.inode_allocations_are_same; eauto.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) inum);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct_fresh (nth_error (value_to_bits value0) inum). 
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
Qed.

Lemma have_same_structure_DiskAllocator_read:
forall bn1 bn2 u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
(bn1 < File.DiskAllocatorParams.num_of_blocks <->
bn2 < File.DiskAllocatorParams.num_of_blocks) ->
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
erewrite block_allocations_are_same; eauto.
destruct_fresh (nth_error (value_to_bits (fst (snd (snd s2)) File.DiskAllocatorParams.bitmap_addr)) bn2);
setoid_rewrite D.
destruct b; simpl; intuition eauto.
simpl; intuition eauto.
destruct (block_allocator_empty bn1); 
destruct (block_allocator_empty bn2); 
cleanup; eauto;
simpl; intuition eauto.
Qed.

Lemma have_same_structure_get_inode:
forall inum u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
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



Lemma have_same_structure_get_owner:
forall inum u u' s1 s2,
AD_related_states u' None s1 s2 ->
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
forall inum off u u' s1 s2,
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 ->
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

destruct r1,r2; try solve [intuition congruence];
simpl; eauto.
shelve.
Unshelve.
all: eauto.
Admitted.