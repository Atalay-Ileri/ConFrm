Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType SSECommon.


Lemma inode_allocations_are_same:
forall u fm1 fm2 s1 s2 inum ex,
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
same_for_user_except u ex fm1 fm2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (s1 Inode.InodeAllocatorParams.bitmap_addr))
inum =
nth_error
  (value_to_bits (s2 Inode.InodeAllocatorParams.bitmap_addr)) inum.
Proof.
  unfold refines, files_rep, 
  files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    destruct_fresh (fm1 inum).
    {
      destruct_fresh (x0 inum).
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H12.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H10, H12 in D; simpl in *; congruence.
      rewrite nth_seln_eq in H.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H15, H21 in D1; simpl in *; congruence.
      rewrite nth_seln_eq in H20, H0.
      rewrite H0, H20; eauto.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H8; exfalso.
      apply H13; eauto; congruence.
    }
    {
      edestruct H1; exfalso.
      apply H11; eauto; congruence.
    }
  }
  {
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in D; eauto.
    cleanup.
    destruct_fresh (fm1 inum).
    {
      edestruct H1; exfalso.
      apply H9; eauto; congruence.
    }
    destruct_fresh (x0 inum).
    {
      unfold file_map_rep in *; cleanup.
      edestruct H8; exfalso.
      apply H12; eauto; congruence.
    }
    {
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H11.
      cleanup; split_ors; cleanup; try congruence.
      rewrite nth_seln_eq in H0.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H16.
      cleanup; split_ors; cleanup; try congruence.
      rewrite nth_seln_eq in H19.
      rewrite H0, H19; eauto.
      rewrite H14, H20 in D1; simpl in *; congruence.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
      rewrite H9, H11 in D; simpl in *; congruence.
    }
  }
Qed.


Lemma SSE_get_inode:
forall o fm1 fm2 u' ex s1 s2 inum ret1 u,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.get_inode inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.get_inode inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.get_inode.  
unfold Inode.get_inode, Inode.InodeAllocator.read; intros.
cleanup.
{
  repeat invert_step.
  {
    eexists; split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    simpl; intuition congruence.
  }
  {
    eexists; split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    simpl; intuition congruence.
  }
  {
    apply nth_error_None in D0; rewrite value_to_bits_length in D0;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *; lia.
  }
  {
    repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D1.
    repeat exec_step.
    simpl; intuition congruence.

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D1.
    repeat exec_step.
    simpl; intuition congruence.
  } 
}
{
  repeat invert_step.
  {
    eexists; repeat exec_step.
  }
  {
    repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split. repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    exists (Crashed s2); split.
    repeat exec_step.
    simpl; intuition congruence.
  }
}
Unshelve.
all: exact (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length).
Qed.
Opaque Inode.get_inode.




Lemma SSE_set_inode:
forall o fm1 fm2 u' ex s1 s2 inum inode1 inode2 ret1 u,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.set_inode inum inode1) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.set_inode inum inode2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.set_inode.  
unfold Inode.set_inode, Inode.InodeAllocator.write; intros.
cleanup.
{
  repeat invert_step.
  {
    destruct s2; simpl in *.
    exists (Finished (upd t (Inode.InodeAllocatorParams.bitmap_addr + S inum) (Inode.encode_inode inode2), t0) (Some tt)); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    repeat econstructor; eauto.
    simpl; intuition congruence.
  }
  {
    destruct s2; simpl in *.
    exists (Finished (t, t0) None); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    econstructor; eauto.
    eapply TransactionalDiskLayer.ExecWriteInboundFull; eauto.
    simpl; intuition congruence.
  }
  {
    destruct s2; simpl in *.
    exists (Finished (t, t0) None); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    repeat econstructor; eauto.
    simpl; intuition congruence.
  }
  {
    apply nth_error_None in D0; rewrite value_to_bits_length in D0;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *; lia.
  }
  {
    repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat eapply bind_reorder_l.
    repeat econstructor.    
    simpl; intuition congruence.

    exists (Crashed s2); split.
    repeat exec_step.
    erewrite <- inode_allocations_are_same.
    4: eauto.
    all: eauto.
    setoid_rewrite D0.
    repeat exec_step.
    repeat eapply bind_reorder_l.
    repeat econstructor; eauto.
    simpl; intuition congruence.
  } 
}
{
  repeat invert_step.
  {
    eexists; repeat exec_step.
  }
  {
    eexists; repeat exec_step.
  }
}
Qed.
Opaque Inode.set_inode.


Lemma SSE_get_owner:
forall o fm1 fm2 s1 s2 inum ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
refines s1 fm1 ->
refines s2 fm2 ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o (snd s1) (Inode.get_owner inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o (snd s2) (Inode.get_owner inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.get_owner.  
unfold Inode.get_owner; intros.
invert_step.
{
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  {
    eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
  }
  unfold refines, files_rep in *; cleanup; setoid_rewrite H0; eauto.
  unfold refines, files_rep in *; cleanup; setoid_rewrite H1; eauto.
}
{
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  {
    eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
  }
  unfold refines, files_rep in *; cleanup; setoid_rewrite H0; eauto.
  unfold refines, files_rep in *; cleanup; setoid_rewrite H1; eauto.
}
{
  repeat invert_step_crash.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x1; simpl in *; try solve [intuition congruence]. 
  {
    exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash; eauto.
    simpl; intuition eauto.
  }
  unfold refines, files_rep in *; cleanup; setoid_rewrite H0; eauto.
  unfold refines, files_rep in *; cleanup; setoid_rewrite H1; eauto.
  {
    eapply_fresh SSE_get_inode in H2; eauto.
    cleanup;
    destruct x3; simpl in *; try solve [intuition congruence]. 
    {
        repeat invert_step.
        eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
        cleanup; destruct o; try solve [intuition congruence].
        eexists; split.
        repeat exec_step.
        simpl; intuition congruence.
    }
    {
        repeat invert_step.
        eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
        cleanup; destruct o; try solve [intuition congruence].
        eexists; split.
        repeat exec_step.
        simpl; intuition congruence.
    }
  unfold refines, files_rep in *; cleanup; setoid_rewrite H0; eauto.
  unfold refines, files_rep in *; cleanup; setoid_rewrite H1; eauto.
  } 
}
Unshelve.
all: eauto.
Qed.
Opaque Inode.get_owner.


Lemma SSE_get_all_block_numbers:
forall o fm1 fm2 s1 s2 inum ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.get_all_block_numbers inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.get_all_block_numbers inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.get_all_block_numbers.  
unfold Inode.get_all_block_numbers; intros.
invert_step.
{
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  {
    eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
  }
}
{
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  {
    eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
  }
}
{
  repeat invert_step_crash.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x1; simpl in *; try solve [intuition congruence]. 
  {
    exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash; eauto.
    simpl; intuition eauto.
  }
  {
    eapply_fresh SSE_get_inode in H2; eauto.
    cleanup;
    destruct x3; simpl in *; try solve [intuition congruence]. 
    {
        repeat invert_step.
        eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
        cleanup; destruct o; try solve [intuition congruence].
        eexists; split.
        repeat exec_step.
        simpl; intuition congruence.
    }
    {
        repeat invert_step.
        eapply Inode.get_inode_finished_oracle_eq in H2; eauto.
        cleanup; destruct o; try solve [intuition congruence].
        eexists; split.
        repeat exec_step.
        simpl; intuition congruence.
    }
  } 
}
Unshelve.
all: eauto.
Qed.
Opaque Inode.get_all_block_numbers.
  

Set Nested Proofs Allowed.
Lemma free_block_exists:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
  (firstn DiskAllocatorParams.num_of_blocks
      (value_to_bits
        (s1 DiskAllocatorParams.bitmap_addr))) <
DiskAllocatorParams.num_of_blocks ->
(get_first_zero_index
      (firstn DiskAllocatorParams.num_of_blocks
        (value_to_bits
            (s2 DiskAllocatorParams.bitmap_addr)))) <
  DiskAllocatorParams.num_of_blocks.
Proof. Admitted.

Lemma free_block_exists_iff:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
  (firstn DiskAllocatorParams.num_of_blocks
      (value_to_bits
        (s1 DiskAllocatorParams.bitmap_addr))) <
DiskAllocatorParams.num_of_blocks <->
(get_first_zero_index
      (firstn DiskAllocatorParams.num_of_blocks
        (value_to_bits
            (s2 DiskAllocatorParams.bitmap_addr)))) <
  DiskAllocatorParams.num_of_blocks.
Proof. Admitted.



Lemma free_block_exists_inode:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
  (firstn Inode.InodeAllocatorParams.num_of_blocks
      (value_to_bits
        (s1 Inode.InodeAllocatorParams.bitmap_addr))) <
        Inode.InodeAllocatorParams.num_of_blocks ->
(get_first_zero_index
      (firstn Inode.InodeAllocatorParams.num_of_blocks
        (value_to_bits
            (s2 Inode.InodeAllocatorParams.bitmap_addr)))) <
            Inode.InodeAllocatorParams.num_of_blocks.
Proof. Admitted.

Lemma free_block_exists_iff_inode:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
  (firstn Inode.InodeAllocatorParams.num_of_blocks
      (value_to_bits
        (s1 Inode.InodeAllocatorParams.bitmap_addr))) <
        Inode.InodeAllocatorParams.num_of_blocks <->
(get_first_zero_index
      (firstn Inode.InodeAllocatorParams.num_of_blocks
        (value_to_bits
            (s2 Inode.InodeAllocatorParams.bitmap_addr)))) <
            Inode.InodeAllocatorParams.num_of_blocks.
Proof. Admitted.


Lemma SSE_alloc:
forall o fm1 fm2 s1 s2 v v' ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (DiskAllocator.alloc v) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (DiskAllocator.alloc v') ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent DiskAllocator.alloc.  
unfold DiskAllocator.alloc; intros.
invert_step.
cleanup.
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat econstructor.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    assert (~ get_first_zero_index
    (firstn DiskAllocatorParams.num_of_blocks
       (value_to_bits
          ((fst s2)
             DiskAllocatorParams.bitmap_addr))) <
 DiskAllocatorParams.num_of_blocks). {
    intros Hnot.
    eapply free_block_exists_iff in Hnot; eauto.
 }
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat econstructor.
    simpl; intuition congruence.
}
{
  repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].
    clear D.
    eapply free_block_exists in l; eauto.

    exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    clear D.
    eapply free_block_exists in l; eauto.
    exists (Crashed (upd ((fst s2))
    (DiskAllocatorParams.bitmap_addr +
     S
       (get_first_zero_index
          (firstn DiskAllocatorParams.num_of_blocks
             (value_to_bits
                ((fst s2) DiskAllocatorParams.bitmap_addr)))))
    v', (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.


    clear D.
    eapply free_block_exists in l; eauto.
    exists (Crashed (upd
    (upd (fst s2)
       (DiskAllocatorParams.bitmap_addr +
        S
          (get_first_zero_index
             (firstn DiskAllocatorParams.num_of_blocks
                (value_to_bits
                   ((fst s2)
                      DiskAllocatorParams.bitmap_addr)))))
       v') DiskAllocatorParams.bitmap_addr
    (bits_to_value
       (updn
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))
          (get_first_zero_index
             (firstn DiskAllocatorParams.num_of_blocks
                (value_to_bits
                   ((fst s2)
                      DiskAllocatorParams.bitmap_addr))))
          true)), (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.



    clear D.
    eapply free_block_exists in l; eauto.
    exists (Crashed (upd (fst s2)
    (DiskAllocatorParams.bitmap_addr +
     S
       (get_first_zero_index
          (firstn DiskAllocatorParams.num_of_blocks
             (value_to_bits
                ((fst s2)
                   DiskAllocatorParams.bitmap_addr)))))
    v', (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.


    clear D.
    eapply free_block_exists in l; eauto.
    exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof DiskAllocatorParams.blocks_fit_in_disk. 
    unfold DiskAllocatorParams.num_of_blocks, 
    DiskAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat econstructor.
    simpl; intuition congruence.


    clear D.
    assert (~ get_first_zero_index
    (firstn DiskAllocatorParams.num_of_blocks
       (value_to_bits
          ((fst s2)
             DiskAllocatorParams.bitmap_addr))) <
 DiskAllocatorParams.num_of_blocks). {
    intros Hnot.
    eapply free_block_exists_iff in Hnot; eauto.
 }
 exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn DiskAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
                DiskAllocatorParams.bitmap_addr))))
    DiskAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
}
Qed.
Opaque DiskAllocator.alloc.


Lemma SSE_alloc_inode:
forall o fm1 fm2 s1 s2 v v' ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.alloc v) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.alloc v') ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.alloc Inode.InodeAllocator.alloc.  
unfold Inode.alloc, Inode.InodeAllocator.alloc; intros.
invert_step.
cleanup.
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists_inode in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists_inode in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    eapply free_block_exists_inode in l; eauto.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat econstructor.
    simpl; intuition congruence.
}
{
  repeat invert_step.
    eexists; split.
    repeat exec_step.
    clear D.
    assert (~ get_first_zero_index
    (firstn Inode.InodeAllocatorParams.num_of_blocks
       (value_to_bits
          ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))) <
             Inode.InodeAllocatorParams.num_of_blocks). {
    intros Hnot.
    eapply free_block_exists_iff_inode in Hnot; eauto.
 }
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat econstructor.
    simpl; intuition congruence.
}
{
  repeat invert_step_crash; try solve [solve_illegal_state].
    exists (Crashed s2); split.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].
    clear D.
    eapply free_block_exists_inode in l; eauto.

    exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    clear D.
    eapply free_block_exists_inode in l; eauto.
    exists (Crashed (upd ((fst s2))
    (Inode.InodeAllocatorParams.bitmap_addr +
     S
       (get_first_zero_index
          (firstn Inode.InodeAllocatorParams.num_of_blocks
             (value_to_bits
                ((fst s2) Inode.InodeAllocatorParams.bitmap_addr)))))
                (Inode.encode_inode
                {|
                  Inode.owner := v';
                  Inode.block_numbers := []
                |}), (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.


    clear D.
    eapply free_block_exists_inode in l; eauto.
    exists (Crashed (upd
    (upd (fst s2)
       (Inode.InodeAllocatorParams.bitmap_addr +
        S
          (get_first_zero_index
             (firstn Inode.InodeAllocatorParams.num_of_blocks
                (value_to_bits
                   ((fst s2)
                   Inode.InodeAllocatorParams.bitmap_addr)))))
                   (Inode.encode_inode
                   {|
                     Inode.owner := v';
                     Inode.block_numbers := []
                   |})) Inode.InodeAllocatorParams.bitmap_addr
    (bits_to_value
       (updn
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))
          (get_first_zero_index
             (firstn Inode.InodeAllocatorParams.num_of_blocks
                (value_to_bits
                   ((fst s2)
                   Inode.InodeAllocatorParams.bitmap_addr))))
          true)), (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.



    clear D.
    eapply free_block_exists_inode in l; eauto.
    exists (Crashed (upd (fst s2)
    (Inode.InodeAllocatorParams.bitmap_addr +
     S
       (get_first_zero_index
          (firstn Inode.InodeAllocatorParams.num_of_blocks
             (value_to_bits
                ((fst s2)
                Inode.InodeAllocatorParams.bitmap_addr)))))
                   (Inode.encode_inode
                   {|
                     Inode.owner := v';
                     Inode.block_numbers := []
                   |}), (snd s2))); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    simpl; intuition congruence.


    clear D.
    eapply free_block_exists_inode in l; eauto.
    exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk. 
    unfold Inode.InodeAllocatorParams.num_of_blocks, 
    Inode.InodeAllocatorParams.bitmap_addr in *.
    eapply lt_le_lt; eauto.
    simpl; repeat exec_step.
    repeat econstructor.
    simpl; intuition congruence.


    clear D.
    assert (~ get_first_zero_index
    (firstn Inode.InodeAllocatorParams.num_of_blocks
       (value_to_bits
          ((fst s2)
          Inode.InodeAllocatorParams.bitmap_addr))) <
          Inode.InodeAllocatorParams.num_of_blocks). {
    intros Hnot.
    eapply free_block_exists_iff_inode in Hnot; eauto.
 }
 exists (Crashed s2); split.
    repeat exec_step.
    destruct_fresh (Compare_dec.lt_dec
    (get_first_zero_index
       (firstn Inode.InodeAllocatorParams.num_of_blocks
          (value_to_bits
             ((fst s2)
             Inode.InodeAllocatorParams.bitmap_addr))))
             Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat exec_step.
    rewrite cons_app;
    econstructor.
    repeat econstructor.
}
Qed.
Opaque Inode.alloc Inode.InodeAllocator.alloc.

  
Ltac solve_bounds:=
match goal with
|[H: forall _: nat , _ -> ?x _ = _ |- ?x _ = _ ] =>
    pose proof FSParameters.inodes_before_data;
    rewrite H;
    unfold DiskAllocatorParams.bitmap_addr,
    DiskAllocatorParams.num_of_blocks,
    Inode.InodeAllocatorParams.bitmap_addr,
    Inode.InodeAllocatorParams.num_of_blocks in *;
    try lia; eauto
end. 

Lemma SSE_extend:
forall o fm1 fm2 s1 s2 v v' ret1 u u' ex inum,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.extend inum v) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.extend inum v') ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.extend.  
unfold Inode.extend; intros.
invert_step.
cleanup.
{
  repeat invert_step.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x2; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  unfold refines, files_rep, files_inner_rep in *; cleanup.
  eapply Inode.get_inode_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh Inode.get_inode_finished in H4; eauto.
  cleanup; split_ors; cleanup.

  eapply_fresh SSE_set_inode in H3; eauto.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence]. 
  eapply Inode.set_inode_finished_oracle_eq in H3; eauto; cleanup.

  eexists; split.
  repeat exec_step.
  simpl; eapply H2.
  simpl; intuition congruence.

  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
}
{
  repeat invert_step.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].

  repeat invert_step.
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
}
{

  repeat invert_step_crash; try solve [solve_illegal_state].
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x1; simpl in *; try solve [intuition congruence]. 

  
  exists (Crashed s0); split.
    repeat exec_step.
    repeat eapply bind_reorder_l.    
    rewrite cons_app;
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].
    eapply_fresh SSE_get_inode in H2; eauto.
    cleanup.
    destruct x2; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    unfold refines, files_rep, files_inner_rep in *; cleanup.
    eapply Inode.get_inode_finished in H2; eauto.
    cleanup; split_ors; cleanup.
    eapply_fresh Inode.get_inode_finished in H4; eauto.
    cleanup; split_ors; cleanup.
  
    eapply_fresh SSE_set_inode in H3; eauto.
    cleanup.
    destruct x8; simpl in *; try solve [intuition congruence].   


    exists (Crashed s3); split.
    repeat exec_step.
    simpl; eauto.
    simpl; intuition congruence.
    {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }

  eapply_fresh SSE_get_inode in H2; eauto.
    cleanup.
    destruct x0; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].

    exists (Crashed s0); split.
    repeat exec_step.
    simpl; intuition congruence.

 }
Unshelve.
all: eauto.
Qed.
Opaque Inode.extend.

Lemma SSE_free:
forall o s1 s2 v v' ret1 u,
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (DiskAllocator.free v) ret1 ->
(v < DiskAllocatorParams.num_of_blocks <-> v' < DiskAllocatorParams.num_of_blocks) ->
nth_error
      (value_to_bits
         (fst s1 DiskAllocatorParams.bitmap_addr)) v =
nth_error
      (value_to_bits
         (fst s2 DiskAllocatorParams.bitmap_addr)) v' ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (DiskAllocator.free v') ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent DiskAllocator.free.  
unfold DiskAllocator.free; intros.
invert_step.
destruct (Compare_dec.lt_dec v'
DiskAllocatorParams.num_of_blocks); try lia.
cleanup.
{
  repeat invert_step.
  exists (Finished (upd (fst s2) DiskAllocatorParams.bitmap_addr (bits_to_value
  (updn (value_to_bits ((fst s2) DiskAllocatorParams.bitmap_addr)) v' false)), snd s2) (Some tt)); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  {
    repeat invert_step_crash.
    exists (Crashed s2); repeat exec_step.

    cleanup; repeat invert_step_crash.
    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.

    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.

    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.
  }
}
{
  repeat invert_exec.
  exists (Finished s2 None); split.
  destruct (Compare_dec.lt_dec v'
  DiskAllocatorParams.num_of_blocks); try lia.
    repeat econstructor.
    simpl; intuition.
  
    exists (Crashed s2); split.
    destruct (Compare_dec.lt_dec v'
    DiskAllocatorParams.num_of_blocks); try lia.
      repeat econstructor.
      simpl; intuition.
}
Qed.
Opaque DiskAllocator.free.
  

Lemma SSE_free_inode:
forall o s1 s2 v v' ret1 u,
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.free v) ret1 ->
(v < Inode.InodeAllocatorParams.num_of_blocks <-> v' < Inode.InodeAllocatorParams.num_of_blocks) ->
nth_error
      (value_to_bits
         (fst s1 Inode.InodeAllocatorParams.bitmap_addr)) v =
nth_error
      (value_to_bits
         (fst s2 Inode.InodeAllocatorParams.bitmap_addr)) v' ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.free v') ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.free Inode.InodeAllocator.free.  
unfold Inode.free, Inode.InodeAllocator.free; intros.
invert_step.
destruct (Compare_dec.lt_dec v'
Inode.InodeAllocatorParams.num_of_blocks); try lia.
cleanup.
{
  repeat invert_step.
  exists (Finished (upd (fst s2) Inode.InodeAllocatorParams.bitmap_addr (bits_to_value
  (updn (value_to_bits ((fst s2) Inode.InodeAllocatorParams.bitmap_addr)) v' false)), snd s2) (Some tt)); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  exists (Finished s2 None); split.
  repeat exec_step.
  cleanup.
  setoid_rewrite <- H1.
  repeat econstructor.
  eauto.
  simpl; intuition.

  {
    repeat invert_step_crash.
    exists (Crashed s2); repeat exec_step.

    cleanup; repeat invert_step_crash.
    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.

    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.

    exists (Crashed s2); split.
    repeat exec_step.
    setoid_rewrite D0.
    repeat econstructor.
    simpl; intuition.
  }
}
{
  repeat invert_exec.
  exists (Finished s2 None); split.
  destruct (Compare_dec.lt_dec v'
  Inode.InodeAllocatorParams.num_of_blocks); try lia.
    repeat econstructor.
    simpl; intuition.
  
    exists (Crashed s2); split.
    destruct (Compare_dec.lt_dec v'
    Inode.InodeAllocatorParams.num_of_blocks); try lia.
      repeat econstructor.
      simpl; intuition.
}
Qed.
Opaque Inode.free Inode.InodeAllocator.free.


Lemma SSE_change_owner:
forall o fm1 fm2 u' s1 s2 inum ret1 u own1 own2,
same_for_user_except u' (Some inum) fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (Inode.change_owner inum own1) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (Inode.change_owner inum own2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent Inode.change_owner.  
unfold Inode.change_owner; intros.
invert_step.
cleanup.
{
  repeat invert_step.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x2; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  unfold refines, files_rep, files_inner_rep in *; cleanup.
  eapply Inode.get_inode_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh Inode.get_inode_finished in H4; eauto.
  cleanup; split_ors; cleanup.

  eapply_fresh SSE_set_inode in H3; eauto.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence]. 
  eapply Inode.set_inode_finished_oracle_eq in H3; eauto; cleanup.

  eexists; split.
  econstructor; eauto.
  simpl; eauto.
  simpl; intuition congruence.

  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
}
{
  repeat invert_step.
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].

  repeat invert_step.
    eexists; split.
    repeat exec_step.
    simpl; intuition congruence.
}
{

  repeat invert_step_crash; try solve [solve_illegal_state].
  eapply_fresh SSE_get_inode in H2; eauto.
  cleanup.
  destruct x1; simpl in *; try solve [intuition congruence]. 

  
  exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash.
    repeat cleanup_pairs;
    repeat econstructor; eauto.
    simpl; intuition congruence.

    cleanup; try solve [solve_illegal_state];
    repeat invert_step_crash; try solve [solve_illegal_state].
    eapply_fresh SSE_get_inode in H2; eauto.
    cleanup.
    destruct x2; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].
    unfold refines, files_rep, files_inner_rep in *; cleanup.
    eapply Inode.get_inode_finished in H2; eauto.
    cleanup; split_ors; cleanup.
    eapply_fresh Inode.get_inode_finished in H4; eauto.
    cleanup; split_ors; cleanup.
  
    eapply_fresh SSE_set_inode in H3; eauto.
    cleanup.
    destruct x8; simpl in *; try solve [intuition congruence].   


    exists (Crashed s3); split.
    econstructor; eauto.
    simpl; eauto.
    simpl; intuition congruence.
    {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
  }

  eapply_fresh SSE_get_inode in H2; eauto.
    cleanup.
    destruct x0; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh Inode.get_inode_finished_oracle_eq in H2; eauto.
    cleanup; destruct o; try solve [intuition congruence].

    exists (Crashed s0); split.
    repeat exec_step.
    simpl; intuition congruence.

 }
Unshelve.
all: eauto.
Qed.
Opaque Inode.change_owner.



Lemma SSE_auth_then_exec:
forall T (p1 p2: addr -> prog _ (option T)) inum ex,
(forall o fm1 fm2 s1 s2 ret1 u u',
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (p1 inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (p2 inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None) /\
(forall s1 r1 s2 r2, ret1 = Finished s1 r1 -> ret2 = Finished s2 r2 -> (r1 = None <-> r2 = None))) -> 

forall o fm1 fm2 s1 s2 ret1 u u',
same_for_user_except u' ex fm1 fm2 ->
refines s1 fm1 ->
refines s2 fm2 ->
exec (AuthenticatedDiskLayer.AuthenticatedDiskLang) u o s1 (auth_then_exec inum p1) ret1 ->
exists ret2, 
exec (AuthenticatedDiskLayer.AuthenticatedDiskLang) u o s2 (auth_then_exec inum p2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
  Opaque Inode.get_owner.
  unfold auth_then_exec; intros.
  destruct ret1.
  {
  repeat invert_exec.
  4: {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     3:{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H9; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H28 in H6; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H31 in H25; eauto; cleanup.
       eapply H32 in H22; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     simpl; intuition congruence.
   }
   2:{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].

     eapply H in H10; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     edestruct H14; eauto.
     destruct o; try solve [ intuition congruence]. 
     destruct s2.
     {
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     repeat econstructor.
     {
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H20; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh a0 in H1; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H24 in H20; eauto; cleanup.
       eapply H26 in H17; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite H1; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
    {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H11; eauto.
        2: rewrite H2; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
   }
   {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].

     eapply H in H10; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     edestruct H14; eauto.
     destruct o; try solve [ intuition congruence].
     destruct s2.
     {
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     repeat econstructor.
     {
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H18; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh a0 in H1; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H25 in H21; eauto; cleanup.
       eapply H27 in H18; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite H1; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t5); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
    {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H11; eauto.
        2: rewrite H2; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t4); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
   }
  }
  {
  repeat invert_exec.
  split_ors; repeat invert_exec; cleanup.
  {
     eapply_fresh SSE_get_owner in H5; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     destruct s2.
     exists (Crashed (s2, s0)); split.
     repeat rewrite <- app_assoc.
     eapply ExecBindCrash.
     eapply lift2_exec_step_crashed; eauto.
     simpl; intuition congruence.
  }
  {
    repeat invert_exec.
    eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x4; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
    repeat invert_step_crash.
    {
      destruct s2.
     exists (Crashed (s, s0)); split.
     econstructor.
     eapply lift2_exec_step; eauto.
     simpl; repeat exec_step.
     rewrite cons_app;
     eapply ExecBindCrash;
     repeat econstructor.
     simpl; intuition congruence.
    }
    {
      eapply H in H10; eauto; cleanup.
      destruct x; simpl in *; try solve [ intuition congruence]. 
      
      destruct s2.
      {
      exists (Crashed (s2, s3)); split.
      repeat exec_step.
      repeat econstructor.
      eapply lift2_exec_step; eauto.
      repeat exec_step.

      simpl.
      rewrite cons_app;
      econstructor.
      repeat econstructor.
      {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite e0; eauto.
        cleanup; split_ors; cleanup.
        eapply Inode.get_owner_finished in H7; eauto.
        2: rewrite e; eauto.
        cleanup; split_ors; cleanup.
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H13; eauto; cleanup.
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H16; eauto; cleanup.
        unfold same_for_user_except in *; cleanup.
        eapply_fresh a0 in H1; eauto; cleanup.
        unfold file_map_rep in *; cleanup.
        eapply H20 in H16; eauto; cleanup.
        eapply H22 in H13; eauto; cleanup.
        unfold file_rep in *; cleanup.
        congruence.
      }
      simpl; repeat exec_step.
      repeat rewrite <- app_assoc.
      eapply ExecBindCrash;
      repeat econstructor.
      eapply lift2_exec_step_crashed; eauto.
      simpl; intuition congruence.
      }
      {
          unfold refines, files_rep, files_inner_rep in *; 
          simpl in *; cleanup.
          eapply Inode.get_owner_finished in H6; eauto.
          2: rewrite H1; eauto.
        repeat cleanup_pairs; simpl in *.
        unfold refines, files_rep, files_inner_rep; eauto. 
        eexists; split; eauto.

        eexists; split.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
        intros; repeat solve_bounds.
        eauto.
      }
      {
          unfold refines, files_rep, files_inner_rep in *; 
          simpl in *; cleanup.
          eapply Inode.get_owner_finished in H7; eauto.
          2: rewrite H2; eauto.
        repeat cleanup_pairs; simpl in *.
        unfold refines, files_rep, files_inner_rep; eauto. 
        eexists; split; eauto.

        eexists; split.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
        intros; repeat solve_bounds.
        eauto.
      }
    }
    {
     eapply H in H11; eauto; try logic_clean.
     destruct x; simpl in *; try solve [ intuition congruence].
     {
       cleanup; repeat invert_step_crash.
       {
         edestruct H12; eauto.
         destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, s3)); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite e0; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite e; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H15; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H18; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh a0 in H1; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H22 in H18; eauto; cleanup.
            eapply H24 in H15; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          rewrite cons_app;
          eapply ExecBindCrash;
          repeat econstructor.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (fst s3, fst s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H26; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H29 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H32 in H26; eauto; cleanup.
            eapply H33 in H23; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          rewrite cons_app;
          eapply ExecBindCrash;
          simpl; repeat econstructor.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (fst s3, fst s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H26; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H29 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H32 in H26; eauto; cleanup.
            eapply H33 in H23; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, s3)); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H28 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H31 in H25; eauto; cleanup.
            eapply H32 in H22; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          rewrite cons_app;
          eapply ExecBindCrash;
          repeat econstructor; eauto.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (snd s3, snd s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H28 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H31 in H25; eauto; cleanup.
            eapply H32 in H22; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          simpl; intuition congruence.
        }
       }
     }
     {
      unfold refines, files_rep, files_inner_rep in *; 
      simpl in *; logic_clean.
      eapply Inode.get_owner_finished in H6; eauto.
    repeat cleanup_pairs; simpl in *.
    unfold refines, files_rep, files_inner_rep; eauto. 
     eexists; split; eauto.

    eexists; split.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
    intros; repeat solve_bounds.
    eauto.

  }
  {
      unfold refines, files_rep, files_inner_rep in *; 
      simpl in *; logic_clean.
      eapply Inode.get_owner_finished in H7; eauto.
    repeat cleanup_pairs; simpl in *.
    unfold refines, files_rep, files_inner_rep; eauto. 
    eexists; split; eauto.

    eexists; split.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
    intros; repeat solve_bounds.
    eauto.
  }
}
{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     exists (Crashed (s2, s)); split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H24; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H27 in H3; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H30 in H24; eauto; cleanup.
       eapply H31 in H21; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     rewrite cons_app;
     eapply ExecBindCrash;
     repeat econstructor.
     simpl; intuition congruence.
   }
   {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     exists (Crashed (s2, (snd s, snd s))); split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H24; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H27 in H3; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H30 in H24; eauto; cleanup.
       eapply H31 in H21; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     simpl; intuition congruence.
   }
   {
    destruct x4; simpl in *; try solve [ intuition congruence]. 
    eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
    destruct o; simpl in *; try solve [intuition congruence].
    repeat invert_step_crash.
    destruct s2.
    exists (Crashed (s, s0)); split.
    repeat exec_step.
    repeat econstructor.
    eapply lift2_exec_step; eauto.
    repeat exec_step.
    rewrite cons_app;
    eapply ExecBindCrash;
    repeat econstructor.
    simpl; intuition congruence.

    destruct s2.
    exists (Crashed (s, (snd s0, snd s0))); split.
    repeat exec_step.
    repeat econstructor.
    eapply lift2_exec_step; eauto.
    repeat exec_step.
    simpl; intuition congruence.
   }
  }
  }
Unshelve.
all: eauto.
all: exact Definitions.impl.
Qed.