Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType TSCommon InodeTS.

Lemma inode_allocations_are_same_2:
forall u im1 im2 fm1 fm2 bm1 bm2 s1 s2 inum ex,
Inode.inode_rep im1 s1 ->
Inode.inode_rep im2 s2 ->
file_map_rep fm1 im1 bm1 ->
file_map_rep fm2 im2 bm2 ->
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
  destruct_fresh (im1 inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    destruct_fresh (fm1 inum).
    {
      destruct_fresh (im2 inum).
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H15.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H13, H7 in D; simpl in *; congruence.
      rewrite nth_seln_eq in H.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H8, H18 in D1; simpl in *; congruence.
      rewrite nth_seln_eq in H15, H0.
      rewrite H0, H15; eauto.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H3; edestruct H2; exfalso.
      apply H12; eauto.
      eapply H7; eauto; congruence.
    }
    {
      cleanup.
    }
  }
  {
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in D; eauto.
    cleanup.
    destruct_fresh (fm1 inum).
    {
      congruence.
    }
    destruct_fresh (im2 inum).
    {
      unfold file_map_rep in *; cleanup.
      edestruct H1; edestruct H3; exfalso.
      eapply H9; eauto.
      eapply H12; eauto.
      eapply H2; congruence.
    }
    {
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H14.
      cleanup; split_ors; cleanup; try congruence.
      rewrite nth_seln_eq in H0.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H9.
      cleanup; split_ors; cleanup; try congruence.
      rewrite nth_seln_eq in H17.
      rewrite H0, H17; eauto.
      rewrite H7, H18 in D1; simpl in *; congruence.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
      rewrite H12, H14 in D; simpl in *; congruence.
    }
  }
Qed.

Lemma TS_free_all_blocks:
forall bnl1 bnl2 o s1 s2 ret1 u dm1 dm2,
DiskAllocator.block_allocator_rep dm1 (fst (snd s1)) ->
DiskAllocator.block_allocator_rep dm2 (fst (snd s2)) ->
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s1 (free_all_blocks bnl1) ret1 ->
length bnl1 = length bnl2 ->
Forall (fun a => a < DiskAllocatorParams.num_of_blocks) bnl1 ->
Forall (fun a => a < DiskAllocatorParams.num_of_blocks) bnl2 ->
Forall (fun a => nth_error (value_to_bits (fst (snd s1) DiskAllocatorParams.bitmap_addr)) a = Some true) bnl1 ->
Forall (fun a => nth_error (value_to_bits (fst (snd s2) DiskAllocatorParams.bitmap_addr)) a = Some true) bnl2 ->
NoDup bnl1 ->
NoDup bnl2 ->
exists ret2, 
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s2 (free_all_blocks bnl2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
  induction bnl1; simpl; intros; eauto.
  {
    invert_exec;
    destruct bnl2; simpl in *; try lia.
    eexists; split.
    repeat econstructor.
    simpl; intuition.

    eexists; split.
    repeat econstructor.
    simpl; intuition.
  }
  {
   invert_exec;
   destruct bnl2; simpl in *; try lia.
   {
   eapply_fresh TS_free in H1.
   cleanup.
   destruct x2; simpl in *; try solve [intuition congruence].
   eapply_fresh DiskAllocator.free_finished_oracle_eq in H1; eauto.
   destruct o; simpl in *; try solve [intuition congruence].
   eapply_fresh DiskAllocator.free_finished in H1; eauto.
   cleanup; split_ors; cleanup.
   eapply_fresh DiskAllocator.free_finished in H10; only 2: apply H0; eauto.
   cleanup; split_ors; cleanup.

   eapply IHbnl1 in H9.
   cleanup.
   destruct x2; simpl in *; try solve [intuition congruence].
  exists (Finished s3 o); split.
  econstructor.
  eauto.
  simpl; eauto.
  simpl; intuition congruence.
  eauto.
  eauto.
  eauto.
  inversion H3; eauto.
  inversion H4; eauto.
  {
    inversion H3; eauto.
    inversion H5; eauto; cleanup.
    inversion H7; subst.
    repeat cleanup_pairs.
    unfold DiskAllocator.block_allocator_rep in *; cleanup.
    eapply Forall_forall; intros.
    eapply Forall_forall in H22; eauto.
    eapply DiskAllocator.valid_bits_extract with (n:= x1) in H32.
    cleanup.
    eapply DiskAllocator.valid_bits_extract with (n:= x1) in H20.
    cleanup.
    repeat rewrite nth_seln_eq in *.
    eapply Forall_forall in H26; eauto.
    eapply nth_error_nth with (d:= false) in H26.
    setoid_rewrite H26 in H12.
    setoid_rewrite Mem.delete_ne in H20; eauto.
    repeat split_ors; cleanup; try congruence; eauto.
    erewrite nth_error_nth'. 
    setoid_rewrite H20; eauto.
    all: try rewrite value_to_bits_length;
    pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
    unfold DiskAllocatorParams.num_of_blocks in *; try lia.
    all: intros Hx; subst; intuition.
  }
  {
    inversion H4; eauto.
    inversion H6; eauto; cleanup.
    inversion H8; subst.
    repeat cleanup_pairs.
    unfold DiskAllocator.block_allocator_rep in *; cleanup.
    eapply Forall_forall; intros.
    eapply Forall_forall in H22; eauto.
    eapply DiskAllocator.valid_bits_extract with (n:= x1) in H29.
    cleanup.
    eapply DiskAllocator.valid_bits_extract with (n:= x1) in H15.
    cleanup.
    repeat rewrite nth_seln_eq in *.
    eapply Forall_forall in H26; eauto.
    eapply nth_error_nth with (d:= false) in H26.
    setoid_rewrite H26 in H12.
    setoid_rewrite Mem.delete_ne in H15; eauto.
    repeat split_ors; cleanup; try congruence; eauto.
    erewrite nth_error_nth'. 
    setoid_rewrite H15; eauto.
    all: try rewrite value_to_bits_length;
    pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
    unfold DiskAllocatorParams.num_of_blocks in *; try lia.
    all: intros Hx; subst; intuition.
  }
  inversion H7; eauto.
  inversion H8; eauto.
  inversion H3; inversion H4; subst.
  intuition.
  inversion H5; inversion H6; 
  subst; eauto.
  setoid_rewrite H16; eauto.
   }
   {
     invert_step.
    eapply_fresh TS_free in H1.
    cleanup.
    destruct x0; simpl in *; try solve [intuition congruence].
    eapply_fresh DiskAllocator.free_finished_oracle_eq in H1; eauto.
    destruct o; simpl in *; try solve [intuition congruence].
   exists (Finished s0 None); split.
   econstructor.
   eauto.
   simpl; eauto.
   repeat econstructor.
   simpl; intuition congruence.
   inversion H3; inversion H4; subst.
  intuition.
  inversion H5; inversion H6; 
  subst; eauto.
  setoid_rewrite H15; eauto.
   }
   {
     repeat invert_step_crash.
     {
        eapply_fresh TS_free in H1.
        cleanup.
        destruct x; simpl in *; try solve [intuition congruence].

        exists (Crashed s0); split.
        eapply ExecBindCrash.
        eauto.
        simpl; intuition congruence.
        inversion H3; inversion H4; subst.
        intuition.
        inversion H5; inversion H6; 
        subst; eauto.
        setoid_rewrite H15; eauto.
      }
      {
        eapply_fresh TS_free in H9.
        logic_clean.
        destruct x3; simpl in *; try solve [intuition congruence].
        eapply_fresh DiskAllocator.free_finished_oracle_eq in H9; eauto.
      eapply_fresh DiskAllocator.free_finished in H1; eauto.
      eapply_fresh DiskAllocator.free_finished in H9; only 2: apply H; eauto.
      cleanup; repeat split_ors; cleanup; simpl in *; try solve [intuition congruence].
      {
        eapply IHbnl1 in H10.
   cleanup.
   destruct x0; simpl in *; try solve [intuition congruence].
  exists (Crashed s3); split.
  econstructor.
  eauto.
  simpl; eauto.
  simpl; intuition congruence.
  eauto.
  eauto.
  eauto.
  inversion H3; eauto.
  inversion H4; eauto.
  {
    inversion H3; eauto.
    inversion H5; eauto; cleanup.
    inversion H7; subst.
    repeat cleanup_pairs.
    unfold DiskAllocator.block_allocator_rep in *; cleanup.
    eapply Forall_forall; intros.
    eapply Forall_forall in H22; eauto.
    eapply DiskAllocator.valid_bits_extract with (n:= x) in H32.
    cleanup.
    eapply DiskAllocator.valid_bits_extract with (n:= x) in H15.
    cleanup.
    repeat rewrite nth_seln_eq in *.
    eapply Forall_forall in H26; eauto.
    eapply nth_error_nth with (d:= false) in H26.
    setoid_rewrite H26 in H12.
    setoid_rewrite Mem.delete_ne in H15; eauto.
    repeat split_ors; cleanup; try congruence; eauto.
    erewrite nth_error_nth'. 
    setoid_rewrite H15; eauto.
    all: try rewrite value_to_bits_length;
    pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
    unfold DiskAllocatorParams.num_of_blocks in *; try lia.
    all: intros Hx; subst; intuition.
  }
  {
    inversion H4; eauto.
    inversion H6; eauto; cleanup.
    inversion H8; subst.
    repeat cleanup_pairs.
    unfold DiskAllocator.block_allocator_rep in *; cleanup.
    eapply Forall_forall; intros.
    eapply Forall_forall in H22; eauto.
    eapply DiskAllocator.valid_bits_extract with (n:= x) in H29.
    cleanup.
    eapply DiskAllocator.valid_bits_extract with (n:= x) in H20.
    cleanup.
    repeat rewrite nth_seln_eq in *.
    eapply Forall_forall in H26; eauto.
    eapply nth_error_nth with (d:= false) in H26.
    setoid_rewrite H26 in H12.
    setoid_rewrite Mem.delete_ne in H20; eauto.
    repeat split_ors; cleanup; try congruence; eauto.
    erewrite nth_error_nth'. 
    setoid_rewrite H20; eauto.
    all: try rewrite value_to_bits_length;
    pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
    unfold DiskAllocatorParams.num_of_blocks in *; try lia.
    all: intros Hx; subst; intuition.
  }
  inversion H7; eauto.
  inversion H8; eauto.
  }
  {
    invert_step.
   exists (Crashed s0); split.
   econstructor.
   eauto.
   simpl; eauto.

   repeat econstructor.
   simpl; intuition congruence.
  }
  inversion H3; inversion H4; subst.
  intuition.
  inversion H5; inversion H6; 
  subst; eauto.
  setoid_rewrite H16; eauto.
  }
  }
}
Unshelve.
all: eauto.
Qed.

Lemma TS_delete_inner:
forall o ex fm1 fm2 s1 s2 inum ret1 u u',
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst (snd s1)) ->
files_inner_rep fm2 (fst (snd s2)) ->
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s1 (delete_inner inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s2 (delete_inner inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof. 
Transparent delete_inner.  
unfold delete_inner; intros.
invert_step.
{
  eapply_fresh TS_get_all_block_numbers in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence].
  eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H2; eauto.
  destruct o; simpl in *; try solve [intuition congruence].
  unfold files_inner_rep in *; cleanup.
  eapply_fresh Inode.get_all_block_numbers_finished in H2; eauto.
  eapply_fresh Inode.get_all_block_numbers_finished in H5; eauto.
  cleanup; repeat split_ors; cleanup.

  eapply_fresh TS_free_all_blocks in H3.
  cleanup.
  destruct x10; simpl in *; try solve [intuition congruence].
  eapply_fresh free_all_blocks_finished_oracle_eq in H3.
  2: apply H7.
  destruct o; simpl in *; try solve [intuition congruence].
  eapply_fresh FileInnerSpecs.free_all_blocks_finished in H3; eauto.
  eapply_fresh FileInnerSpecs.free_all_blocks_finished in H7.
  cleanup; repeat split_ors; cleanup.

  eapply_fresh TS_free_inode in H4.
  cleanup.
  destruct x12; simpl in *; try solve [intuition congruence].
  eapply_fresh Inode.free_finished_oracle_eq in H4; eauto.

  exists (Finished s4 o); split.
  econstructor; eauto.
  simpl; econstructor; eauto.
  simpl; eauto.
  simpl; intuition congruence.
  intuition.
  all: eauto.
  all: try solve[ 
  eapply DiskAllocator.block_allocator_rep_inbounds_eq; 
  eauto; intros; repeat solve_bounds].
  {
    
    eapply inode_allocations_are_same_2.
    5: eauto.
    all: eauto.
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep in *; cleanup.
      eexists; split.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
      apply b0.
      intros; repeat solve_bounds.
      eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep in *; cleanup.
      eexists; split.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
      apply b.
      intros; repeat solve_bounds.
      eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, 
      Inode.InodeAllocator.block_allocator_rep,
      Inode.inode_map_rep in *; cleanup.
      destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); eauto.
      rewrite e5, e8 in H23; simpl in *; try lia; try congruence.
    }
  }
  {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
  }
  {
    eapply SameRetType.all_block_numbers_in_bound.
    2: eauto.
    all: eauto.
  }
  {
    eapply SameRetType.all_block_numbers_in_bound.
    4: eauto.
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; FileInnerSpecs.solve_bounds.
  }
    {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto.
      cleanup.
      unfold same_for_user_except in *; cleanup.
      eapply_fresh H17 in H7; eauto; cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H25 in H23; eauto; cleanup.
      eapply_fresh H24 in H22; eauto; cleanup.
      eauto.
    }
    {
    eapply SameRetType.all_block_numbers_in_bound.
    4: eauto.
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; FileInnerSpecs.solve_bounds.
  }
  {
    eapply SameRetType.all_block_numbers_in_bound.
    4: eauto.
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; FileInnerSpecs.solve_bounds.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H16 in H23; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H24; cleanup.
      eapply nth_error_Some in H24.
      destruct_fresh (nth_error (Inode.block_numbers x9) x11); try congruence.
      eapply_fresh H21 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H25 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v0; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H11; erewrite nth_error_nth'; eauto.
      rewrite H19, H11; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H27; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H27; try congruence; try lia.
      setoid_rewrite D in H24; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H15 in H22; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H24; cleanup.
      eapply nth_error_Some in H24.
      destruct_fresh (nth_error (Inode.block_numbers x8) x11); try congruence.
      eapply_fresh H21 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H25 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H11; erewrite nth_error_nth'; eauto.
      rewrite H14, H11; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H27; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H27; try congruence; try lia.
      setoid_rewrite D in H24; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H24 in H23; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H16 in H22; cleanup; eauto.
    }
}
{
  eapply_fresh TS_get_all_block_numbers in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence].
  eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H2; eauto.
  destruct o; simpl in *; try solve [intuition congruence].
  unfold files_inner_rep in *; cleanup.
  eapply_fresh Inode.get_all_block_numbers_finished in H2; eauto.
  eapply_fresh Inode.get_all_block_numbers_finished in H4; eauto.
  cleanup; repeat split_ors; cleanup.

  eapply_fresh TS_free_all_blocks in H3.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence].
  eapply_fresh free_all_blocks_finished_oracle_eq in H3.
  2: apply H6.
  destruct o; simpl in *; try solve [intuition congruence].
  eapply_fresh FileInnerSpecs.free_all_blocks_finished in H3; eauto.
  eapply_fresh FileInnerSpecs.free_all_blocks_finished in H6.
  cleanup; repeat split_ors; cleanup.

  exists (Finished s3 None); split.
  econstructor; eauto.
  simpl; econstructor; eauto.
  simpl; eauto.
  repeat econstructor.
  simpl; intuition congruence.
  all: eauto.
  all: try solve[ 
  eapply DiskAllocator.block_allocator_rep_inbounds_eq; 
  eauto; intros; repeat solve_bounds].
  {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
  }
  {
    eapply SameRetType.all_block_numbers_in_bound.
    4: eauto.
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; FileInnerSpecs.solve_bounds.
  }
  {
    eapply SameRetType.all_block_numbers_in_bound.
    4: eauto.
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; FileInnerSpecs.solve_bounds.
  }
    {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto.
      cleanup.
      unfold same_for_user_except in *; cleanup.
      eapply_fresh H16 in H6; eauto; cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H24 in H22; eauto; cleanup.
      eapply_fresh H23 in H21; eauto; cleanup.
      eauto.
    }
    
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H15 in H21; cleanup; eauto.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H15 in H22; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x7) x9); try congruence.
      eapply_fresh H20 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v0; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H18, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H14 in H21; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x6) x9); try congruence.
      eapply_fresh H20 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H13, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H15 in H21; cleanup; eauto.
    }
}
{
  eapply_fresh TS_get_all_block_numbers in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence].
  eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H2; eauto.
  destruct o; simpl in *; try solve [intuition congruence].
  
  exists (Finished s0 None); split.
  econstructor; eauto.
  simpl; econstructor; eauto.
  simpl; intuition congruence.
}
{
  repeat invert_step_crash.
  {
    eapply_fresh TS_get_all_block_numbers in H2; eauto.
    cleanup.
    destruct x; simpl in *; try solve [intuition congruence].
    
    exists (Crashed s0); split.
    eapply ExecBindCrash; eauto.
    simpl; intuition congruence.
  }
  {
    eapply_fresh TS_get_all_block_numbers in H3; eauto.
    logic_clean.
    destruct x3; simpl in *; try solve [intuition congruence].
    eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H3; eauto.
    unfold files_inner_rep in *; logic_clean.
    eapply_fresh Inode.get_all_block_numbers_finished in H3; eauto.
    eapply_fresh Inode.get_all_block_numbers_finished in H2; eauto.
    cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
    {
      repeat invert_step_crash.
      {
        eapply_fresh TS_free_all_blocks in H4.
        cleanup.
        destruct x8; simpl in *; try solve [intuition congruence].

        exists (Crashed s3); split.
        econstructor; eauto.
        simpl;
        eapply ExecBindCrash; eauto.
        simpl; intuition congruence.

        all: eauto.
        all: try solve[ 
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; 
        eauto; intros; repeat solve_bounds].
        {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto.
      cleanup.
      unfold same_for_user_except in *; cleanup.
      eapply_fresh H16 in H6; eauto; cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H24 in H22; eauto; cleanup.
      eapply_fresh H23 in H17; eauto; cleanup.
      eauto.
    }
    
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H15 in H17; cleanup; eauto.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22 ; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H15 in H22; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x7) x9); try congruence.
      eapply_fresh H21 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v0; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H19, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H12 in H17; eauto; cleanup.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x0) x9); try congruence.
      eapply_fresh H21 in D; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v; eauto; cleanup.
      split_ors; cleanup.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H14, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply H15 in H17; cleanup; eauto.
    }
      }
      {
        eapply_fresh TS_free_all_blocks in H6.
        logic_clean.
        destruct x2; simpl in *; try solve [intuition congruence].
        eapply_fresh free_all_blocks_finished_oracle_eq in H6.
        2: apply H4.
        eapply_fresh FileInnerSpecs.free_all_blocks_finished in H6; eauto.
        eapply_fresh FileInnerSpecs.free_all_blocks_finished in H4.
        cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
        {
          eapply_fresh TS_free_inode in H12.
          cleanup.
          destruct x9; simpl in *; try solve [intuition congruence].
          exists (Crashed s4); split.
          repeat (econstructor; simpl; eauto).
          simpl; eauto.
          simpl; intuition congruence.
          intuition.
          {
    
    eapply inode_allocations_are_same_2.
    5: eauto.
    all: eauto.
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep in *; cleanup.
      eexists; split.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
      apply b0.
      intros; repeat solve_bounds.
      eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep in *; cleanup.
      eexists; split.
      eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq.
      apply b.
      intros; repeat solve_bounds.
      eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, 
      Inode.InodeAllocator.block_allocator_rep,
      Inode.inode_map_rep in *; cleanup.
      destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); eauto.
      rewrite e5, e8 in H22; simpl in *; try lia; try congruence.
    }
  }
        }
        {
          invert_exec.
          exists (Crashed s3); split.
          repeat (econstructor; simpl; eauto).
          simpl; intuition congruence.
        }
        all: eauto.
        all: try solve[ 
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; 
        eauto; intros; repeat solve_bounds].
        {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
  }
  {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; logic_clean.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; logic_clean.
      eapply H18 in H17; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; logic_clean.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; logic_clean.
      eapply H21 in H22; logic_clean; eauto.
  }
  {
    eapply DiskAllocator.block_allocator_rep_inbounds_eq.
    2: intros; repeat solve_bounds.
    eauto.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17 ; eauto.
      logic_clean.
      clear H6.
      unfold same_for_user_except in *; cleanup_no_match.
      eapply_fresh H16 in H15; eauto; cleanup_no_match.
      unfold file_map_rep, file_rep in *; cleanup_no_match.
      eapply_fresh H24 in H22; eauto; cleanup_no_match.
      eapply_fresh H23 in H17; eauto; cleanup_no_match.
      eauto.
    }
    
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H5.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup_no_match.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup_no_match.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H6.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup_no_match.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup_no_match.
      eapply H15 in H17; cleanup; eauto.
  }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H6.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto.
      cleanup_no_match.
      unfold file_map_rep, file_rep in *; cleanup_no_match.
      eapply_fresh H15 in H22; eauto; cleanup_no_match.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup_no_match.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x7) x10); try congruence.
      eapply_fresh H21 in D; cleanup_no_match.
      unfold DiskAllocator.block_allocator_rep in *; cleanup_no_match.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v0; eauto; cleanup_no_match.
      split_ors; cleanup_no_match.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H19, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e4 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H6.
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto.
      cleanup_no_match.
      unfold file_map_rep, file_rep in *; cleanup_no_match.
      eapply_fresh H9 in H17; eauto; cleanup_no_match.
      eapply Forall_forall; eauto; intros.
      eapply In_nth in H23; cleanup_no_match.
      eapply nth_error_Some in H23.
      destruct_fresh (nth_error (Inode.block_numbers x0) x10); try congruence.
      eapply_fresh H21 in D; cleanup_no_match.
      unfold DiskAllocator.block_allocator_rep in *; cleanup_no_match.
      eapply nth_error_nth in D.
      rewrite H24 in D; subst.
      eapply DiskAllocator.valid_bits_extract with (n:= a) in v; eauto; cleanup_no_match.
      split_ors; cleanup_no_match.
      rewrite nth_seln_eq in H10; erewrite nth_error_nth'; eauto.
      rewrite H14, H10; eauto.
      all: try rewrite value_to_bits_length;
      unfold DiskAllocatorParams.num_of_blocks in *;
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      destruct (Compare_dec.lt_dec a FSParameters.file_blocks_count); try lia.
      rewrite e1 in H26; try congruence; try lia.
      setoid_rewrite D in H23; intuition.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H6.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup_no_match.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup_no_match.
      eapply H23 in H22; cleanup; eauto.
    }
    {
      repeat cleanup_pairs;
      repeat unify_invariants.
      clear H6.
      unfold Inode.inode_rep, file_map_rep, file_rep, Inode.inode_map_rep in *; cleanup_no_match.
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup_no_match.
      eapply H15 in H17; cleanup; eauto.
    }
      }
    }
    {
      invert_exec.
      eapply_fresh TS_get_all_block_numbers in H3; eauto.
      logic_clean.
      destruct x; simpl in *; try solve [intuition congruence].
      eapply_fresh Inode.get_all_block_numbers_finished_oracle_eq in H3; eauto.
      destruct o; simpl in *; try solve [intuition congruence].

      exists (Crashed s3); split.
      repeat (econstructor; simpl; eauto).
      simpl; intuition congruence.

      unfold files_inner_rep; eexists; eauto.
      unfold files_inner_rep; eexists; eauto.
    }
  }
}
Unshelve.
all: eauto.
Qed. 
Opaque delete_inner.


Theorem Termination_Sensitive_delete:
  forall u u' m inum ex,
    Termination_Sensitive
      u (delete inum) (delete inum) recover
      AD_valid_state (AD_related_states u' ex)
      (authenticated_disk_reboot_list m).
Proof.
  Opaque change_owner_inner.
  unfold Termination_Sensitive, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  delete;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**write finished **)
   invert_exec.
   eapply TS_auth_then_exec in H11; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eexists; econstructor_recovery.
     eauto.
   }
   {
     intros.
     eapply_fresh TS_delete_inner in H7.
     3: eauto.
     3: eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.delete_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
     }
     {
      eexists.
      intuition eauto; cleanup; eauto.
     }
     eauto.
   }
  }
  {
    invert_exec.
    eapply_fresh TS_auth_then_exec in H14; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eapply_fresh FileSpecs.delete_crashed in H14; eauto.
    eapply_fresh FileSpecs.delete_crashed in H1; eauto.
    repeat split_ors; cleanup.
    {
      match goal with
        [H: refines ?s1 ?x,
        H0: refines ?s2 ?x0, 
        H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply Termination_Sensitive_recover in A;
          try instantiate (1:= (fst s, (snd (snd s), snd (snd s)))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: eexists; econstructor_recovery; [|eauto]; eauto.
     {
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
     }
   }
   {
      exfalso; eapply delete_crashed_exfalso; eauto.
   }
   {
      exfalso; eapply delete_crashed_exfalso.
      eapply same_for_user_except_symmetry. eauto.
      all: eauto.
   }
   {
      match goal with
        [H: refines ?s1 ?x,
        H0: refines ?s2 ?x0, 
        H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply Termination_Sensitive_recover in A;
          try instantiate (1:= (fst s, (snd (snd s), snd (snd s)))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: eexists; econstructor_recovery; [|eauto]; eauto.
     {
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
       {
         unfold same_for_user_except in *; cleanup.
         split; intros. 
         unfold addrs_match_exactly in *; intros.
         destruct (addr_dec a1 inum);
         [repeat rewrite Mem.delete_eq; eauto; intuition congruence
         |repeat rewrite Mem.delete_ne; eauto; intuition congruence].
         split; intros.
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.delete_eq in H5, H16; eauto; cleanup
         |rewrite Mem.delete_ne in H5, H16; eauto; cleanup].
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.delete_eq in H5, H4; eauto; cleanup
         |rewrite Mem.delete_ne in H5, H4; eauto; cleanup].
         }
       }
     }
   }
  }
  {
     intros.
     eapply_fresh TS_delete_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.delete_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
     }
     {
      eexists.
      intuition eauto; cleanup; eauto.
     }
  }
}
Unshelve.
all: eauto.
Qed.
