Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language.

Lemma blocks_allocator_rep_upd:
forall x4 t0 a v1,
DiskAllocator.block_allocator_rep x4 t0 ->
nth_error (value_to_bits (t0 DiskAllocatorParams.bitmap_addr)) a =
Some true ->
a < DiskAllocatorParams.num_of_blocks ->
DiskAllocator.block_allocator_rep (Mem.upd x4 a v1)
(upd t0 (DiskAllocatorParams.bitmap_addr + S a) v1).
Proof.
  unfold DiskAllocator.block_allocator_rep; intros.
  cleanup.
  exists (t0 DiskAllocatorParams.bitmap_addr), (updn x0 a v1).
  intuition eauto.
  rewrite upd_ne; eauto; lia.
  erewrite <- seln_eq_updn_eq with (l:= (value_to_bits (t0 DiskAllocatorParams.bitmap_addr))).
  erewrite <- upd_nop.
  eapply DiskAllocator.valid_bits_upd.
  eauto.
  rewrite value_to_bits_length; eauto.
  rewrite value_to_bits_length; eauto.
  pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
  unfold DiskAllocatorParams.num_of_blocks in *; lia.
  erewrite seln_eq_updn_eq.
  rewrite value_to_bits_to_value.
  rewrite upd_ne; eauto; lia.
  eapply nth_error_nth in H0.
  rewrite nth_seln_eq; eauto.
  eapply nth_error_nth in H0.
  rewrite nth_seln_eq; eauto.
  rewrite updn_length; eauto.
  rewrite Mem.upd_ne; eauto; lia.
  Unshelve.
  all: constructor.
Qed.

Lemma file_map_rep_upd:
forall x inum f off v1 x2 x4 a inode,
file_map_rep x x2 x4  ->
nth_error (Inode.block_numbers inode) off = Some a ->
x inum = Some f ->
x2 inum = Some inode ->
Inode.inode_map_valid x2 ->
file_map_rep (Mem.upd x inum (update_file f off v1)) x2 (Mem.upd x4 a v1).
Proof.
  unfold file_map_rep in *; intros; cleanup.
  split; eauto.
  unfold addrs_match_exactly in *.
  intros.
  destruct (addr_dec inum a0); subst.
  rewrite Mem.upd_eq; eauto.
  intuition congruence.
  rewrite Mem.upd_ne; eauto.

  intros.
  eapply_fresh H4 in H2; eauto.
  destruct (addr_dec inum inum0); subst.
  rewrite Mem.upd_eq in H6; eauto.
  rewrite H2 in H5.
  cleanup.
  unfold file_rep, update_file in *; 
  simpl in *; cleanup.
  intuition eauto.
  rewrite updn_length; eauto.
  destruct (addr_dec i off); subst.
  cleanup.
  exists v1.
  erewrite FileInnerSpecs.nth_error_updn_eq; eauto.                
  rewrite Mem.upd_eq; eauto.
  eapply_fresh Inode.nth_error_some_lt in H0; lia.
  eapply_fresh H7 in H8; cleanup.
  exists x0.
  erewrite FileInnerSpecs.nth_error_updn_ne; eauto.               
  rewrite Mem.upd_ne; eauto.
  destruct (addr_dec block_number a); eauto; subst.
  unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
  eapply H3 in H2; cleanup.
  eapply NoDup_nth_error in H2; eauto.
  eapply nth_error_Some; eauto.
  congruence.
  congruence.
  rewrite Mem.upd_ne in H6; eauto.
  eapply_fresh H4 in H5; eauto.
  unfold file_rep in *; cleanup.
  intuition eauto. 
  eapply_fresh H9 in H13; eauto; cleanup.
  eexists; intuition eauto.
  rewrite Mem.upd_ne; eauto.

  destruct (addr_dec block_number a); eauto; subst.
  unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
  eapply H16 in H2; eauto.
  eapply NoDup_nth_error in H2.
  instantiate (1:= i) in H2;
  instantiate (1:= length (Inode.block_numbers inode0) + off) in H2.
  eapply_fresh Inode.nth_error_some_lt in H14; lia.
  
  rewrite app_length. 
  eapply_fresh Inode.nth_error_some_lt in H0; lia.
  rewrite nth_error_app2.
  rewrite nth_error_app1.
  replace (length (Inode.block_numbers inode0) + off -
  length (Inode.block_numbers inode0)) with off.
  congruence.
  lia.
  eapply nth_error_Some; eauto.
  congruence.
  lia.
Qed.



Lemma same_for_user_except_symmetry:
   forall u ex x x0,
   same_for_user_except u ex x x0 ->
   same_for_user_except u ex x0 x.
   Proof.
       unfold same_for_user_except, 
       addrs_match_exactly; intros.
       cleanup.
       split; intuition eauto.
       eapply H; eauto.
       apply H in H2; eauto.
       symmetry; eapply H0; eauto.
       symmetry; eapply H0; eauto.
       symmetry; eapply H1; eauto.
       symmetry; eapply H1; eauto.
   Qed.


Ltac econstructor_recovery :=
  match goal with
  | [|- recovery_exec _ ?u [?o] _ [] _ _ _ ]=>
    eapply (@ExecFinished _ _ _ _ u o)
  | [|- recovery_exec _ ?u (?o :: _) _ (?rf :: _) _ _ _ ]=>
    eapply (@ExecRecovered _ _ _ _ u o _ _ _ rf)
  end.

  Ltac invert_exec_lift_no_match :=
  match goal with
  | [H: Language.exec' _ _ _ (Op _ (P1 _)) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (Op _ (P2 _)) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- lift_L1 _ _; _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- lift_L2 _ _; _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- Op _ (P1 _); _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- Op _ (P2 _); _) _ |- _ ]=>
    invert_exec'' H
  | _ =>
    try invert_exec_no_match
  end.

  Ltac invert_exec_lift :=
  match goal with
  | [H: Language.exec' _ _ _ (Op _ (P1 _)) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (Op _ (P2 _)) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- lift_L1 _ _; _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- lift_L2 _ _; _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- Op _ (P1 _); _) _ |- _ ]=>
    invert_exec'' H
  | [H: Language.exec' _ _ _ (_ <- Op _ (P2 _); _) _ |- _ ]=>
    invert_exec'' H
  | _ =>
    try invert_exec
  end.

Theorem SelfSimulation_Exists_recover:
  forall u u' n ex,
      SelfSimulation_Exists u recover recover recover
          AD_valid_state (AD_related_states u' ex)
          (authenticated_disk_reboot_list n).
Proof.
  induction n; simpl;
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list in *;
  intros; cleanup; simpl in *.
  {
    invert_exec; cleanup.
    unfold recover in *; repeat invert_exec; simpl in *.
    simpl in H11.
    repeat invert_exec_lift_no_match.
    eexists.    
    econstructor_recovery.
    repeat econstructor.
  }
  {
    invert_exec; cleanup.
    unfold recover in *; repeat invert_exec; simpl in *.
    repeat invert_exec_lift_no_match.
    repeat cleanup_pairs.    
    destruct s2, s1; simpl in *.
    edestruct IHn.
    3: apply H15.
    intros; eauto.
    intros; eauto.
    instantiate (2:= (s0, (t2, t2))).
    unfold refines, files_rep in *; simpl in *.
    cleanup; do 2 eexists; intuition eauto.
    eexists.
    econstructor_recovery.
    repeat econstructor; eauto.
    simpl; eauto.
  }
Qed.

Ltac invert_bind :=
match goal with
|[H: exec' _ _ _ (Ret _) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (Op _ (P1 _)) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (Op _ (P2 _)) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (_ <- _ ; _) _ |- _] =>
invert_exec'' H
| _ =>
  try invert_exec
end.

Ltac invert_bind_no_match :=
match goal with
|[H: exec' _ _ _ (Ret _) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (Op _ (P1 _)) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (Op _ (P2 _)) _ |- _] =>
invert_exec'' H
|[H: exec' _ _ _ (_ <- _ ; _) _ |- _] =>
invert_exec'' H
| _ =>
  try invert_exec_no_match
end.

Set Nested Proofs Allowed.
Lemma lt_le_lt:
      forall n m p q,
      n + m < q -> p <= m -> n + p < q.
Proof.  lia. Qed.

Lemma nth_error_None_r :
forall T (l: list T) n,
n >= length l ->
nth_error l n = None.
Proof.
  apply nth_error_None.
Qed.

Lemma bind_reorder_l:
  forall O (L: Language O) T  
  (p1: prog L T) T' (p2: T -> prog L T') 
  T'' (p3: T' -> prog L T'') 
  u o s r,
      exec L u o s (Bind p1 (fun t => Bind (p2 t) p3)) r ->
      exec L u o s (Bind (Bind p1 p2) p3) r.
Proof.  Proof.
eapply bind_reorder.
Qed.

Lemma bind_reorder_r:
  forall O (L: Language O) T  
  (p1: prog L T) T' (p2: T -> prog L T') 
  T'' (p3: T' -> prog L T'') 
  u o s r,
  exec L u o s (Bind (Bind p1 p2) p3) r ->
      exec L u o s (Bind p1 (fun t => Bind (p2 t) p3)) r.
      
Proof.  Proof.
eapply bind_reorder.
Qed.

Lemma inode_allocations_are_same:
forall u fm1 fm2 s1 s2 t1 t2 inum ex,
refines s1 fm1 ->
refines s2 fm2 ->
same_for_user_except u ex fm1 fm2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
t1 = fst (snd s1) ->
t2 = fst (snd s2) ->
nth_error
(value_to_bits
  (t1 Inode.InodeAllocatorParams.bitmap_addr))
inum =
nth_error
  (value_to_bits (t2 
  Inode.InodeAllocatorParams.bitmap_addr)) inum.
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
      destruct_fresh (x1 inum).
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H4, H10 in D; simpl in *; congruence.
      rewrite nth_seln_eq in H3.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H15, H21 in D1; simpl in *; congruence.
      rewrite nth_seln_eq in H20.
      rewrite H3, H20; eauto.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H9; exfalso.
      apply H13; eauto; congruence.
    }
    {
      edestruct H1; exfalso.
      apply H3; eauto; congruence.
    }
  }
  {
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in D; eauto.
    cleanup.
    destruct_fresh (fm1 inum).
    {
      edestruct H1; exfalso.
      apply H; eauto; congruence.
    }
    destruct_fresh (x1 inum).
    {
      unfold file_map_rep in *; cleanup.
      edestruct H3; exfalso.
      apply H12; eauto; congruence.
    }
    {
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
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
      rewrite H3, H7 in D; simpl in *; congruence.
    }
  }
Qed.

Lemma inode_owners_are_same:
forall u fm1 fm2 s1 s2 inum ex,
refines s1 fm1 ->
refines s2 fm2 ->
same_for_user_except u ex fm1 fm2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (fst (snd s1) Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
  Inode.owner (Inode.decode_inode
(fst (snd s1) (Inode.InodeAllocatorParams.bitmap_addr + S inum))) =
  Inode.owner
(Inode.decode_inode
(fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum))).
Proof.
  unfold refines, files_rep, 
  files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x1 inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    destruct_fresh (fm2 inum).
    {
      destruct_fresh (x inum).
      eapply_fresh H5 in D0; eauto; cleanup.
      unfold file_map_rep in *; cleanup.
      eapply_fresh H13 in D0; eauto.
      eapply_fresh H14 in D; eauto.
      unfold file_rep in *; cleanup.

      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H23.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H21, H23 in D1; simpl in *; congruence.
      rewrite H21, H23 in D1; simpl in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H28.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H26, H32 in D; simpl in *; congruence.
      rewrite H26, H32 in D; simpl in *; cleanup.
      eauto.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H8; exfalso.
      apply H14; eauto; congruence.
    }
    {
      edestruct H1; exfalso.
      apply H0; eauto; congruence.
    }
  }
  {
    unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17.
      cleanup; split_ors; cleanup; try congruence.
      eapply nth_error_nth in H3.
      rewrite <- nth_seln_eq in H3.
      rewrite H0 in H3; congruence.
      rewrite H15, H17 in D; simpl in *; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.

Lemma inode_owners_are_same':
forall u fm1 fm2 s1 s2 t1 t2 inum ex,
refines s1 fm1 ->
refines s2 fm2 ->
same_for_user_except u ex fm1 fm2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (t1 Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
t1 = fst (snd s1) ->
t2 = fst (snd s2) ->
  Inode.owner (Inode.decode_inode
(t1 (Inode.InodeAllocatorParams.bitmap_addr + S inum))) =
  Inode.owner
(Inode.decode_inode
(t2 (Inode.InodeAllocatorParams.bitmap_addr + S inum))).
Proof.
  unfold refines, files_rep, 
  files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x1 inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    destruct_fresh (fm2 inum).
    {
      destruct_fresh (x inum).
      eapply_fresh H7 in D0; eauto; cleanup.
      unfold file_map_rep in *; cleanup.
      eapply_fresh H10 in D0; eauto.
      eapply_fresh H14 in D; eauto.
      unfold file_rep in *; cleanup.

      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H23.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H21, H23 in D1; simpl in *; congruence.
      rewrite H21, H23 in D1; simpl in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H28.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H26, H32 in D; simpl in *; congruence.
      rewrite H26, H32 in D; simpl in *; cleanup.
      eauto.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H4; exfalso.
      apply H14; eauto; congruence.
    }
    {
      edestruct H1; exfalso.
      apply H0; eauto; congruence.
    }
  }
  {
    unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17.
      cleanup; split_ors; cleanup; try congruence.
      eapply nth_error_nth in H3.
      rewrite <- nth_seln_eq in H3.
      rewrite H0 in H3; congruence.
      rewrite H15, H17 in D; simpl in *; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.


Lemma block_numbers_in_length:
forall inum off a s2 d' x x0 u ex,
refines d' x ->
refines s2 x0 ->
same_for_user_except u ex x x0 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (fst (snd d') Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
nth_error
 (Inode.block_numbers
    (Inode.decode_inode
       (fst (snd d') (Inode.InodeAllocatorParams.bitmap_addr + S inum))))
 off = Some a ->
off <
length
(Inode.block_numbers
(Inode.decode_inode
  (fst (snd s2)
     (Inode.InodeAllocatorParams.bitmap_addr + S inum)))).
Proof.
  unfold refines, files_rep, 
  files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x3 inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    destruct_fresh (x0 inum).
    {
      destruct_fresh (x1 inum).
      eapply_fresh H6 in D0; eauto; cleanup.
      unfold file_map_rep in *; cleanup.
      eapply_fresh H14 in D0; eauto.
      eapply_fresh H15 in D; eauto.
      unfold file_rep in *; cleanup.

      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H24.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H22, H24 in D1; simpl in *; congruence.
      rewrite H22, H24 in D1; simpl in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H29.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H27, H33 in D; simpl in *; congruence.
      rewrite H27, H33 in D; simpl in *; cleanup.
      eapply nth_error_Some; eauto; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H9; exfalso.
      apply H15; eauto; congruence.
    }
    {
      edestruct H1; exfalso.
      apply H0; eauto; congruence.
    }
  }
  {
    unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H18.
      cleanup; split_ors; cleanup; try congruence.
      eapply nth_error_nth in H3.
      rewrite <- nth_seln_eq in H3.
      rewrite H0 in H3; congruence.
      rewrite H16, H18 in D; simpl in *; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.

Lemma block_numbers_oob:
forall inum off s2 d' x x0 u ex,
refines d' x ->
refines s2 x0 ->
same_for_user_except u ex x x0 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (fst (snd d') Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
nth_error
 (Inode.block_numbers
    (Inode.decode_inode
       (fst (snd d') (Inode.InodeAllocatorParams.bitmap_addr + S inum))))
 off = None ->
off >=
length
(Inode.block_numbers
(Inode.decode_inode
  (fst (snd s2)
     (Inode.InodeAllocatorParams.bitmap_addr + S inum)))).
     Proof.
      unfold refines, files_rep, 
      files_inner_rep, same_for_user_except; intros.
      cleanup; repeat cleanup_pairs.
      destruct_fresh (x3 inum).
      {
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
        cleanup.
        destruct_fresh (x0 inum).
        {
          destruct_fresh (x1 inum).
          eapply_fresh H6 in D0; eauto; cleanup.
          unfold file_map_rep in *; cleanup.
          eapply_fresh H14 in D0; eauto.
          eapply_fresh H15 in D; eauto.
          unfold file_rep in *; cleanup.
    
          unfold Inode.inode_rep, 
          Inode.inode_map_rep,
          Inode.InodeAllocator.block_allocator_rep in *.
          cleanup.
          eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H24.
          cleanup; split_ors; cleanup; try congruence.
          rewrite H22, H24 in D1; simpl in *; congruence.
          rewrite H22, H24 in D1; simpl in *.
          cleanup.
    
          eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H29.
          cleanup; split_ors; cleanup; try congruence.
          rewrite H27, H33 in D; simpl in *; congruence.
          rewrite H27, H33 in D; simpl in *; cleanup.
          eapply nth_error_None; eauto; congruence.
    
          all: try rewrite value_to_bits_length;
          unfold Inode.InodeAllocatorParams.num_of_blocks in *;
          pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
    
          unfold file_map_rep in *; cleanup.
          edestruct H9; exfalso.
          apply H15; eauto; congruence.
        }
        {
          edestruct H1; exfalso.
          apply H0; eauto; congruence.
        }
      }
      {
        unfold Inode.inode_rep, 
          Inode.inode_map_rep,
          Inode.InodeAllocator.block_allocator_rep in *.
          cleanup.
          eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H18.
          cleanup; split_ors; cleanup; try congruence.
          eapply nth_error_nth in H3.
          rewrite <- nth_seln_eq in H3.
          rewrite H0 in H3; congruence.
          rewrite H16, H18 in D; simpl in *; congruence.
    
          all: try rewrite value_to_bits_length;
          unfold Inode.InodeAllocatorParams.num_of_blocks in *;
          pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
      }
    Qed.

Hint Resolve block_numbers_in_length : core.
Hint Resolve block_numbers_oob : core.

Ltac exec_step:= 
  repeat eapply bind_reorder_l;
  rewrite cons_app; econstructor; 
  [solve [repeat econstructor; eauto] 
  | try solve [repeat econstructor; eauto] ].

Ltac invert_step :=
  simpl in *; 
  try match goal with
  |[A: exec _ _ _ _ _ _ |- _] =>
   repeat eapply bind_reorder_r in A 
  end;
  repeat invert_bind; simpl in *; cleanup;
  try congruence;
  try solve [unfold Inode.InodeAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.num_of_blocks,
        DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks in *;
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk; 
        pose proof DiskAllocatorParams.blocks_fit_in_disk; 
        lia].

 Ltac invert_step_crash :=
  simpl in *; 
  try match goal with
  |[A: exec _ _ _ _ _ _ |- _] =>
   repeat eapply bind_reorder_r in A 
  end;
  repeat invert_bind_no_match; simpl in *; try split_ors; cleanup_no_match;
  try congruence;
  try solve [unfold Inode.InodeAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.num_of_blocks,
        DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks in *;
        pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk; 
        pose proof DiskAllocatorParams.blocks_fit_in_disk; 
        lia].




Lemma block_nums_inbound:
forall inum off s2 fm,
refines s2 fm ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
nth_error
(value_to_bits
  (fst (snd s2) Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
(nth off
    (Inode.block_numbers
        (Inode.decode_inode
          (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0)
  < DiskAllocatorParams.num_of_blocks.
  Proof.
    unfold refines, files_rep, 
    files_inner_rep, same_for_user_except; intros.
    cleanup; repeat cleanup_pairs.
    destruct_fresh (x inum).
    {
      eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
      cleanup.
      
      unfold file_rep in *; cleanup.
  
        unfold Inode.inode_rep, 
        Inode.inode_map_rep,
        Inode.InodeAllocator.block_allocator_rep in *.
        cleanup.
  
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
        cleanup; split_ors; cleanup; try congruence.
        rewrite H5, H10 in D; simpl in *; congruence.

        unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
        eapply_fresh H6 in D; eauto.
        cleanup.
        unfold file_map_rep, file_rep in *; cleanup.
        eapply_fresh H14 in D; eauto; cleanup.

        unfold DiskAllocator.block_allocator_rep in *.
        rewrite H5, H10 in D; simpl in *; cleanup.

        destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x4 inum value0))) off).
        eapply_fresh H17 in D; cleanup.
        eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

        destruct (Compare_dec.lt_dec (nth off
        (Inode.block_numbers
           (Inode.decode_inode (seln x4 inum value0))) 0) DiskAllocatorParams.num_of_blocks); eauto.
        rewrite H20 in H21; try congruence; try lia.

        apply nth_error_None in D.
        rewrite <- nth_seln_eq, seln_oob; eauto.
        unfold DiskAllocatorParams.num_of_blocks.
        apply FSParameters.file_blocks_count_nonzero.
        lia.
        
        all: try rewrite value_to_bits_length;
        unfold Inode.InodeAllocatorParams.num_of_blocks in *;
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
    }
    {
      unfold file_rep in *; cleanup.
        unfold Inode.inode_rep, 
        Inode.inode_map_rep,
        Inode.InodeAllocator.block_allocator_rep in *.
        cleanup.
  
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H6.
        cleanup; split_ors; cleanup; try congruence.
        eapply nth_error_nth in H1.
        rewrite nth_seln_eq in H6; rewrite H6 in H1; congruence.
        rewrite H2, H9 in D; simpl in *; congruence.

        all: try rewrite value_to_bits_length;
        unfold Inode.InodeAllocatorParams.num_of_blocks in *;
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
    }
  Qed.

Lemma used_blocks_are_allocated:
forall s2 off inum fm,
refines s2 fm ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
off < length (Inode.block_numbers
(Inode.decode_inode
    (fst (snd s2)
      (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) ->
nth_error
(value_to_bits
  (fst (snd s2) Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
nth_error
    (value_to_bits
      (fst (snd s2)
          DiskAllocatorParams.bitmap_addr))
    (nth off
      (Inode.block_numbers
          (Inode.decode_inode
            (fst (snd s2)
                (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0) = Some true.
Proof.
  unfold refines, files_rep, 
  files_inner_rep; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    
    unfold file_rep in *; cleanup.

      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H8.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H6, H11 in D; simpl in *; congruence.

      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply_fresh H7 in D; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H15 in D; eauto; cleanup.

      unfold DiskAllocator.block_allocator_rep in *.
      rewrite H6, H11 in D; simpl in *; cleanup.

      destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x4 inum value0))) off).
      eapply_fresh H18 in D; cleanup.
      eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

      eapply DiskAllocator.valid_bits_extract with (n:= (nth off
      (Inode.block_numbers
         (Inode.decode_inode (seln x4 inum value0)))
      0)) in H19.
      cleanup; split_ors; cleanup; try congruence.
      erewrite nth_error_nth'; eauto.
      rewrite <- nth_seln_eq, H23; eauto.

      rewrite value_to_bits_length.
      eapply Forall_forall in H14.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H14.
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.
      
      rewrite H20.
      eapply Forall_forall in H14.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H14.
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.

      rewrite H20, value_to_bits_length. 
      apply DiskAllocatorParams.num_of_blocks_in_bounds.
      
      apply nth_error_None in D; lia.
      lia.

      rewrite H9, value_to_bits_length. 
      apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
  }
  {
    unfold file_rep in *; cleanup.
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
      cleanup; split_ors; cleanup; try congruence.
      eapply nth_error_nth in H2.
      rewrite nth_seln_eq in H7; rewrite H7 in H2; congruence.
      rewrite H3, H10 in D; simpl in *; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.

Lemma data_block_inbounds:
forall inum off s2 fm,
refines s2 fm ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
off < length (Inode.block_numbers
(Inode.decode_inode
    (fst (snd s2)
      (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) ->
nth_error
(value_to_bits
  (fst (snd s2) Inode.InodeAllocatorParams.bitmap_addr))
inum = Some true ->
DiskAllocatorParams.bitmap_addr +
S
(nth off
(Inode.block_numbers
(Inode.decode_inode
  (fst (snd (fst s2, snd s2))
    (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0) <
FSParameters.data_length.
Proof.
  unfold refines, files_rep, 
  files_inner_rep; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (x inum).
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in D; eauto.
    cleanup.
    
    unfold file_rep in *; cleanup.

      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H8.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H6, H11 in D; simpl in *; congruence.

      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply_fresh H7 in D; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H15 in D; eauto; cleanup.

      unfold DiskAllocator.block_allocator_rep in *.
      rewrite H6, H11 in D; simpl in *; cleanup.

      destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x4 inum value0))) off).
      eapply_fresh H18 in D; cleanup.
      eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

      eapply DiskAllocator.valid_bits_extract with (n:= (nth off
      (Inode.block_numbers
         (Inode.decode_inode (seln x4 inum value0)))
      0)) in H19.
      cleanup; split_ors; cleanup; try congruence.
      pose proof DiskAllocatorParams.blocks_fit_in_disk.
      unfold DiskAllocatorParams.bitmap_addr, DiskAllocatorParams.num_of_blocks in *. 

      eapply Forall_forall in H14.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H14.
      apply PeanoNat.Nat.le_succ_l in H14.
      eapply lt_le_lt; eauto.
      
      rewrite H20.
      eapply Forall_forall in H14.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H14.
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.

      rewrite H20, value_to_bits_length. 
      apply DiskAllocatorParams.num_of_blocks_in_bounds.
      
      apply nth_error_None in D; lia.
      lia.

      rewrite H9, value_to_bits_length. 
      apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
  }
  {
    unfold file_rep in *; cleanup.
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
      cleanup; split_ors; cleanup; try congruence.
      eapply nth_error_nth in H2.
      rewrite nth_seln_eq in H7; rewrite H7 in H2; congruence.
      rewrite H3, H10 in D; simpl in *; congruence.

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.

Hint Resolve data_block_inbounds: core.

Ltac substitute_facts :=
try 
  match goal with
  |[A: nth_error (value_to_bits (?t Inode.InodeAllocatorParams.bitmap_addr)) ?n = _ 
        |- context [nth_error (value_to_bits (?y Inode.InodeAllocatorParams.bitmap_addr)) ?n] ] =>
  erewrite <- inode_allocations_are_same with (t1 := t)(t2:= y);
  [ | | | eauto | | |]; 
  try match goal with
  | [|- refines _ _ ] =>
  eauto
  end; eauto;
  try solve [repeat cleanup_pairs; simpl; eauto]
  end;
try (match goal with
  |[A: nth_error ?x ?n = _ |- context [nth_error ?x ?n] ] =>
  setoid_rewrite A
  end; simpl);
try match goal with
  |[A: nth_error (Inode.block_numbers _) _ = Some _ 
  |- context [nth_error (Inode.block_numbers _) _] ] =>
  erewrite nth_error_nth' with (d:= 0)
  end;
try match goal with
  |[A: nth_error (Inode.block_numbers _) ?n = None 
  |- context [nth_error (Inode.block_numbers _) ?n] ] =>
  setoid_rewrite nth_error_None_r; eauto
  end;
try match goal with
  |[ A: refines ?s2 _,
  A0: ?inum < Inode.InodeAllocatorParams.num_of_blocks,
A1: nth_error
(value_to_bits
  (fst (snd _) Inode.InodeAllocatorParams.bitmap_addr))
?inum = Some true |- context [Compare_dec.lt_dec 
  (nth ?off (Inode.block_numbers (Inode.decode_inode
  (fst (snd (fst ?s2, snd ?s2))
      (Inode.InodeAllocatorParams.bitmap_addr + S ?inum)))) ?def) ?c] ] =>
      pose proof A1 as A2;
      erewrite inode_allocations_are_same in A2;
      [| | | eauto | | |]; 
      try match goal with
      | [|- refines _ _ ] =>
      eauto
      end; eauto;
      try solve [repeat cleanup_pairs; simpl; eauto];
      pose proof (block_nums_inbound inum off s2 _ A A0 A2);
  cleanup;
  destruct (Compare_dec.lt_dec 
  (nth off (Inode.block_numbers (Inode.decode_inode
  (fst (snd s2)
      (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) def) c) eqn:X; 
      [|simpl in *; lia];
      setoid_rewrite X
end;
try match goal with
| [A: refines (_, (?t, _)) ?x,
  A0: refines ?s2 ?x0,
  A1: same_for_user_except _ _ ?x ?x0
  |- exec' (Inode.owner (Inode.decode_inode (?t _))) _ _ _ _ ] =>
  erewrite inode_owners_are_same';
  [| | | eauto | | | |];
  try match goal with
      | [|- refines _ _ ] =>
      eauto
      end; eauto;
  try solve [repeat cleanup_pairs; simpl; eauto]

|[A: refines ?x4 ?x,
  A0: refines ?s2 ?x0,
  A1: same_for_user_except _ _ ?x ?x0
|- context[Some (Inode.owner (Inode.decode_inode (fst (snd (fst ?s2, snd ?s2)) _)))] ] =>
  erewrite inode_owners_are_same with (s1:= x4)(s2:= s2);
  [| | | eauto | |];
  try match goal with
      | [|- refines _ _ ] =>
      eauto
      end; eauto;
  try solve [repeat cleanup_pairs; simpl; eauto]
end;
try 
  match goal with
  |[|- context [nth_error (value_to_bits (_ DiskAllocatorParams.bitmap_addr)) 
  (nth _ (Inode.block_numbers _) _)] ] =>
  erewrite used_blocks_are_allocated; eauto
  end.

Ltac solve_termination :=  
  match goal with
  [H: refines ?s1 ?x,
  H0: refines ?s2 ?x0, 
  H1: same_for_user_except _ _ ?x ?x0,
  A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
    eapply SelfSimulation_Exists_recover in A;
    try instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))) in A;
    unfold AD_valid_state, refines_valid, FD_valid_state; 
    intros; eauto
  end;
  repeat match goal with
  |  [A: fst ?x = fst ?y,
  A0: snd ?x = snd ?y |- _] =>
  assert(x = y); [repeat cleanup_pairs; eauto|];
    subst; clear A A0
  end;
  match goal with
  [A : AD_related_states _ _ _ _ -> 
  exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
    edestruct A; clear A
  end;
    [ unfold AD_related_states, refines_related, FD_related_states;
      do 2 eexists; intuition eauto;
      simpl in *; unfold refines in *;
      repeat cleanup_pairs;
      unfold files_rep in *; 
      cleanup; simpl in *; 
      subst; eauto
    |];
  try match goal with
    [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
      exists (Recovered (extract_state_r s2'));
      econstructor_recovery; [|
        instantiate (1 := s2); eauto ]
    end;
    repeat eapply bind_reorder_l;
    repeat (
      repeat eapply bind_reorder_l;
      repeat exec_step;
      substitute_facts;
      repeat eapply bind_reorder_l;
      repeat exec_step);
    repeat eapply bind_reorder_l;
    try solve[
      eauto;
    repeat (rewrite cons_app;
    eapply ExecBindCrash);
    repeat cleanup_pairs;
    repeat econstructor; eauto].

Ltac solve_illegal_state := 
try match goal with
|[H: nth_error (Inode.block_numbers _) _ = Some ?a,
H0: nth_error (value_to_bits (_ DiskAllocatorParams.bitmap_addr)) ?a = Some false |- _] =>
eapply nth_error_nth in H as Htemp; 
rewrite <- Htemp in *;
erewrite used_blocks_are_allocated in H0; 
try congruence; eauto;
[ repeat cleanup_pairs; eauto
| eapply nth_error_Some; eauto;
setoid_rewrite H; congruence]
end; 
try match goal with
|[H: nth_error (Inode.block_numbers _) _ = Some ?a,
H0: nth_error (value_to_bits (_ DiskAllocatorParams.bitmap_addr)) ?a = None |- _] =>
eapply nth_error_nth in H as Htemp; 
rewrite <- Htemp in *;
erewrite used_blocks_are_allocated in H0; 
try congruence; eauto;
[ repeat cleanup_pairs; eauto
| eapply nth_error_Some; eauto;
setoid_rewrite H; congruence]
end;
try match goal with
|[H: ~ ?a < _,
H0: nth_error (Inode.block_numbers _) _ = Some ?a |- _] =>
    exfalso; apply H;
    eapply nth_error_nth in H0; 
    rewrite <- H0;
    eapply block_nums_inbound; eauto;
    repeat cleanup_pairs; eauto
end;
match goal with
|[H: ?inum < Inode.InodeAllocatorParams.num_of_blocks,
H0: nth_error (value_to_bits (_ Inode.InodeAllocatorParams.bitmap_addr)) ?inum = None |- _] =>
    apply nth_error_None in H0;
    rewrite value_to_bits_length in H0;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *;
    lia
end.

Ltac solve_termination_after_commit:=
match goal with
    [H: refines ?s1 ?x,
    H0: refines ?s2 ?x0, 
    H1: same_for_user_except _ _ ?x ?x0,
    A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
      eapply SelfSimulation_Exists_recover in A;
      try instantiate (1:= (fst s2, (fst (snd s2), fst (snd s2)))) in A;
      unfold AD_valid_state, refines_valid, FD_valid_state; 
      intros; eauto
    end;
    repeat match goal with
    |  [A: fst ?x = fst ?y,
    A0: snd ?x = snd ?y |- _] =>
    assert(x = y); [repeat cleanup_pairs; eauto|];
      subst; clear A A0
    end;
    match goal with
    [A : AD_related_states _ _ _ _ -> 
    exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
      edestruct A; clear A
    end;
      [ unfold AD_related_states, refines_related, FD_related_states;
        do 2 eexists; intuition eauto;
        simpl in *; unfold refines in *;
        repeat cleanup_pairs;
        unfold files_rep in *; 
        cleanup; simpl in *; 
        subst; repeat cleanup_pairs; eauto
      |];
    try match goal with
      [A : recovery_exec _ _ _ ?s2 _ _ _ ?s2' |- _] =>  
        exists (Recovered (extract_state_r s2'));
        econstructor_recovery; [|
          instantiate (1 := s2); eauto ]
      end;
      repeat eapply bind_reorder_l;
      repeat (
        repeat eapply bind_reorder_l;
        repeat exec_step;
        repeat substitute_facts;
        repeat eapply bind_reorder_l;
        repeat exec_step);
      repeat eapply bind_reorder_l;
      try solve[
        eauto;
      repeat (rewrite cons_app;
      eapply ExecBindCrash);
      repeat cleanup_pairs;
      repeat econstructor; eauto].


Ltac solve_termination_after_abort :=  
match goal with
[H: refines ?s1 ?x,
H0: refines ?s2 ?x0, 
H1: same_for_user_except _ _ ?x ?x0,
A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
  eapply SelfSimulation_Exists_recover in A;
  try instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))) in A;
  unfold AD_valid_state, refines_valid, FD_valid_state; 
  intros; eauto
end;
repeat match goal with
|  [A: fst ?x = fst ?y,
A0: snd ?x = snd ?y |- _] =>
assert(x = y); [repeat cleanup_pairs; eauto|];
  subst; clear A A0
end;
match goal with
[A : AD_related_states _ _ _ _ -> 
exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
  edestruct A; clear A
end;
  [ unfold AD_related_states, refines_related, FD_related_states;
    do 2 eexists; intuition eauto;
    simpl in *; unfold refines in *;
    repeat cleanup_pairs;
    unfold files_rep in *; 
    cleanup; simpl in *; 
    subst; eauto
  |];
try match goal with
  [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
    exists (Recovered (extract_state_r s2'));
    econstructor_recovery; [|
      instantiate (1 := (fst s2, (snd (snd s2), snd (snd s2)))); eauto ]
  end;
  repeat eapply bind_reorder_l;
  repeat (
    repeat eapply bind_reorder_l;
    repeat exec_step;
    repeat substitute_facts;
    repeat eapply bind_reorder_l;
    repeat exec_step);
  repeat eapply bind_reorder_l;
  try solve[
    eauto;
  repeat (rewrite cons_app;
  eapply ExecBindCrash);
  repeat cleanup_pairs;
  repeat econstructor; eauto].

