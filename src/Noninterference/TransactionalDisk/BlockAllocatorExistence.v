Require Import Framework File FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia.

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

Lemma used_blocks_are_allocated:
forall s2 off inum fm,
refines s2 fm ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
off < length (Inode.block_numbers
(Inode.decode_inode
    (fst (snd (snd s2))
      (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) ->
test_bit inum
(value_to_bits
  (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) = true ->
test_bit (nth off (Inode.block_numbers (Inode.decode_inode
            (fst (snd (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0) 
  (value_to_bits (fst (snd (snd s2)) DiskAllocatorParams.bitmap_addr)) = true.
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
      (* rewrite H4, H11 in D; simpl in *; try congruence. *)
      
      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H12 in D; eauto; cleanup.

      unfold DiskAllocator.block_allocator_rep in *.
      edestruct H7; eauto.
      rewrite H4, H11 in D; simpl in *; try congruence.
      cleanup.

      destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x4 inum value0))) off).
      edestruct H16 in D; eauto; cleanup.
      eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

      eapply DiskAllocator.valid_bits_extract with (n:= (nth off
      (Inode.block_numbers
         (Inode.decode_inode (seln x4 inum value0)))
      0)) in H19.
      cleanup; split_ors; cleanup; try congruence.

      eapply Forall_forall in H18.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H18.
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.
      
      rewrite H20.
      unfold DiskAllocatorParams.num_of_blocks; eauto.
      rewrite H20; eauto.

      apply nth_error_None in D; lia.
      lia.

      rewrite H9; eauto. 
  }
  {
    unfold file_rep in *; cleanup.
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
      cleanup; split_ors; cleanup; try congruence.
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
    (fst (snd (snd s2))
      (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) ->
test_bit inum
(value_to_bits
  (fst (snd (snd s2)) Inode.InodeAllocatorParams.bitmap_addr)) = true ->
DiskAllocatorParams.bitmap_addr +
S
(nth off
(Inode.block_numbers
(Inode.decode_inode
  (fst (snd (snd (fst s2, snd s2)))
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

      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply_fresh H7 in D; eauto.
      cleanup.
      unfold file_map_rep, file_rep in *; cleanup.
      eapply_fresh H14 in D; eauto; cleanup.

      unfold DiskAllocator.block_allocator_rep in *.
      rewrite H4, H11 in D; simpl in *; cleanup.

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

      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      apply PeanoNat.Nat.le_succ_l in H13.
      eapply lt_le_lt; eauto.
      
      rewrite H20.
      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.

      rewrite H20; eauto. 
      
      apply nth_error_None in D; lia.
      lia.

      rewrite H9; eauto.
  }
  {
    unfold file_rep in *; cleanup.
    unfold Inode.inode_rep, 
    Inode.inode_map_rep,
    Inode.InodeAllocator.block_allocator_rep in *.
    cleanup.


    eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
    cleanup; split_ors; cleanup; try congruence.
    rewrite H3, H10 in D; simpl in *; congruence.

    all: try rewrite value_to_bits_length;
    unfold Inode.InodeAllocatorParams.num_of_blocks in *;
    pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
  }
Qed.

Hint Resolve data_block_inbounds: core.


Lemma data_block_inbounds_2:
forall inum off s fm im dm inode,
Inode.inode_rep im s ->
File.DiskAllocator.block_allocator_rep dm s ->
File.file_map_rep fm im dm ->
im inum = Some inode ->
off < length (Inode.block_numbers inode) ->
File.DiskAllocatorParams.bitmap_addr +
S (seln (Inode.block_numbers inode) off 0) <
FSParameters.data_length.
Proof.
  intros.
  cleanup; repeat cleanup_pairs.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H2; eauto.
    cleanup.
    
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H5, H10 in H2; simpl in *; congruence.

      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply_fresh H6 in H2; eauto.
      cleanup.
      unfold File.file_map_rep, File.file_rep in *; cleanup.
      eapply_fresh H14 in H2; eauto; cleanup.

      unfold File.DiskAllocator.block_allocator_rep in *.
      rewrite H5, H10 in H2; simpl in *; cleanup.

      destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x2 inum value0))) off).
      eapply_fresh H18 in D; cleanup.
      eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

      eapply File.DiskAllocator.valid_bits_extract with (n:= (nth off
      (Inode.block_numbers
         (Inode.decode_inode (seln x2 inum value0)))
      0)) in H19.
      cleanup; split_ors; cleanup; try congruence.
      pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
      unfold File.DiskAllocatorParams.bitmap_addr, File.DiskAllocatorParams.num_of_blocks in *. 

      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      apply PeanoNat.Nat.le_succ_l in H13.
      eapply lt_le_lt; eauto.
      rewrite nth_seln_eq; eauto.
      

      rewrite H20.
      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.

      rewrite H20; eauto.    

      apply nth_error_None in D; lia.
      destruct (Compare_dec.lt_dec inum (length x2)); eauto.
      edestruct (H9 inum); try lia.
      rewrite H5, H in H2; simpl in *; try congruence; try lia.
      rewrite H8; eauto. 
Qed.

Set Nested Proofs Allowed.
Lemma used_blocks_are_allocated_2:
forall s off inum im inode dm fm,
Inode.inode_rep im s ->
File.DiskAllocator.block_allocator_rep
     dm s ->
     File.file_map_rep fm im dm ->
im inum = Some inode ->
off < length (Inode.block_numbers inode) ->
test_bit (seln (Inode.block_numbers inode) off 0)
  (value_to_bits
    (s File.DiskAllocatorParams.bitmap_addr)) = true.
Proof.
intros.
eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H2; eauto.
cleanup.
unfold Inode.inode_rep, Inode.inode_map_rep,
Inode.inode_map_valid,
Inode.inode_valid,
Inode.InodeAllocator.block_allocator_rep in *; cleanup.
match goal with
     | [H: ?x1 ?inum = Some _,
        H1: forall _ _, 
        ?x1 _ = Some _ -> _ /\ _|- _] =>
        eapply_fresh H1 in H; eauto; cleanup
end.
     
match goal with
| [H: Forall _ (Inode.block_numbers _)|- _] =>
  eapply_fresh Forall_forall in H; [| eapply in_seln; eauto]
end;
unfold File.DiskAllocatorParams.num_of_blocks; intuition eauto.
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
{
  match goal with
| [H: Inode.InodeAllocator.valid_bits
_ _ (value_to_bits
   (?s1
      Inode.InodeAllocatorParams.bitmap_addr))
?s1 |- _] =>
eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H; eauto
end.
all: try solve [pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
try rewrite value_to_bits_length;
unfold Inode.InodeAllocatorParams.num_of_blocks in *; try lia].
cleanup; split_ors; cleanup; try congruence.
- rewrite H5, H13 in H2; simpl in *; congruence.
- unfold File.file_map_rep, File.file_rep in *; cleanup.
eapply_fresh a0 in H2; eauto; cleanup.

unfold File.DiskAllocator.block_allocator_rep in *.
cleanup.
rewrite H5, H13 in H2; simpl in *; cleanup.

destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x2 inum value0))) off).
eapply_fresh H15 in D; cleanup.
eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

eapply File.DiskAllocator.valid_bits_extract with (n:= (nth off
(Inode.block_numbers
   (Inode.decode_inode (seln x2 inum value0)))
0)) in v.
cleanup; split_ors; cleanup; try congruence.
erewrite nth_seln_eq; eauto.

rewrite e1.
rewrite <- nth_seln_eq.
unfold File.DiskAllocatorParams.num_of_blocks in *;
pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
eapply PeanoNat.Nat.lt_le_trans; eauto.

rewrite e1; eauto. 

apply nth_error_None in D; lia.
}
{
  unfold Inode.inode_rep, Inode.inode_map_rep,
    Inode.inode_map_valid,
    Inode.inode_valid,
    Inode.InodeAllocator.block_allocator_rep in *; cleanup.
    edestruct (H10 inum); try lia.
    rewrite H5, H12 in *; 
    simpl in *; try lia; try congruence.
}
Qed.

Lemma inode_allocations_are_same:
forall im1 im2 s1 s2 inum,
Inode.inode_rep im1 s2 ->
Inode.inode_rep im2 s1 ->
addrs_match_exactly im1 im2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
test_bit inum
(value_to_bits
  (s1 Inode.InodeAllocatorParams.bitmap_addr)) =
test_bit inum
  (value_to_bits (s2 Inode.InodeAllocatorParams.bitmap_addr)).
Proof.
  unfold refines, files_rep, 
  files_inner_rep, same_for_user_except; intros.
  cleanup; repeat cleanup_pairs.
  destruct_fresh (im1 inum).
  {
      destruct_fresh (im2 inum).
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H8, H10 in D; simpl in *; congruence.
      rewrite nth_seln_eq in H.
      repeat erewrite nth_error_nth'.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H5.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H3, H14 in D0; simpl in *; congruence.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H1; exfalso.
      apply H4; eauto; congruence.
    }
  { 
    destruct_fresh (im2 inum).
    {
      unfold file_map_rep in *; cleanup.
      edestruct H1; exfalso.
      apply H4; eauto; congruence.
    }
    {
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10.
      cleanup; split_ors; cleanup; try congruence.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H5.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H3, H14 in D0; simpl in *; congruence.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
      rewrite H8, H10 in D; simpl in *; congruence.
    }
  }
Qed.

Lemma inode_allocations_are_same_2:
forall u im1 im2 fm1 fm2 bm1 bm2 s1 s2 inum ex,
Inode.inode_rep im1 s1 ->
Inode.inode_rep im2 s2 ->
file_map_rep fm1 im1 bm1 ->
file_map_rep fm2 im2 bm2 ->
same_for_user_except u ex fm1 fm2 ->
inum < Inode.InodeAllocatorParams.num_of_blocks ->
test_bit inum
(value_to_bits
  (s1 Inode.InodeAllocatorParams.bitmap_addr))
= test_bit inum
  (value_to_bits (s2 Inode.InodeAllocatorParams.bitmap_addr)).
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

      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.

      unfold file_map_rep in *; cleanup.
      edestruct H3; edestruct H2; exfalso.
      apply H14; eauto.
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
      edestruct H2; edestruct H3; exfalso.
      eapply H14; eauto.
      eapply H12; eauto.
      congruence.
    }   
    {
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.
      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H14.
      cleanup; split_ors; cleanup; try congruence.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H9.
      cleanup; split_ors; cleanup; try congruence.

      rewrite H7, H18 in D1; simpl in *; congruence.
      all: try rewrite value_to_bits_length;
      unfold Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; try lia.
      rewrite H12, H14 in D; simpl in *; congruence.
    }
  }
Qed.



Lemma get_all_file_sizes_up_to_related_equal:
forall n fm1 fm2 ex u,
same_for_user_except u ex fm1 fm2 ->
get_all_file_sizes_up_to fm1 n = get_all_file_sizes_up_to fm2 n.
Proof.
  unfold same_for_user_except; 
  induction n; simpl; intros; 
  cleanup; eauto.
  {
    erewrite IHn; eauto.
    destruct_fresh (fm1 n);
    destruct_fresh (fm2 n); eauto.
    {
      eapply H1 in D; eauto; cleanup; eauto.
    }
    {
      edestruct H; exfalso; intuition.
      eapply H2; eauto; congruence.
    }
    {
      edestruct H; exfalso; intuition.
      eapply H3; eauto; congruence.
    }
  }
Qed. 

Fixpoint count_trues_up_to n bm :=
match n with
| 0 => 0
| S x => 
  if test_bit x bm then
    S (count_trues_up_to x bm)
  else
  count_trues_up_to x bm
end.


Lemma count_trues_up_to_length :
forall n bm,
count_trues_up_to n bm <= n.
Proof.
  induction n; simpl in *; intros;
  cleanup; try lia.
  specialize (IHn bm).
  destruct (test_bit n bm); simpl; try lia.
Qed.

Lemma count_trues_up_to_length_upper_bound :
forall n bm,
count_trues_up_to n bm <= bitmap_size.
Proof.
  induction n; simpl in *; intros;
  cleanup; try lia.
  specialize (IHn bm).
  destruct_fresh (test_bit n bm); simpl; try lia.
  assert (n < bitmap_size). {
    destruct (Compare_dec.lt_dec n bitmap_size); eauto.
      pose proof test_bit_oob as Hp.
      rewrite Hp in D; try congruence; lia.
  }
  pose proof (count_trues_up_to_length n bm).
  lia.
Qed.

Lemma count_trues_up_to_all :
forall n bm,
count_trues_up_to n bm = n ->
(forall i, i < n -> test_bit i bm = true).
Proof.
  induction n; intros;
  cleanup; try lia; eauto.

  simpl in *.
  destruct (PeanoNat.Nat.eq_dec i n); subst.
  destruct (test_bit n bm); eauto.
  pose proof (count_trues_up_to_length n bm).
  lia.
  apply IHn; eauto.
  destruct (test_bit n bm); eauto.
  pose proof (count_trues_up_to_length n bm).
  lia.
  lia.
Qed.


Lemma get_first_zero_index_count_trues:
forall n bm,
get_first_zero_index bm < n <->
count_trues_up_to n bm < n.
Proof.
  induction n; simpl in *; intros;
  cleanup; try lia.
  destruct_fresh (test_bit n bm); simpl; try lia.
  edestruct (get_first_zero_index_correct bm).
  {
    intuition try lia.
    inversion H1; subst.
    {
      rewrite H in D; try congruence.
      assert (get_first_zero_index bm < bitmap_size). {
        destruct (Compare_dec.lt_dec (get_first_zero_index bm) bitmap_size); eauto.
        pose proof test_bit_oob as Hp.
        rewrite Hp in D; try congruence; lia.
      }
      lia.
    }
    {
      assert(get_first_zero_index bm < n) by lia.
      edestruct IHn; try lia.
      apply H4 in H2; lia.
    }
    {
      assert(count_trues_up_to n bm < n) by lia.
      edestruct IHn; try lia.
      apply H4 in H2; lia.
    }
  }
  {
    {
      intuition try lia.
      inversion H; subst.
      {
        pose proof (count_trues_up_to_length (get_first_zero_index bm) bm).
        lia.
      }
      {
        edestruct (IHn bm); lia.
      }
      {
        edestruct (get_first_zero_index_correct bm).
        destruct (Compare_dec.lt_dec (get_first_zero_index bm) (S n)); eauto.
        rewrite H1 in D; try congruence; lia.
      }
    }
  }
Qed.
(*
Lemma count_trues_lt_exists_empty:
forall bl,
count_trues bl < length bl ->
exists i, i < length bl /\ seln bl i false = false.
Proof.
  induction bl; simpl in *; intros;
  cleanup; try lia.
  edestruct IHbl; try lia.
  cleanup.
  exists (S x); simpl; eauto.
  split; eauto; try lia.
  exists 0; simpl; split; eauto.
  lia.
Qed.


  Lemma count_trues_upd_true:
  forall l a,
  seln l a false = false ->
  a < length l ->
  count_trues (updn l a true) = S (count_trues l).
  Proof.
    induction l; simpl; intros; try lia.
    destruct a0; simpl in *; subst; eauto.
    destruct a; eauto;
    erewrite IHl; eauto; lia.
  Qed.
  
  Lemma count_trues_upd_false:
  forall l a,
  seln l a false = true ->
  a < length l ->
  S (count_trues (updn l a false)) = count_trues l.
  Proof.
    induction l; simpl; intros; try lia.
    destruct a0; simpl in *; subst; eauto.
    destruct a; eauto;
    erewrite IHl; eauto; lia.
  Qed.

  Lemma count_trues_upd_list_true:
  forall l_a l,
  (forall a, In a l_a -> seln l a false = false) ->
  Forall (fun a => a < length l) l_a ->
  NoDup l_a -> 
  count_trues (repeated_apply (fun l a => updn l a true) l l_a) = length l_a + count_trues l.
  Proof.
    induction l_a; simpl; intros; try lia.
    inversion H0; clear H0; subst.
    inversion H1; clear H1; subst.
    erewrite count_trues_upd_true.
    rewrite IHl_a; eauto.
    erewrite seln_repeated_apply_updn; eauto.
    rewrite repeated_apply_length; intros; eauto.
    apply updn_length.
  Qed.

  Lemma count_trues_upd_list_false:
  forall l_a l,
  (forall a, In a l_a -> seln l a false = true) ->
  Forall (fun a => a < length l) l_a ->
  NoDup l_a -> 
  length l_a + count_trues (repeated_apply (fun l a => updn l a false) l l_a) 
  = count_trues l.
  Proof.
    induction l_a; simpl; intros; try lia.
    inversion H0; clear H0; subst.
    inversion H1; clear H1; subst.
    rewrite <- PeanoNat.Nat.add_succ_r.
    erewrite count_trues_upd_false.
    rewrite IHl_a; eauto.
    erewrite seln_repeated_apply_updn; eauto.
    rewrite repeated_apply_length; intros; eauto.
    apply updn_length.
  Qed.

  Lemma firstn_repeated_apply_comm:
  forall T l_a n (b: T) l,
  firstn n (repeated_apply (fun l a => updn l a b) l l_a) =
  repeated_apply (fun l a => updn l a b) (firstn n l) l_a.
  Proof.
    induction l_a; simpl; eauto.
    intros.
    rewrite updn_firstn_comm; eauto.
    rewrite IHl_a; eauto.
  Qed.
*)
Set Nested Proofs Allowed.
Lemma count_trues_up_to_count_somes_up_to_eq:
forall n bm s,
DiskAllocator.block_allocator_rep bm s ->
count_trues_up_to n (value_to_bits (s DiskAllocatorParams.bitmap_addr)) = 
count_somes_up_to n bm.
Proof.
  induction n; simpl; intros; eauto.
  erewrite IHn; eauto.
  unfold DiskAllocator.block_allocator_rep in *; logic_clean.
  destruct (Compare_dec.lt_dec n DiskAllocatorParams.num_of_blocks).
  eapply DiskAllocator.valid_bits_extract in H0; eauto.
  all: try solve [setoid_rewrite H1; eauto; lia].
  cleanup.
  split_ors; cleanup; eauto.
  edestruct (H2 n); try lia.
  cleanup; eauto.
Qed.


(*
Lemma count_trues_ge_all_some:
forall l bm s,
DiskAllocator.block_allocator_rep bm s ->
Forall (fun a => bm a <> None) l ->
NoDup l ->
count_trues_up_to (s DiskAllocatorParams.bitmap_addr) >= length l.
Proof. 
  induction l; simpl; intros.
  lia.
  inversion H0; inversion H1; 
  clear H0 H1; cleanup.  eapply_fresh DiskAllocator.block_allocator_rep_delete with (a:= a) in H.
  assert (A: Forall (fun ax : addr => (Mem.delete bm a) ax <> None) l). {
    eapply Forall_forall; intros.
    destruct (PeanoNat.Nat.eq_dec a x); subst.
    tauto.
    rewrite delete_ne; eauto.
    eapply Forall_forall in H5; eauto.
  }
  specialize (IHl _ _ Hx A H9).
  clear Hx.
  unfold DiskAllocator.block_allocator_rep in *; cleanup.
  eapply DiskAllocator.valid_bits_extract with (n:= a) in H0; eauto.
  cleanup; split_ors; cleanup; try congruence.

  replace (firstn DiskAllocatorParams.num_of_blocks
  (value_to_bits (s DiskAllocatorParams.bitmap_addr))) with
  (updn (firstn DiskAllocatorParams.num_of_blocks
  (value_to_bits
     (upd s DiskAllocatorParams.bitmap_addr
        (bits_to_value
           (updn (value_to_bits (s DiskAllocatorParams.bitmap_addr))
              a false)) DiskAllocatorParams.bitmap_addr))) a true).

  erewrite count_trues_upd_true.
  lia.
  rewrite seln_firstn.
  rewrite upd_eq.
  rewrite bits_to_value_to_bits_exact.
  rewrite seln_updn_eq; eauto.
  rewrite value_to_bits_length.
  pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
  destruct (Compare_dec.lt_dec a DiskAllocatorParams.num_of_blocks).
  unfold DiskAllocatorParams.num_of_blocks in *; lia.
  rewrite H2 in H3; try congruence; lia.
  rewrite updn_length, value_to_bits_length; eauto.
  eauto.
  destruct (Compare_dec.lt_dec a DiskAllocatorParams.num_of_blocks).
  unfold DiskAllocatorParams.num_of_blocks in *; lia.
  rewrite H2 in H3; try congruence; lia.
  pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
  rewrite firstn_length_l.
  destruct (Compare_dec.lt_dec a DiskAllocatorParams.num_of_blocks).
  unfold DiskAllocatorParams.num_of_blocks in *; lia.
  rewrite H2 in H3; try congruence; lia.
  rewrite value_to_bits_length; unfold DiskAllocatorParams.num_of_blocks; eauto.
  destruct (Compare_dec.lt_dec a DiskAllocatorParams.num_of_blocks); 
  [|rewrite H2 in H3; try congruence; lia].
  rewrite <- updn_firstn_comm.
  rewrite upd_eq.
  rewrite bits_to_value_to_bits_exact.
  
  rewrite updn_twice.
  erewrite seln_eq_updn_eq; eauto.
  rewrite updn_length, value_to_bits_length; eauto.
  eauto.
  destruct (Compare_dec.lt_dec a DiskAllocatorParams.num_of_blocks).
  unfold DiskAllocatorParams.num_of_blocks in *; lia.
  rewrite H2 in H4; try congruence; lia.
  pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
  rewrite value_to_bits_length;
  rewrite H1; unfold DiskAllocatorParams.num_of_blocks; eauto.
Qed.
*)

Lemma file_map_rep_delete_file:
      forall fm im bm s f i inum,
      file_map_rep fm im bm ->
      Inode.inode_rep im s ->
      DiskAllocator.block_allocator_rep bm s ->
      fm inum = Some f ->
      im inum = Some i ->
      let bm' := (repeated_apply (Mem.delete (AEQ:=addr_dec)) bm (Inode.block_numbers i)) in
      let s' := (upd (upd s DiskAllocatorParams.bitmap_addr
                     (bits_to_value
                        (repeated_apply (fun l a => unset_bit a l)
                                        (value_to_bits (s DiskAllocatorParams.bitmap_addr)) (Inode.block_numbers i)))) Inode.InodeAllocatorParams.bitmap_addr
                (bits_to_value
                        (unset_bit inum (value_to_bits (s Inode.InodeAllocatorParams.bitmap_addr)))))  in
 
 file_map_rep (Mem.delete fm inum) (Mem.delete im inum) bm' /\
 Inode.inode_rep (Mem.delete im inum) s' /\
 DiskAllocator.block_allocator_rep bm' s'.
    Proof.
      unfold file_map_rep, file_rep, 
    Inode.inode_rep, Inode.inode_map_rep,
    Inode.inode_map_valid, Inode.inode_valid in *;
      intros; cleanup.
      eapply_fresh H7 in H2; eauto; cleanup.
      eapply_fresh H5 in H3; cleanup.
      split.
      2: split.
      {(** file_map_rep **)
       intuition.
        {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.delete_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.delete_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H14;
             rewrite Mem.delete_eq in H15; eauto |
             rewrite Mem.delete_ne in H14;
             rewrite Mem.delete_ne in H15; eauto];
            try congruence.
            eapply_fresh H7 in H14; eauto.
            unfold file_rep in *; cleanup; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H14;
             rewrite Mem.delete_eq in H15; eauto |
             rewrite Mem.delete_ne in H14;
             rewrite Mem.delete_ne in H15; eauto];
            try congruence.
            eapply_fresh H7 in H14; eauto.
            unfold file_rep in *; cleanup; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H14;
             rewrite Mem.delete_eq in H15; eauto |
             rewrite Mem.delete_ne in H14;
             rewrite Mem.delete_ne in H15; eauto];
            try congruence.
            {
              eapply_fresh H6 in H14; eauto.
              eapply_fresh H7 in H14; eauto.
              cleanup.
              eapply_fresh H19 in H16; eauto;
              cleanup.
              eexists; intuition eauto.
              eapply nth_error_In in H16.
              eapply not_In_NoDup_app in H16; eauto.
              rewrite repeated_apply_delete_not_in; eauto.
            }
          }
          {
            rewrite count_somes_up_to_some_repeated_delete; eauto.
            erewrite get_all_file_sizes_up_to_delete; eauto.
            unfold Inode.InodeAllocator.block_allocator_rep in *.
            cleanup.
            destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); eauto.
            edestruct (H16 inum).
            lia.
            
            rewrite H4, H0 in H3; simpl in *; congruence.
            eapply Forall_forall; intros.
            eapply_fresh in_seln_exists in H14; cleanup.
            edestruct H11.
            eapply nth_error_nth'; eauto.
            rewrite <- nth_seln_eq in H17; cleanup.
            rewrite H16 in H18; eexists; eauto.
          }
        }
      {(** inode_rep **)
        eexists; intuition eauto.
        rewrite upd_comm.
        eapply Inode.InodeAllocator.block_allocator_rep_upd_noop; eauto.
        eapply Inode.InodeAllocator.block_allocator_rep_delete; eauto.
        unfold DiskAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.bitmap_addr.
        pose proof FSParameters.inodes_before_data; lia.
        destruct (addr_dec inum i0); subst.
        repeat rewrite Mem.delete_eq; simpl; eauto.
        repeat rewrite Mem.delete_ne; simpl; eauto.
        
        destruct (addr_dec inum i0); subst.
        rewrite Mem.delete_eq in H14; simpl; congruence.
        rewrite Mem.delete_ne in H14; simpl; eauto.
        eapply H5 in H14; cleanup; eauto.

        destruct (addr_dec inum i0); subst.
        rewrite Mem.delete_eq in H14; simpl; congruence.
        rewrite Mem.delete_ne in H14; simpl; eauto.
        eapply H5 in H14; cleanup; eauto.

        destruct (addr_dec inum i0); subst.
        rewrite Mem.delete_eq in H15; simpl; congruence.
        rewrite Mem.delete_ne in H15; simpl; eauto.
        destruct (addr_dec inum j); subst.
        rewrite Mem.delete_eq in H16; simpl; congruence.
        rewrite Mem.delete_ne in H16; simpl; eauto.
      }
      {
       eapply DiskAllocator.block_allocator_rep_upd_noop; eauto.
       eapply DiskAllocator.block_allocator_rep_delete_list; eauto.
        unfold DiskAllocatorParams.bitmap_addr,
        Inode.InodeAllocatorParams.bitmap_addr.
        pose proof FSParameters.inodes_before_data; lia.
      }
      Unshelve.
      eauto.
Qed.

Lemma get_all_file_sizes_up_to_delete_oob:
forall n a fm,
a >= n ->
get_all_file_sizes_up_to (Mem.delete fm a) n =
get_all_file_sizes_up_to fm n.
Proof.
  induction n; simpl; intros; eauto;
  rewrite delete_ne; eauto.
  rewrite IHn; lia.
  lia.
Qed.

(*
Lemma block_counts_up_to_le:
forall n fm s,
files_inner_rep fm s ->
length (get_trues (value_to_bits (s DiskAllocatorParams.bitmap_addr))) >=
get_all_file_sizes_up_to fm n.
Proof.
  unfold files_inner_rep; induction n; simpl; intros; cleanup.
  {
    unfold file_map_rep, file_rep, 
    Inode.inode_rep, Inode.inode_map_rep,
    Inode.inode_map_valid, Inode.inode_valid in *;
    cleanup.
    destruct_fresh (fm 0); try lia.
    destruct_fresh (x 0).
    {
      eapply_fresh H2 in D; eauto; cleanup.
      eapply_fresh H5 in D0; cleanup.
      eapply count_trues_ge_all_some; eauto.
      eapply Forall_forall; intros.
      eapply in_seln_exists in H11; cleanup.
      rewrite nth_seln_eq in H12.
      eapply nth_error_nth' in H11.
      apply H8 in H11; cleanup; try congruence.
      rewrite H12 in H13; congruence.
    }
    edestruct H; exfalso.
    eapply H6; eauto; congruence.
  }
  {
    destruct_fresh (im (S n)).
    {
    edestruct FileInnerSpecs.inode_exists_then_file_exists; eauto.
    cleanup.
    
      eapply file_map_rep_delete_file in H; eauto.
      cleanup.
      eapply IHn in H; eauto.
      rewrite upd_ne in H.
      rewrite upd_eq in H; eauto.
      rewrite bits_to_value_to_bits_exact in H.
      rewrite get_all_file_sizes_up_to_delete_oob in H; eauto.


      assert (A: length (blocks x) + count_trues
      (firstn DiskAllocatorParams.num_of_blocks
         (repeated_apply (fun (l : list bool) (a : nat) => updn l a false)
            (value_to_bits (s DiskAllocatorParams.bitmap_addr))
            (Inode.block_numbers i))) >=
            length (blocks x) + get_all_file_sizes_up_to fm n) by lia.
      rewrite firstn_repeated_apply_comm in A.
      assume (Ax: (length (blocks x) = length (Inode.block_numbers i))).
      rewrite Ax in A.
      erewrite count_trues_upd_list_false in A.
      lia.

      all: shelve. (* Solvable *)
    }
    {
      eapply FileInnerSpecs.inode_missing_then_file_missing in D; eauto.
      cleanup.
      simpl; eauto.
    }
  }
  Unshelve.
  all: eauto.
Admitted.


Lemma block_counts_ge:
forall n fm im bm s,
file_map_rep fm im bm ->
Inode.inode_rep im s ->
DiskAllocator.block_allocator_rep bm s ->
n >= FSParameters.inode_count ->
count_trues (firstn DiskAllocatorParams.num_of_blocks
(value_to_bits (s DiskAllocatorParams.bitmap_addr))) <=
get_all_file_sizes_up_to fm n.
Proof. Admitted.


Lemma not_in_inodes_then_free:
  forall a im bm fm s1,
  Inode.inode_rep im s1 ->
  DiskAllocator.block_allocator_rep bm s1 ->
  file_map_rep fm im bm ->
  (forall i inode, im i = Some inode -> ~In a (Inode.block_numbers inode)) ->
  a < DiskAllocatorParams.num_of_blocks ->
  test_bit a (value_to_bits (s1 DiskAllocatorParams.bitmap_addr)) = false.
  Proof.
    unfold Inode.inode_rep, DiskAllocator.block_allocator_rep; intros; cleanup.

    eapply DiskAllocator.valid_bits_extract in H4; eauto; cleanup.
    split_ors; cleanup; eauto.
    {
      unfold file_map_rep, file_rep in *.
      cleanup.
      apply H11 in H8; cleanup.
      exfalso; eapply H2; eauto.
    }
    eauto.
    eauto.
Qed.

Lemma get_all_file_sizes_up_to_get_trues_upper_bound:
  forall n fm1 s1,
  files_inner_rep fm1 s1 ->
  get_all_file_sizes_up_to fm1 n <=
  length (get_trues (value_to_bits (s1 DiskAllocatorParams.bitmap_addr))).
  Proof.
    induction n; unfold files_inner_rep; intros; cleanup.
    {
      simpl. 
    }
    {
      simpl.
      destruct_fresh (fm1 0).
      
      unfold file_map_rep, file_rep, 
      DiskAllocator.block_allocator_rep in *; cleanup.
      
    }


Lemma block_counts_match:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
length (get_trues (value_to_bits (s1 DiskAllocatorParams.bitmap_addr))) = 
length (get_trues (value_to_bits (s2 DiskAllocatorParams.bitmap_addr))).
Proof.
  unfold files_inner_rep; intros; cleanup.
  eapply get_all_file_sizes_up_to_related_equal in H; eauto.

  

    eapply get_all_file_sizes_up_to_related_equal in H; eauto.



rewrite firstn_length_l in *.
eauto.
rewrite value_to_bits_length;
pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
unfold DiskAllocatorParams.num_of_blocks; eauto.
rewrite value_to_bits_length;
pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
unfold DiskAllocatorParams.num_of_blocks; eauto.
2: eauto. eauto.
eauto.
eauto.
all: apply firstn_length_l; rewrite value_to_bits_length;
pose proof DiskAllocatorParams.num_of_blocks_in_bounds;
unfold DiskAllocatorParams.num_of_blocks; eauto.
Admitted.



Lemma free_block_exists_get_trues:
forall n fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
length (get_trues (value_to_bits (s1 DiskAllocatorParams.bitmap_addr))) < n ->
length (get_trues (value_to_bits (s2 DiskAllocatorParams.bitmap_addr))) < n.
Proof. 
  induction n; simpl; intros; try lia.
*)

Set Nested Proofs Allowed.

Lemma free_block_exists:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index (value_to_bits (s1 DiskAllocatorParams.bitmap_addr)) < DiskAllocatorParams.num_of_blocks ->
get_first_zero_index (value_to_bits (s2 DiskAllocatorParams.bitmap_addr)) < DiskAllocatorParams.num_of_blocks.
Proof. 
unfold files_inner_rep; intros; cleanup.
eapply get_first_zero_index_count_trues.
eapply get_first_zero_index_count_trues in H2.
erewrite count_trues_up_to_count_somes_up_to_eq; eauto.
erewrite count_trues_up_to_count_somes_up_to_eq in H2; only 2: eauto.
unfold file_map_rep in *; cleanup.
erewrite get_all_file_sizes_up_to_related_equal in H2; eauto.
Qed.

Lemma free_block_exists_iff:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index (value_to_bits (s1 DiskAllocatorParams.bitmap_addr)) < DiskAllocatorParams.num_of_blocks <->
get_first_zero_index (value_to_bits (s2 DiskAllocatorParams.bitmap_addr)) <
  DiskAllocatorParams.num_of_blocks.
Proof. 
  intros; split.
  eapply free_block_exists; eauto.
  eapply free_block_exists.
  apply same_for_user_except_symmetry; eauto.
  all: eauto.
Qed.

Lemma test_bit_same_count_trues_up_to_eq:
forall n bm1 bm2,
(forall i, i < n -> test_bit i bm1 = test_bit i bm2) ->
count_trues_up_to n bm1 = count_trues_up_to n bm2.
Proof.
  induction n; simpl; intros; eauto.
  erewrite H, IHn; simpl; eauto.
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

Lemma free_block_exists_inode:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
(value_to_bits
        (s1 Inode.InodeAllocatorParams.bitmap_addr)) <
        Inode.InodeAllocatorParams.num_of_blocks ->
(get_first_zero_index
(value_to_bits
            (s2 Inode.InodeAllocatorParams.bitmap_addr))) <
            Inode.InodeAllocatorParams.num_of_blocks.
Proof.
  intros.
  eapply get_first_zero_index_count_trues.
  eapply get_first_zero_index_count_trues in H2.
  erewrite test_bit_same_count_trues_up_to_eq in H2; eauto.
  intros.
  unfold same_for_user_except, files_inner_rep, file_map_rep  in *; cleanup.
  eapply inode_allocations_are_same; eauto.

  eapply addrs_match_exactly_trans; eauto.
  eapply addrs_match_exactly_trans; eauto.
  eapply addrs_match_exactly_sym; eauto.
  eapply addrs_match_exactly_sym; eauto.
Qed.

Lemma free_block_exists_iff_inode:
forall fm1 fm2 s1 s2 u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 s1 ->
files_inner_rep fm2 s2 ->
get_first_zero_index
  (value_to_bits
        (s1 Inode.InodeAllocatorParams.bitmap_addr)) <
        Inode.InodeAllocatorParams.num_of_blocks <->
(get_first_zero_index
      (value_to_bits
            (s2 Inode.InodeAllocatorParams.bitmap_addr))) <
            Inode.InodeAllocatorParams.num_of_blocks.
Proof. 
  intros; split.
  eapply free_block_exists_inode; eauto.
  eapply free_block_exists_inode.
  apply same_for_user_except_symmetry; eauto.
  all: eauto.
Qed.