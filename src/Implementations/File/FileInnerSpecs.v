Require Import Framework FSParameters AuthenticatedDiskLayer.
Require Import BlockAllocator Inode File.
Require Import Compare_dec FunctionalExtensionality Lia.
Import IfNotations.


(*** Lemmas ***)

Ltac solve_bounds:=
  match goal with
  |[H: forall _: nat , _ -> ?x _ = _ |- ?x _ = _ ] =>
   pose proof inodes_before_data;
   rewrite H;
   unfold DiskAllocatorParams.bitmap_addr,
   DiskAllocatorParams.num_of_blocks,
   InodeAllocatorParams.bitmap_addr,
   InodeAllocatorParams.num_of_blocks in *;
   try lia; eauto
  end.


Set Nested Proofs Allowed.
Lemma inode_rep_some_inbounds:
forall im s inum inode,
inode_rep im s ->
im inum = Some inode ->
inum < inode_count.
Proof.
unfold inode_rep, block_allocator_rep,
inode_map_rep, inode_map_valid,
InodeAllocatorParams.num_of_blocks; intros; cleanup.
destruct (lt_dec inum inode_count); eauto.
rewrite H1, H6 in H0; 
simpl in *; try congruence; try lia.
Qed.

Lemma inode_exists_then_file_exists:
  forall fm im s inum inode,
  file_map_rep fm im s ->
  im inum = Some inode ->
  exists f, fm inum = Some f.
Proof.
  unfold file_map_rep; intros; cleanup.
  destruct_fresh (fm inum); eauto.
  edestruct H; exfalso.
  apply H3; eauto; congruence.
Qed.

Lemma inode_missing_then_file_missing:
  forall fm im s inum,
  file_map_rep fm im s ->
  im inum = None ->
  fm inum = None.
Proof.
  unfold file_map_rep, addrs_match_exactly; intros; cleanup.
  destruct_fresh (fm inum); eauto.
  edestruct H; exfalso.
  eapply H2; eauto; congruence.
Qed.

Lemma Some_injective:
  forall A (a1 a2: A),
    Some a1 = Some a2 ->
    a1 = a2.
Proof.
  intros; congruence.
Qed.

Lemma nth_error_updn_eq:
  forall T (l: list T) n m v,
    n = m ->
    n < length l ->
    nth_error (updn l n v) m = Some v.
Proof.
  induction l; simpl; intros; eauto.
  lia.
  destruct n; simpl in *; 
  cleanup; simpl in *; eauto.
  rewrite IHl; eauto; lia.
Qed.

Lemma nth_error_updn_ne:
  forall T (l: list T) n m v,
    n <> m \/ n >= length l ->
    nth_error (updn l n v) m = nth_error l m.
Proof.
  induction l; simpl; intros; eauto.
  destruct n; simpl in *;
  cleanup; simpl in *; eauto.
  split_ors; cleanup; try lia.
  destruct m; simpl in *; eauto; lia.
  destruct m; simpl; eauto.
  rewrite IHl; eauto; lia.
Qed.

Lemma seln_not_In_ne:
  forall T (l: list T) a t def,
  ~In t l ->
  a < length l ->
  t <> seln l a def.
  Proof.
  induction l; simpl; intros; eauto.
  lia.
  destruct a0; eauto.
  eapply IHl; eauto; lia.
  Qed.


Lemma NoDup_seln_ne:
  forall T (l: list T) a b def1 def2,
    NoDup l ->
    a < length l ->
    b < length l ->
    a <> b ->
    seln l a def1 <> seln l b def2.
Proof.
  induction l; simpl; intros; eauto.
  lia.
  inversion H; cleanup; clear H.
  destruct a0, b; simpl in *;
  cleanup; simpl in *; eauto; try lia.
  eapply seln_not_In_ne; eauto; lia.
  intros Hnot; 
  symmetry in Hnot; 
  eapply seln_not_In_ne; 
  eauto; lia.
  eapply IHl; eauto; lia.
Qed.

Lemma file_map_rep_eq:
  forall fd1 fd2 im s,
    file_map_rep fd1 im s ->
    file_map_rep fd2 im s ->
    fd1 = fd2.
Proof.
  unfold file_map_rep;
  intros; extensionality inum.
  cleanup.
  unfold addrs_match_exactly in *.
  specialize (H inum); specialize (H0 inum);
  destruct_fresh (fd1 inum); cleanup;
  destruct_fresh (im inum).
  {
    destruct_fresh (fd2 inum).
    {
      eapply_fresh H2 in D0; eauto.
      eapply_fresh H1 in D0; eauto.
      unfold file_rep in *; cleanup.
      destruct f, f0; simpl in *; cleanup.
      assert_fresh (blocks = blocks0). {
        eapply list_seln_ext'; eauto.
        intros.
        repeat rewrite nth_seln_eq.
        apply Some_injective.
        repeat rewrite <- nth_error_nth'; try lia.
        destruct_fresh (nth_error (block_numbers i) pos).
        eapply_fresh H5 in D2; eauto; cleanup.
        eapply_fresh H8 in D2; eauto; cleanup; eauto.
        apply nth_error_None in D2; lia.
      }
      rewrite A; eauto.
    }
    {
      edestruct H0; eauto.
      exfalso; eapply H4; congruence.
    }
  }
  {
    edestruct H; eauto.
    exfalso; eapply H3; congruence.
  }
  {
    edestruct H; eauto.
    exfalso; eapply H4; congruence.
  }
  {
    destruct_fresh (fd2 inum); eauto.
    {
      edestruct H0; eauto.
      exfalso; eapply H3; congruence.
    }
  }
  Unshelve.
  exact value0.
Qed.

Lemma files_inner_rep_eq:
  forall fd1 fd2 s,
    files_inner_rep fd1 s ->
    files_inner_rep fd2 s ->
    fd1 = fd2.
Proof.
  unfold files_rep, files_inner_rep;
  intros; extensionality inum.
  cleanup.
  eapply DiskAllocator.block_allocator_rep_eq in H3; eauto; subst.
  eapply inode_rep_eq in H; eauto; subst.
  eapply file_map_rep_eq in H4; subst; eauto.
  rewrite H4; eauto. 
Qed.

Lemma files_rep_eq:
  forall fd1 fd2 s,
    files_rep fd1 s ->
    files_rep fd2 s ->
    fd1 = fd2.
Proof.
  unfold files_rep; intros; cleanup.
  eapply files_inner_rep_eq in H2; eauto.
Qed.

Lemma files_crash_rep_eq:
  forall fd1 fd2 s,
    files_crash_rep fd1 s ->
    files_crash_rep fd2 s ->
    fd1 = fd2.
Proof.
  unfold files_crash_rep; intros; cleanup.
  eapply files_inner_rep_eq in H; eauto.
Qed.



(*** Inner Finished Specs ***)

Lemma free_all_blocks_finished:
  forall u l_a o s s' r block_map,
    DiskAllocator.block_allocator_rep block_map (fst (snd s)) ->
    exec (TDLang data_length) u o s (free_all_blocks l_a) (Finished s' r) ->
    exists new_block_map,
    ((r = None /\
     DiskAllocator.block_allocator_rep new_block_map (fst (snd s'))) \/
    (r = Some tt /\
     DiskAllocator.block_allocator_rep new_block_map (fst (snd s')) /\
     (forall a, In a l_a -> new_block_map a = None))) /\
    (forall a,
       a < DiskAllocatorParams.bitmap_addr \/
       a > DiskAllocatorParams.bitmap_addr + DiskAllocatorParams.num_of_blocks -> 
       fst (snd s') a = fst (snd s) a) /\
    (forall a, ~In a l_a -> new_block_map a = block_map a) /\
    snd (snd s') = snd (snd s).
Proof.
  induction l_a; simpl; intros; eauto.
  invert_exec; eexists; intuition eauto.

  cleanup; repeat invert_exec.
  {
    eapply DiskAllocator.free_finished in H0; eauto.
    cleanup; split_ors; cleanup.
    eapply IHl_a in H1; eauto.
    cleanup; split_ors; cleanup.
    {
      eexists; intuition eauto.
      rewrite H1; eauto.
      rewrite H1; eauto.
      rewrite H5; eauto.
      rewrite Mem.delete_ne; eauto.
    }
    {
      exists x.
      intuition eauto.      
      right; intuition eauto.
      subst.
      destruct (in_dec addr_dec a0 l_a); eauto.
      rewrite H5; eauto.
      rewrite Mem.delete_eq; eauto.
      rewrite H1; eauto.
      rewrite H1; eauto.
      rewrite H5; eauto.
      rewrite Mem.delete_ne; eauto.
    }
  }
  {
    eapply DiskAllocator.free_finished in H0; eauto.
    cleanup; split_ors; cleanup.
    eexists; intuition eauto.
  }
Qed.

Lemma change_owner_inner_finished:
  forall u s s' o t own inum fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (change_owner_inner own inum) (Finished s' t) ->
    (t = None \/
      (exists f, 
      fm inum = Some f /\
      files_inner_rep (Mem.upd fm inum (change_file_owner f own)) (fst (snd s')))) /\
      snd (snd s') = snd (snd s).
Proof.
  unfold change_owner_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  repeat cleanup_pairs.
  eapply Inode.change_owner_finished in H0; eauto.

  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; intuition eauto.

    eapply_fresh inode_exists_then_file_exists in H4; eauto; cleanup.
    unfold file_map_rep in *; cleanup.
    eapply_fresh H6 in H4; eauto.
    unfold file_rep in *; cleanup; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; repeat solve_bounds.
    {
        unfold addrs_match_exactly in *; intros.
        destruct (addr_dec inum a); subst.
        repeat rewrite Mem.upd_eq; eauto.
        split; intros; congruence.
        repeat rewrite Mem.upd_ne; eauto.
    }
    all:
    destruct (addr_dec inum inum0); subst;
    [rewrite Mem.upd_eq in H10;
        rewrite Mem.upd_eq in H11; eauto |
        rewrite Mem.upd_ne in H10;
        rewrite Mem.upd_ne in H11; eauto];
    cleanup; simpl; eauto;
    eapply H6 in H10; eauto; cleanup; eauto.
Qed. 

Lemma delete_inner_finished:
  forall u s s' o t inum fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (delete_inner inum) (Finished s' t) ->
    (t = None \/
      (files_inner_rep (Mem.delete fm inum) (fst (snd s')))) /\
      snd (snd s') = snd (snd s).
Proof.
  unfold delete_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  repeat cleanup_pairs.
  eapply get_all_block_numbers_finished in H0; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; eauto.

  eapply free_all_blocks_finished in H0; eauto.
  2: eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
  intros; repeat solve_bounds.

  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; try solve [intuition eauto].
  unfold inode_rep in *; cleanup.
  eapply free_finished in H1; eauto.
  2: simpl; eexists; intuition eauto;
  eapply InodeAllocator.block_allocator_rep_inbounds_eq; eauto;
  intros; repeat solve_bounds.

  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; intuition eauto.
  {

    eapply_fresh inode_exists_then_file_exists in H6; eauto; cleanup.
    unfold file_map_rep in *; cleanup.
    eapply_fresh H14 in H6; eauto.
    unfold file_rep in *; cleanup; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; repeat solve_bounds. 
          {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.delete_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.delete_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H18;
             rewrite Mem.delete_eq in H19; eauto |
             rewrite Mem.delete_ne in H18;
             rewrite Mem.delete_ne in H19; eauto];
            try congruence.
            eapply_fresh H14 in H18; eauto.
            unfold file_rep in *; cleanup; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H18;
             rewrite Mem.delete_eq in H19; eauto |
             rewrite Mem.delete_ne in H18;
             rewrite Mem.delete_ne in H19; eauto];
            try congruence.
            eapply_fresh H14 in H18; eauto.
            unfold file_rep in *; cleanup; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H18;
             rewrite Mem.delete_eq in H19; eauto |
             rewrite Mem.delete_ne in H18;
             rewrite Mem.delete_ne in H19; eauto];
            try congruence.
            {
              unfold inode_map_rep,
              inode_map_valid in *;
              cleanup.
              eapply H24 in H6; eauto.
              cleanup.
              eapply_fresh H14 in H18; eauto;
              cleanup.
              unfold file_rep; simpl;
              intuition eauto.
              eapply_fresh H25 in H20; cleanup.
              eexists; intuition eauto.
              eapply nth_error_In in H20.
              eapply not_In_NoDup_app in H20; eauto.
              rewrite H8; eauto.
            }
          }
        }
Qed. 

Lemma extend_inner_finished:
  forall u s s' o t inum v fm,
    files_inner_rep fm (fst (snd s)) ->
    
    exec (TDLang data_length) u o s (extend_inner v inum) (Finished s' t) ->
    (t = None \/
      (exists f, 
      fm inum = Some f /\
      files_inner_rep (Mem.upd fm inum (extend_file f v)) (fst (snd s')))) /\
      snd (snd s') = snd (snd s).
Proof.
  unfold extend_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  repeat cleanup_pairs.
  eapply DiskAllocator.alloc_finished in H0; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; eauto.

  unfold inode_rep in *; cleanup.
  eapply Inode.extend_finished in H1; eauto.
  2: simpl; eexists; intuition eauto; 
  eapply InodeAllocator.block_allocator_rep_inbounds_eq; eauto;
  intros; repeat solve_bounds.

  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; intuition eauto.
  {

  eapply_fresh inode_exists_then_file_exists in H10; eauto; cleanup.
    unfold file_map_rep in *; cleanup.
      eapply_fresh H12 in H10; eauto.
      unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; repeat solve_bounds.
          {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.upd_eq in H16;
             rewrite Mem.upd_eq in H17; eauto |
             rewrite Mem.upd_ne in H16;
             rewrite Mem.upd_ne in H17;eauto].
            {
              cleanup; simpl; intuition eauto.
            }
            {
              eapply H12 in H16; eauto; cleanup; eauto.
            }
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.upd_eq in H16;
             rewrite Mem.upd_eq in H17; eauto |
             rewrite Mem.upd_ne in H16;
             rewrite Mem.upd_ne in H17;eauto].
            
            - cleanup; simpl; repeat rewrite app_length; simpl; eauto.
            
            - eapply H12 in H16; eauto; cleanup; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.upd_eq in H16;
           rewrite Mem.upd_eq in H17; eauto |
           rewrite Mem.upd_ne in H16;
           rewrite Mem.upd_ne in H17;eauto].
          {
            cleanup; simpl in *.
              destruct (lt_dec i (length x5.(blocks))).
              - rewrite nth_error_app1 in H18; eauto.
                apply H15 in H18; cleanup.
                eexists; rewrite nth_error_app1; eauto.
                split; eauto.
                rewrite Mem.upd_ne; eauto.
                intros Hnot; subst; congruence.
                lia.
                lia.

              - assert (A: i = length x5.(blocks)). {
                  apply nth_error_some_lt in H18;
                  rewrite app_length in H18; simpl in *;
                  lia.
                }
                subst.
                rewrite nth_error_app2 in *; try lia.
                rewrite H14 in *.
                rewrite PeanoNat.Nat.sub_diag in *; simpl in *.
                cleanup; eexists; intuition eauto.
                rewrite Mem.upd_eq; eauto.
            }
            {
              eapply_fresh H12 in H16; eauto; cleanup.
              unfold file_rep; simpl;
              intuition eauto.
              eapply H21 in H18; cleanup.
              eexists; intuition eauto.
              rewrite Mem.upd_ne; eauto.
              intros Hnot; subst; congruence.
            }
          }
        }
        {
          intros.
          eapply_fresh inode_exists_then_file_exists in H9; 
          eauto; cleanup.
         unfold file_map_rep in *; cleanup.
         eapply_fresh H11 in H9; eauto.
         unfold file_rep in *; cleanup; eauto.
         intros Hnot; apply In_nth_error in Hnot; cleanup.
         apply H14 in H15; cleanup; congruence.
      }
  Qed.


Lemma write_inner_finished:
  forall u s s' o t inum off v fm,
    files_inner_rep fm (fst (snd s)) ->
    
    exec (TDLang data_length) u o s (write_inner off v inum) (Finished s' t) ->
    (t = None \/
      (exists f, 
      t = Some tt /\
      fm inum = Some f /\
      off < length f.(blocks) /\
      files_inner_rep (Mem.upd fm inum (update_file f off v)) (fst (snd s')))) /\
      snd (snd s') = snd (snd s).
Proof.
  unfold write_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  repeat cleanup_pairs.
  eapply get_block_number_finished in H0; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match;
  eapply_fresh DiskAllocator.block_allocator_rep_inbounds_eq with (s2 := t1) in H2.
  all: try solve [intros; repeat solve_bounds].
  {
    eapply DiskAllocator.write_finished in H1; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match; intuition eauto.

  simpl; repeat (split; eauto).  
  eapply_fresh inode_exists_then_file_exists in H7; eauto; cleanup.
  unfold inode_rep in *; cleanup_no_match;
  right; eexists; intuition eauto; cleanup; eauto.
  {
    unfold file_map_rep, file_rep in *; cleanup.
    eapply H11 in H7; eauto; cleanup; lia.
  }
  eexists; intuition eauto.
  eexists; intuition eauto.
  eapply InodeAllocator.block_allocator_rep_inbounds_eq; [eauto | intros; repeat solve_bounds].
  eexists; split; [ |eauto]; eauto.
  unfold file_map_rep in *; cleanup.
  intuition eauto.  
  {
    unfold addrs_match_exactly in *; intros.
    destruct (addr_dec inum a); subst.
    rewrite Mem.upd_eq; eauto.
    split; intros; congruence.
    rewrite Mem.upd_ne; eauto.
  }
  {
    destruct (addr_dec inum inum0); subst;
    [rewrite Mem.upd_eq in H13; eauto |
      rewrite Mem.upd_ne in H13; eauto].
    {
      cleanup.
      unfold update_file, file_rep in *; simpl in *; cleanup.
      eapply_fresh H11 in H7; eauto; cleanup.
      intuition eauto.
      rewrite updn_length; eauto.
      eapply_fresh H14 in H15; cleanup.

      destruct (addr_dec off i); subst.
      {
        eexists.
        rewrite nth_error_updn_eq,
        Mem.upd_eq; eauto.
        eapply nth_error_nth in H15.
        rewrite nth_seln_eq; eauto.
        rewrite H13.
        eapply nth_error_some_lt; eauto.
      }
      {
        eexists.
        rewrite nth_error_updn_ne,
        Mem.upd_ne; eauto.
        unfold inode_map_rep, inode_map_valid in *; cleanup.
        apply H20 in H7; unfold inode_valid in *; cleanup.
        eapply nth_error_nth in H15; rewrite <- H15.
        rewrite <- nth_seln_eq; eauto.
        eapply NoDup_seln_ne; eauto.
        rewrite <- H13.
        eapply nth_error_some_lt; eauto.
      }
    }
    {
      cleanup.
      unfold update_file, file_rep in *; simpl in *; cleanup.
      eapply_fresh H11 in H12; eauto; cleanup.
      unfold file_rep; intuition eauto.
      eapply_fresh H16 in H17; cleanup.
      eexists; split; eauto.
      rewrite Mem.upd_ne; eauto.

      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H23 in H12; eauto.           
      apply nth_error_In in H17.
      eapply not_In_NoDup_app in H17; eauto.
      intros Hnot.
      eapply seln_not_In_ne; eauto.
    }
  }
  
}
{
  unfold file_map_rep; intuition eauto.
}

Unshelve.
eauto. 
Qed.
  
Lemma read_inner_finished:
  forall u s s' o t inum off fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (read_inner off inum) (Finished s' t) ->
    files_inner_rep fm (fst (snd s'))
    /\ snd (snd s') = snd (snd s).
Proof.
  unfold read_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  repeat cleanup_pairs.
  eapply get_block_number_finished in H0; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match;
  eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t1) in H2.
  
  eapply DiskAllocator.read_finished in H1; eauto.
  simpl in *; cleanup_no_match; split_ors; cleanup_no_match;
  repeat cleanup_pairs; repeat invert_exec_no_match;
  
  unfold inode_rep in *; cleanup_no_match;
  eapply InodeAllocator.block_allocator_rep_inbounds_eq with (s2:= t2) in H1.

  all: intros; repeat solve_bounds.
  all: try solve [
             simpl; repeat (split; eauto);
             try eexists; intuition eauto ].
Qed.

(*** Crash Specs ***)



Lemma auth_then_exec_crashed:
  forall u o s s' inum T (p: Inum -> prog (TDLang data_length) (option T)) fm P,
    files_rep fm s -> 
    exec ADLang u o s (auth_then_exec inum p) (Crashed s') ->
    (forall s s' o, 
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (p inum) (Crashed s') ->
    snd (snd s') = snd (snd s)) ->
    forall fm',
    (forall s s' o t, files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (p inum) (Finished s' t) ->
    (t <> None -> 
    files_inner_rep fm' (fst (snd s')) /\ P) /\ snd (snd s') = snd (snd s)) ->    
    files_crash_rep fm s' \/ 
    (files_crash_rep fm' s' /\ 
    P /\
    exists f, 
    inum < inode_count /\ 
    fm inum = Some f /\ 
    f.(BaseTypes.owner) = u).
Proof.
  unfold auth_then_exec,
  files_rep, files_crash_rep; intros;
  repeat (cleanup; repeat invert_exec; eauto;
          try split_ors);
  unfold files_inner_rep in *; cleanup; eauto;
    repeat cleanup_pairs; simpl in *;
    try eapply get_owner_crashed in H6; eauto;
    try eapply get_owner_finished in H7; eauto;
    try eapply H1 in H10; eauto;
    try eapply H2 in H11; simpl in *; cleanup; eauto;
    repeat cleanup_pairs; simpl in *; eauto;
    try solve [left; eauto];
    try solve [right; eauto];
    try solve[
    eexists; split; eauto;
    eexists; split; eauto;
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; solve_bounds];
    try solve [
    right; edestruct H7; cleanup; 
    try congruence; eexists; repeat (split; eauto); 
    [intuition eauto |];
    split_ors; cleanup;
    eapply_fresh inode_rep_some_inbounds in H10; eauto;
    eapply_fresh inode_exists_then_file_exists in H10; eauto; cleanup;
    unfold file_map_rep, file_rep in *; cleanup;
    eapply H14 in H10; eauto; cleanup; eexists; intuition eauto ].        
    Qed.

Lemma read_inner_crashed:
  forall u s s' o inum off fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (read_inner off inum) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  unfold read_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_crashed in H0; cleanup; eauto.
  }

  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_finished in H1; cleanup; eauto;
    repeat invert_exec; eauto.
    {
      repeat split_ors; cleanup.
      {
        eapply DiskAllocator.read_crashed in H2; eauto;
        repeat cleanup_pairs; eauto.
      }
      {
        eapply DiskAllocator.read_finished in H10; eauto; cleanup_no_match.
        repeat cleanup_pairs; eauto.
        2: {
          clear H3.
          eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
          intros; solve_bounds. 
        }
        cleanup; repeat invert_exec; eauto.
      }
    }
  }
Qed.

Lemma write_inner_crashed:
  forall u s s' o inum off v fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (write_inner off v inum) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  unfold write_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_crashed in H0; cleanup; eauto.
  }

  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_finished in H1; cleanup; eauto;
    repeat invert_exec; eauto.
    {
      repeat split_ors; cleanup.
      {
        eapply DiskAllocator.write_crashed in H2; eauto;
        repeat cleanup_pairs; eauto.
      }
    } 
  }
Qed.


Lemma extend_inner_crashed:
  forall u s s' o inum v fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (extend_inner v inum) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  unfold extend_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply DiskAllocator.alloc_crashed in H0; cleanup; eauto.
  }

  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply DiskAllocator.alloc_finished in H1; cleanup; eauto;
    repeat invert_exec; eauto.
    {
      repeat split_ors; cleanup.
      {
        eapply Inode.extend_crashed in H2; eauto;
        repeat cleanup_pairs; eauto.
        unfold inode_rep in *; cleanup.
        eexists; intuition eauto.
        eapply InodeAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; repeat solve_bounds. 
      }
    } 
  }
Qed.

Lemma free_all_blocks_crashed:
  forall u l_a s s' o block_map,
    DiskAllocator.block_allocator_rep block_map (fst (snd s)) ->
    exec (TDLang data_length) u o s (free_all_blocks l_a) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  induction l_a; simpl; intros; repeat invert_exec_no_match; eauto.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply DiskAllocator.free_crashed in H0; cleanup; eauto.
  }

  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply DiskAllocator.free_finished in H1; cleanup; eauto;
    repeat invert_exec; eauto;
    repeat split_ors; cleanup; eauto.
    repeat cleanup_pairs; eapply IHl_a in H2; eauto.
  }
Qed.

Lemma delete_inner_crashed:
  forall u s s' o inum fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (delete_inner inum) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  unfold delete_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_all_block_numbers_crashed in H0; cleanup; eauto.
  }

  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_all_block_numbers_finished in H1; cleanup; eauto;
    repeat invert_exec; eauto.
    {
      repeat split_ors; cleanup.
      {
        repeat cleanup_pairs.
        eapply free_all_blocks_crashed in H2; eauto;
        repeat cleanup_pairs; eauto.
        clear H3; simpl; eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; repeat solve_bounds.
      }
      repeat cleanup_pairs; simpl in *.
      eapply free_all_blocks_finished in H9; simpl; eauto.
      2: simpl; eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
        intros; repeat solve_bounds.
      simpl in *; cleanup; split_ors; cleanup;
      repeat invert_exec; eauto.
      eapply free_crashed in H10; eauto.
    } 
  }
Qed.

Lemma change_owner_inner_crashed:
  forall u s s' o inum own fm,
    files_inner_rep fm (fst (snd s)) ->
    exec (TDLang data_length) u o s (change_owner_inner own inum) (Crashed s') ->
    snd (snd s') = snd (snd s).
Proof.
  unfold change_owner_inner; intros; repeat invert_exec_no_match.
  unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
  eapply Inode.change_owner_crashed in H0; cleanup; eauto.
Qed.
