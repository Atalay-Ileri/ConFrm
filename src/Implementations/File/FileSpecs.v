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

Lemma Some_injective:
  forall A (a1 a2: A),
    Some a1 = Some a2 ->
    a1 = a2.
Proof.
  intros; congruence.
Qed.

Lemma nth_error_updN_eq:
  forall T (l: list T) n m v,
    n = m ->
    n < length l ->
    nth_error (updN l n v) m = Some v.
Proof.
  induction l; simpl; intros; eauto.
  lia.
  destruct n; simpl in *; 
  cleanup; simpl in *; eauto.
  rewrite IHl; eauto; lia.
Qed.

Lemma nth_error_updN_ne:
  forall T (l: list T) n m v,
    n <> m \/ n >= length l ->
    nth_error (updN l n v) m = nth_error l m.
Proof.
  induction l; simpl; intros; eauto.
  destruct n; simpl in *;
  cleanup; simpl in *; eauto.
  split_ors; cleanup; try lia.
  destruct m; simpl in *; eauto; lia.
  destruct m; simpl; eauto.
  rewrite IHl; eauto; lia.
Qed.

Lemma selN_not_In_ne:
  forall T (l: list T) a t def,
  ~In t l ->
  a < length l ->
  t <> selN l a def.
  Proof.
  induction l; simpl; intros; eauto.
  lia.
  destruct a0; eauto.
  eapply IHl; eauto; lia.
  Qed.


Lemma NoDup_selN_ne:
  forall T (l: list T) a b def1 def2,
    NoDup l ->
    a < length l ->
    b < length l ->
    a <> b ->
    selN l a def1 <> selN l b def2.
Proof.
  induction l; simpl; intros; eauto.
  lia.
  inversion H; cleanup; clear H.
  destruct a0, b; simpl in *;
  cleanup; simpl in *; eauto; try lia.
  eapply selN_not_In_ne; eauto; lia.
  intros Hnot; 
  symmetry in Hnot; 
  eapply selN_not_In_ne; 
  eauto; lia.
  eapply IHl; eauto; lia.
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
  unfold file_map_rep in *; cleanup.
  unfold addrs_match_exactly in *.
  specialize (H inum); specialize (H3 inum);
  destruct_fresh (fd1 inum); cleanup;
  destruct_fresh (x0 inum).
  {
    destruct_fresh (fd2 inum).
    {
      eapply_fresh H2 in D0; eauto.
      eapply_fresh H4 in D0; eauto.
      unfold file_rep in *; cleanup.
      destruct f, f0; simpl in *; cleanup.
      assert_fresh (blocks = blocks0). {
        eapply list_selN_ext'; eauto.
        intros.
        repeat rewrite nth_selN_eq.
        apply Some_injective.
        repeat rewrite <- nth_error_nth'; try lia.
        destruct_fresh (nth_error (block_numbers i) pos).
        eapply_fresh H7 in D2; eauto; cleanup.
        eapply_fresh H10 in D2; eauto; cleanup; eauto.
        apply nth_error_None in D2; lia.
      }
      rewrite A; eauto.
    }
    {
      edestruct H; eauto.
      exfalso; eapply H6; congruence.
    }
  }
  {
    edestruct H3; eauto.
    exfalso; eapply H5; congruence.
  }
  {
    edestruct H3; eauto.
    exfalso; eapply H6; congruence.
  }
  {
    destruct_fresh (fd2 inum); eauto.
    {
      edestruct H; eauto.
      exfalso; eapply H5; congruence.
    }
  }
  Unshelve.
  exact value0.
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

(*** Finish Specs ***)

Lemma init_finished:
  forall u o s s' r,
    exec AuthenticatedDiskLang u o s init (Finished s' r) ->
    files_rep empty_mem s'.
Proof.
  unfold init; intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      exists empty_mem; intuition eauto;
      eexists; intuition eauto.
      { 
        unfold block_allocator_rep.
        do 2 eexists; intuition eauto.
        rewrite upd_ne.
        rewrite upd_eq; eauto.
        rewrite bits_to_value_to_bits.
        simpl.  
        unfold valid_bits; simpl. 
        apply valid_bits'_zeroes.
        pose proof InodeAllocatorParams.num_of_blocks_in_bounds; eauto.
        unfold InodeAllocatorParams.bitmap_addr, DiskAllocatorParams.bitmap_addr.
        pose proof inodes_before_data; lia.
        rewrite map_length, seq_length; eauto.
      }
      {
        unfold empty_mem, inode_map_rep, 
        inode_map_valid; 
        intuition congruence.
      }
      {
        unfold DiskAllocator.block_allocator_rep.
        do 2 eexists; intuition eauto.
        rewrite upd_eq; eauto.
        rewrite bits_to_value_to_bits.
        simpl.  
        unfold DiskAllocator.valid_bits; simpl. 
        apply DiskAllocator.valid_bits'_zeroes.
        pose proof DiskAllocatorParams.num_of_blocks_in_bounds; eauto.
        rewrite map_length, seq_length; eauto.
      }
      {
        unfold empty_mem, file_map_rep, addrs_match_exactly;
        intuition congruence.
      }
    }
  }
Qed.

Lemma read_finished:
  forall u o s s' r inum off fd,
    files_rep fd s ->
    exec AuthenticatedDiskLang u o s (read inum off) (Finished s' r) ->
    files_rep fd s' /\
    ((r = None /\
      (inum >= inode_count \/
       fd inum = None \/
       (exists file,
          fd inum = Some file /\
          file.(BaseTypes.owner) <> u)))\/
     (exists f,
        r = nth_error f.(blocks) off /\
        fd inum = Some f /\
        inum < inode_count /\
        f.(BaseTypes.owner) = u)).
Proof.
  unfold read, auth_then_exec, read_inner;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t1) in H1.    
    eapply DiskAllocator.read_finished in H8; eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply InodeAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H6.
    clear H0 H1 H3 H4 H7 H10.
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      eexists; intuition eauto.
    }
    {
      destruct_fresh (fd inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H1 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        edestruct H4; eauto; cleanup.
        apply nth_error_nth'; eauto.
        rewrite nth_selN_eq in H11;
        erewrite H10 in H11; cleanup; eauto.
        {
          unfold block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H7 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H15 in H5; simpl in *; try congruence; try lia.
        }
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H0; exfalso.
        eapply H3; eauto; congruence.
      }
    }
    all: intros; repeat solve_bounds.
 
  }
  { (** Read Failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.    
    eapply DiskAllocator.read_finished in H8; eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply (InodeAllocator.block_allocator_rep_inbounds_eq x2 t (fst s0)) in H6.
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      eexists; intuition eauto.
    }
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H18 in H5; unfold inode_valid in *.
      cleanup.
      eapply Forall_forall in H15; [| apply in_selN; eauto].
      unfold file_map_rep in *; cleanup.
      destruct_fresh (fd inum).
      eapply_fresh f in H5; eauto.
      unfold file_rep in *; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply_fresh (DiskAllocator.valid_bits_extract x1 x7
       (bits (value_to_bits (fst s0 DiskAllocatorParams.bitmap_addr)))
       (selN (block_numbers x) off 0)) in v; eauto.
      cleanup; try congruence.

      split_ors; cleanup.
      edestruct H17; eauto; cleanup.
      apply nth_error_nth'; eauto.
      rewrite nth_selN_eq in H11; cleanup.
      rewrite H21 in H11; cleanup.

      {
        edestruct H17; eauto; cleanup.
        apply nth_error_nth'; eauto.
        destruct (lt_dec (selN (block_numbers x) off 0)
                         DiskAllocatorParams.num_of_blocks); eauto.
      }
      rewrite bitlist_length.      
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      unfold DiskAllocatorParams.num_of_blocks in *;
      lia.

      - edestruct a.
        exfalso; apply H16; eauto; congruence.
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** off is out-of-bounds **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.  
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      eexists; intuition eauto.
    }
    {
      split_ors; cleanup.
      destruct_fresh (fd inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H2 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
        
        right; eexists; intuition eauto.        
        symmetry; apply nth_error_None; lia.
        
        {
          unfold inode_rep, block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H12 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H16 in H5; simpl in *; try congruence; try lia.
        }
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H; exfalso.
        eapply H10; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** Auth failed **) 
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s0) (fst s0)) in H1.  
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      eexists; intuition eauto.
    }
    {
      destruct_fresh (fd inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H2 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
        
        left; intuition eauto.
        right; right; eexists; intuition eauto.
        congruence.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H; exfalso.
        eapply H7; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** inum doesn't exists **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.  
    repeat (split; eauto).
    {
      unfold files_inner_rep, inode_rep; simpl.
      eexists; intuition eauto.
    }
    left; intuition eauto.
    destruct_fresh (fd inum).
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H6; eauto; congruence.
    }
    intuition.
    all: intros; repeat solve_bounds.
  }
  Unshelve.
  eauto.
Qed.    
     
  

Lemma write_finished:
  forall u o s s' r inum off v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (write inum off v) (Finished s' r) ->
    (r = None /\
     ((inum >= inode_count \/
      fm inum = None \/
      (exists file,
         fm inum = Some file /\
         (file.(BaseTypes.owner) <> u \/ off >= length file.(blocks)))) \/
      (exists f,
         fm inum = Some f /\
         inum < inode_count /\
         f.(BaseTypes.owner) = u /\
         off < length f.(blocks))) /\
     files_rep fm s') \/
    (exists f, r = Some tt /\
          fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          off < length f.(blocks) /\
          files_rep (Mem.upd fm inum (update_file f off v)) s').
Proof.
  unfold write, auth_then_exec, write_inner;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t1) in H1.    
    eapply DiskAllocator.write_finished in H8; eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply InodeAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H6.
    {
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H13 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        {
          unfold block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H11 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H24 in H5; simpl in *; try congruence; try lia.
        }
        lia.
        {
          unfold files_rep, files_inner_rep; simpl.
          split; eauto.
          eexists; intuition eauto.
          unfold inode_rep; eexists; intuition eauto.
          eexists; intuition eauto.
          unfold file_map_rep.
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
            [rewrite Mem.upd_eq in H18; eauto |
             rewrite Mem.upd_ne in H18; eauto].
            cleanup.
            unfold update_file, file_rep; simpl;
            intuition eauto.
            rewrite length_updN; eauto.
            eapply_fresh H16 in H17; cleanup.

            

            destruct (addr_dec off i); subst.
            {
              eexists.
              rewrite nth_error_updN_eq,
              Mem.upd_eq; eauto.
              eapply nth_error_nth in H17.
              rewrite nth_selN_eq; eauto.
              rewrite H15.
              eapply nth_error_some_lt; eauto.
            }
            {
              eexists.
              rewrite nth_error_updN_ne,
              Mem.upd_ne; eauto.
              unfold inode_map_rep, inode_map_valid in *; cleanup.
              apply H24 in H5; unfold inode_valid in *; cleanup.
              eapply nth_error_nth in H17; rewrite <- H17.
              rewrite <- nth_selN_eq; eauto.
              
              

              eapply NoDup_selN_ne; eauto.
              rewrite <- H15.
              eapply nth_error_some_lt; eauto.
            }
            {
              eapply_fresh H13 in H17; eauto; cleanup.
              unfold file_rep; intuition eauto.
              eapply_fresh H21 in H22; cleanup.
              eexists; split; eauto.
              rewrite Mem.upd_ne; eauto.

              unfold inode_map_rep, inode_map_valid in *; cleanup.
              eapply H30 in H5; eauto.           
              apply nth_error_In in H22.
              eapply not_In_NoDup_app in H22; eauto.
              
              intros Hx.
              eapply selN_not_In_ne; eauto.
            }
          }
        }
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H15; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** Write Failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x3 t1 t) in H1.    
    eapply DiskAllocator.write_finished in H8; eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply (InodeAllocator.block_allocator_rep_inbounds_eq x2 t (fst s0)) in H6.
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H17 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H15 in H5; eauto.
        unfold file_rep in Hx0; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H11 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H26 in H5; simpl in *; try congruence; try lia.
        rewrite H19; eauto.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H19; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    all: intros; repeat solve_bounds.
  }
  { (** off is out-of-bounds **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_block_number_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.  
    repeat (split; eauto).
    split_ors; cleanup.
    destruct_fresh (fm inum).
    {
      unfold file_map_rep in *; cleanup.
      eapply_fresh H2 in H5; eauto.
      unfold file_rep in *; cleanup; eauto.

      rewrite <- H10 in H8.
      left; eexists; intuition eauto.
      {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
        eexists; intuition eauto.
        unfold file_map_rep; simpl; eauto.
      }
    }
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H10; eauto; congruence.
    }
    all: intros; repeat solve_bounds.
  }
  { (** Auth failed **) 
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s0) (fst s0)) in H1.  
    repeat (split; eauto).

    destruct_fresh (fm inum).
    {
      unfold file_map_rep in *; cleanup.
      eapply_fresh H2 in H5; eauto.
      unfold file_rep in *; cleanup; eauto.
      
      left; intuition eauto.
      left; intuition eauto.
      right; right; eexists; intuition eauto.
      left; congruence.
      {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
        eexists; intuition eauto.
        unfold file_map_rep; simpl; eauto.
      }
    }
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H7; eauto; congruence.
    }
  
    all: intros; repeat solve_bounds.
  }
  { (** inum doesn't exists **)
  unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.  
    repeat (split; eauto).
    left; intuition eauto.
    destruct_fresh (fm inum).
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H6; eauto; congruence.
    }
    intuition.
    {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
    }
    
    all: intros; repeat solve_bounds.
  }
  Unshelve.
  eauto.
Qed.  


Lemma extend_finished:
  forall u o s s' r inum v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (extend inum v) (Finished s' r) ->
    (r = None /\
     ((inum >= inode_count \/
      fm inum = None \/
      (exists file,
         fm inum = Some file /\
         file.(BaseTypes.owner) <> u)) \/
     (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u)) /\
     files_rep fm s') \/
    (exists f, r = Some tt /\ fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_rep (Mem.upd fm inum (extend_file f v)) s').
Proof.
  unfold extend, auth_then_exec, extend_inner;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= fst s1) in H1.    
    eapply DiskAllocator.alloc_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    unfold inode_rep in *; cleanup.
    eapply block_allocator_rep_inbounds_eq with (s2:= t1) in H.    
    eapply extend_finished in H8; simpl; eauto.
    2: unfold inode_rep; eauto.
    all: eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H11.  
    {
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H8 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        {
          unfold block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H3 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H20 in H5; simpl in *; try congruence; try lia.
        }
        {
          unfold files_rep, files_inner_rep; simpl.
          split; eauto.
          eexists; intuition eauto.
          unfold inode_rep; eexists; intuition eauto.
          eexists; intuition eauto.
          unfold file_map_rep.
          intuition eauto.
          {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.upd_eq in H17;
             rewrite Mem.upd_eq in H18; eauto |
             rewrite Mem.upd_ne in H17;
             rewrite Mem.upd_ne in H18;eauto].
            {
              cleanup.
              unfold update_file, file_rep; simpl;
              intuition eauto.
              repeat rewrite app_length; simpl; eauto.
              destruct (lt_dec i (length f.(blocks))).
              - rewrite nth_error_app1 in H17; eauto.
                apply H16 in H17; cleanup.
                eexists; rewrite nth_error_app1; eauto.
                split; eauto.
                rewrite Mem.upd_ne; eauto.
                intros Hnot; subst; congruence.
                lia.
                lia.
                
              - assert (A: i = length f.(blocks)). {
                  apply nth_error_some_lt in H17;
                  rewrite app_length in H17; simpl in *;
                  lia.
                }
                subst.
                rewrite nth_error_app2 in *; try lia.
                rewrite H15 in *.
                rewrite PeanoNat.Nat.sub_diag in *; simpl in *.
                cleanup; eexists; intuition eauto.
                rewrite Mem.upd_eq; eauto.
            }
            {
              eapply_fresh H8 in H17; eauto; cleanup.
              unfold file_rep; simpl;
              intuition eauto.
              eapply H21 in H22; cleanup.
              eexists; intuition eauto.
              rewrite Mem.upd_ne; eauto.
              intros Hnot; subst; congruence.
            }
          }
        }
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H15; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds. 
    {
      intros.
      destruct_fresh (fm i).
      {
         unfold file_map_rep in *; cleanup.
         eapply_fresh H13 in H12; eauto.
         unfold file_rep in *; cleanup; eauto.
         intros Hnot; apply In_nth_error in Hnot; cleanup.
         apply H16 in H17; cleanup; congruence.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H15; eauto; congruence.
      }      
    }
  }
  { (** Extend Failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x3 (snd s2) (fst s2)) in H1.    
    eapply DiskAllocator.alloc_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    unfold inode_rep in *; cleanup.
    eapply_fresh (block_allocator_rep_inbounds_eq x4 t0 t) in H.    
    eapply extend_finished in H8; simpl; eauto.
    2: unfold inode_rep; eauto.
    all: eauto.
    simpl in *.
    cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq (Mem.upd x3 x v) t (fst s0)) in H11.  
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H15 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H17 in H5; eauto; cleanup.
        unfold file_rep in Hx2; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H7 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H30 in H5; simpl in *; try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H19; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    
    all: intros; repeat solve_bounds.
     {
      intros.
      destruct_fresh (fm i).
      {
         unfold file_map_rep in *; cleanup.
         eapply_fresh H13 in H12; eauto.
         unfold file_rep in *; cleanup; eauto.
         intros Hnot; apply In_nth_error in Hnot; cleanup.
         apply H16 in H17; cleanup; congruence.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H15; eauto; congruence.
      }      
    }    
  }
   { (** Inode.alloc failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 (snd s2) (fst s2)) in H1.    
    eapply DiskAllocator.alloc_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    unfold inode_rep in *; cleanup.
    eapply_fresh (block_allocator_rep_inbounds_eq x3 t0 t) in H.    
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H11 in H5;
      unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H13 in H5; eauto; cleanup.
        unfold file_rep in Hx1; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H7 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H26 in H5; simpl in *; try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H15; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    
    all: intros; repeat solve_bounds.
  }  
  { (** Auth failed **) 
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s0) (fst s0)) in H1.  
    repeat (split; eauto).

    destruct_fresh (fm inum).
    {
      unfold file_map_rep in *; cleanup.
      eapply_fresh H2 in H5; eauto.
      unfold file_rep in *; cleanup; eauto.
      
      left; intuition eauto.
      left; intuition eauto.
      right; right; eexists; intuition eauto.
      congruence.
      {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
        eexists; intuition eauto.
        unfold file_map_rep; simpl; eauto.
      }
    }
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H7; eauto; congruence.
    }
  
    all: intros; repeat solve_bounds.
  }
  { (** inum doesn't exists **)
  unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.  
    repeat (split; eauto).
    left; intuition eauto.
    destruct_fresh (fm inum).
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H6; eauto; congruence.
    }
    intuition.
    {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
    }
    
    all: intros; repeat solve_bounds.
  }
Qed.  


Lemma free_all_blocks_finished:
  forall u l_a o s s' r block_map,
    DiskAllocator.block_allocator_rep block_map (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (free_all_blocks l_a) (Finished s' r) ->
    exists new_block_map,
    ((r = None /\
     DiskAllocator.block_allocator_rep new_block_map (fst s')) \/
    (r = Some tt /\
     DiskAllocator.block_allocator_rep new_block_map (fst s') /\
     (forall a, In a l_a -> new_block_map a = None))) /\
    (forall a,
       a < DiskAllocatorParams.bitmap_addr \/
       a > DiskAllocatorParams.bitmap_addr + DiskAllocatorParams.num_of_blocks -> 
       fst s' a = fst s a) /\
    (forall a, ~In a l_a -> new_block_map a = block_map a) /\
    snd s' = snd s.
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


      
Lemma delete_finished:
  forall u o s s' r inum fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (delete inum) (Finished s' r) ->
    (r = None /\
     ((inum >= inode_count \/
      fm inum = None \/
      (exists file, fm inum = Some file /\ file.(BaseTypes.owner) <> u)) \/
     (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u)) /\
     files_rep fm s') \/
    (exists f, r = Some tt /\ fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_rep (Mem.delete fm inum) s').
Proof.
  unfold delete, auth_then_exec, delete_inner;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_all_block_numbers_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t1) in H1.
    eapply free_all_blocks_finished in H8; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply block_allocator_rep_inbounds_eq with (s2:= fst x8) in H.    
    eapply free_finished in H9; simpl; eauto.
    2: unfold inode_rep; eauto.
    all: eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H11.  
    {
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H9 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        {
          unfold block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H6 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H23 in H5; simpl in *;
          try congruence; try lia.
        }
        {
          unfold files_rep, files_inner_rep; simpl.
          split; eauto.
          eexists; intuition eauto.
          unfold inode_rep; eexists; intuition eauto.
          unfold file_map_rep.
          intuition eauto.
          {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.delete_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.delete_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.delete_eq in H20;
             rewrite Mem.delete_eq in H21; eauto |
             rewrite Mem.delete_ne in H20;
             rewrite Mem.delete_ne in H21; eauto];
            try congruence.
            {
              unfold inode_map_rep,
              inode_map_valid in *;
              cleanup.
              eapply H27 in H5; eauto.
              cleanup.
              eapply_fresh H9 in H20; eauto;
              cleanup.
              unfold file_rep; simpl;
              intuition eauto.
              eapply_fresh H24 in H25; cleanup.
              eexists; intuition eauto.
              eapply nth_error_In in H25.
              eapply not_In_NoDup_app in H25; eauto.
              rewrite H10; eauto.
            }
          }
        }
      }
      {
        unfold file_map_rep,
        addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H18; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** free inode failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_all_block_numbers_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.
    eapply free_all_blocks_finished in H8; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply_fresh (block_allocator_rep_inbounds_eq x3 t (fst x8)) in H.    
    eapply free_finished in H9; simpl; eauto.
    2: unfold inode_rep; eauto.
    all: eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x2 (fst x8) (fst s0)) in H11.
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H21 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H19 in H5; eauto; cleanup.
        unfold file_rep in Hx2; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H14 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H37 in H5; simpl in *;
        try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H23; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    all: intros; repeat solve_bounds.
  }
  { (** free_all_blocks failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_all_block_numbers_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.
    eapply free_all_blocks_finished in H8; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    unfold inode_rep in *; cleanup.
    eapply_fresh (block_allocator_rep_inbounds_eq x3 t (fst s0)) in H.
    {
      left.
      unfold inode_map_rep, inode_map_valid in *; cleanup.
      eapply_fresh H17 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H15 in H5; eauto; cleanup.
        unfold file_rep in Hx1; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H11 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H30 in H5; simpl in *;
        try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H19; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** get_all_block_numbers failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply get_all_block_numbers_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x1 t1 t) in H1.
    {
      left.
      unfold inode_rep, inode_map_rep,
      inode_map_valid in *; cleanup.
      eapply_fresh H14 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H11 in H5; eauto; cleanup.
        unfold file_rep in Hx0; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H13 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H26 in H5; simpl in *;
        try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H16; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }  
    
    all: intros; repeat solve_bounds.
  }  
  { (** Auth failed **) 
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s0) (fst s0)) in H1.  
    repeat (split; eauto).

    destruct_fresh (fm inum).
    {
      unfold file_map_rep in *; cleanup.
      eapply_fresh H2 in H5; eauto.
      unfold file_rep in *; cleanup; eauto.
      
      left; intuition eauto.
      left; intuition eauto.
      right; right; eexists; intuition eauto.
      congruence.
      {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
        eexists; intuition eauto.
        unfold file_map_rep; simpl; eauto.
      }
    }
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H7; eauto; congruence.
    }
  
    all: intros; repeat solve_bounds.
  }
  { (** inum doesn't exists **)
  unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.  
    repeat (split; eauto).
    left; intuition eauto.
    destruct_fresh (fm inum).
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H6; eauto; congruence.
    }
    intuition.
    {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
    }
    
    all: intros; repeat solve_bounds.
  }
Qed.


Lemma change_owner_finished:
  forall u o s s' r inum own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (change_owner inum own) (Finished s' r) ->
    (r = None /\
     ((inum >= inode_count \/
      fm inum = None \/
      (exists file, fm inum = Some file /\ file.(BaseTypes.owner) <> u)) \/
      (exists f,
         fm inum = Some f /\
         inum < inode_count /\
         f.(BaseTypes.owner) = u)) /\
     files_rep fm s') \/
    (exists f,
       r = Some tt /\
       fm inum = Some f /\
       inum < inode_count /\
       f.(BaseTypes.owner) = u /\
       files_rep (Mem.upd fm inum (change_file_owner f own)) s').
Proof.
  unfold change_owner, auth_then_exec, change_owner_inner;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    
    eapply change_owner_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H1.  
    {
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H2 in H5; eauto.
        unfold file_rep in *; cleanup; eauto.
                
        right; eexists; intuition eauto.
        {
          unfold inode_rep, block_allocator_rep,
          inode_map_rep in *; cleanup.
          rewrite H21 in H5; simpl in *.
          unfold InodeAllocatorParams.num_of_blocks in *.
          destruct (lt_dec inum inode_count); eauto.
          rewrite H25 in H5; simpl in *;
          try congruence; try lia.
        }
        {
          unfold files_rep, files_inner_rep; simpl.
          split; eauto.
          eexists; intuition eauto.
          eexists; intuition eauto.
          unfold file_map_rep.
          intuition eauto.
          {
            unfold addrs_match_exactly in *; intros.
            destruct (addr_dec inum a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.
          }
          {
            destruct (addr_dec inum inum0); subst;
            [rewrite Mem.upd_eq in H11;
             rewrite Mem.upd_eq in H12; eauto |
             rewrite Mem.upd_ne in H11;
             rewrite Mem.upd_ne in H12; eauto];
            try congruence.
            {
              unfold inode_rep, inode_map_rep,
              inode_map_valid in *;
              cleanup.
              eapply H2 in H5; eauto.
              cleanup.
              (* 
                 eapply_fresh H9 in H20; eauto;
              cleanup.
               *)
              unfold file_rep; simpl;
              intuition eauto.
            }
            {
              unfold inode_rep, inode_map_rep,
              inode_map_valid in *;
              cleanup.
              eapply H2 in H11; eauto.
            }
          }
        }
      }
      {
        unfold file_map_rep,
        addrs_match_exactly in *; cleanup.
        edestruct H; exfalso.
        eapply H9; eauto; congruence.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** Inode.change_owner failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    
    eapply change_owner_finished in H7; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    repeat cleanup_pairs.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 t1 t) in H1.
    {
      left.
      unfold inode_rep, inode_map_rep,
      inode_map_valid in *; cleanup.
      eapply_fresh H14 in H5; unfold inode_valid in *.
      cleanup.
      repeat split; eauto.
      destruct_fresh (fm inum).
      {
        unfold file_map_rep in *; cleanup.
        eapply_fresh H11 in H5; eauto; cleanup.
        unfold file_rep in Hx0; cleanup.
        right; eexists; intuition eauto.
        unfold block_allocator_rep,
        inode_map_rep in *; cleanup.
        rewrite H10 in H5; simpl in *.
        unfold InodeAllocatorParams.num_of_blocks in *.
        destruct (lt_dec inum inode_count); eauto.
        rewrite H23 in H5; simpl in *;
        try congruence; try lia.
      }
      {
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H2; exfalso.
        eapply H16; eauto; congruence.
      }
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** Auth failed **) 
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s0) (fst s0)) in H1.  
    repeat (split; eauto).

    destruct_fresh (fm inum).
    {
      unfold file_map_rep in *; cleanup.
      eapply_fresh H2 in H5; eauto.
      unfold file_rep in *; cleanup; eauto.
      
      left; intuition eauto.
      left; intuition eauto.
      right; right; eexists; intuition eauto.
      congruence.
      {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
        eexists; intuition eauto.
        unfold file_map_rep; simpl; eauto.
      }
    }
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H7; eauto; congruence.
    }
  
    all: intros; repeat solve_bounds.
  }
  { (** inum doesn't exists **)
  unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply get_owner_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.  
    repeat (split; eauto).
    left; intuition eauto.
    destruct_fresh (fm inum).
    {
      unfold file_map_rep, addrs_match_exactly in *; cleanup.
      edestruct H; exfalso.
      eapply H6; eauto; congruence.
    }
    intuition.
    {
        unfold files_rep, files_inner_rep; simpl;
        eexists; intuition eauto.
    }
    
    all: intros; repeat solve_bounds.
  }
Qed.

Lemma create_finished:
  forall u o s s' r own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (create own) (Finished s' r) ->
    (r = None /\
     files_rep fm s') \/
    (exists inum, r = Some inum /\
             fm inum = None /\
             inum < inode_count /\
             files_rep (Mem.upd fm inum (new_file own)) s').
Proof.
  unfold create;
  intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  { (** Success **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply alloc_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s2:= t) in H1.  
    {      
      right; eexists; intuition eauto.
      {
        destruct_fresh (fm x1); eauto.
        unfold file_map_rep, addrs_match_exactly in *; cleanup.
        edestruct H; exfalso.
        apply H7; eauto; congruence.
      }
      {
        unfold files_rep, files_inner_rep; simpl.
          split; eauto.
          eexists; intuition eauto.
          eexists; intuition eauto.
          unfold file_map_rep.
          intuition eauto.
          {
            unfold file_map_rep,
            addrs_match_exactly in *; intros; cleanup.
            destruct (addr_dec x1 a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.            
          }
          {
            destruct (addr_dec inum x1); subst;
            [rewrite Mem.upd_eq in H;
             rewrite Mem.upd_eq in H7; eauto |
             rewrite Mem.upd_ne in H;
             rewrite Mem.upd_ne in H7; eauto];
            try congruence; cleanup; eauto.
            {
              unfold file_rep; simpl;
              intuition eauto.
              destruct i; simpl in *; congruence.
            }
            {
              unfold file_map_rep in *; cleanup; eauto.
            }
          }
      }
    }
    
    all: intros; repeat solve_bounds.
  }
  { (** Inode.alloc failed **)
    unfold files_rep, files_inner_rep in H; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply alloc_finished in H3; eauto.
    simpl in *; cleanup; split_ors; cleanup.
    eapply_fresh (DiskAllocator.block_allocator_rep_inbounds_eq x0 (snd s1) (fst s1)) in H1.
    {
      left.
      unfold inode_rep, inode_map_rep,
      inode_map_valid in *; cleanup.
      repeat split; eauto.
      simpl; eauto.
      {
        unfold files_inner_rep; simpl;
        eexists; intuition eauto.
        unfold inode_rep, inode_map_rep,
        inode_map_valid; simpl;
        eexists; intuition eauto.
      }
    }
    
    all: intros; repeat solve_bounds.
  }
Qed.


Lemma recover_finished:
  forall u o s s' r fm,
    files_reboot_rep fm s ->
    exec AuthenticatedDiskLang u o s (recover) (Finished s' r) ->
    files_rep fm s'.
Proof.
  unfold recover; intros; simpl.
  repeat invert_exec;
  simpl in *; repeat cleanup_pairs; eauto.
  unfold files_reboot_rep, files_rep; eauto.
Qed.

Lemma write_inner_finished:
  forall u s s' o t inum off v fm,
    files_inner_rep fm (fst s) ->
    
    exec (TransactionalDiskLang data_length) u o s (write_inner off v inum) (Finished s' t) ->
    (t = None \/
      (exists f, 
      fm inum = Some f /\
      files_inner_rep (Mem.upd fm inum (update_file f off v)) (fst s'))) /\
      snd s' = snd s.
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
      rewrite length_updN; eauto.
      eapply_fresh H14 in H15; cleanup.

      destruct (addr_dec off i); subst.
      {
        eexists.
        rewrite nth_error_updN_eq,
        Mem.upd_eq; eauto.
        eapply nth_error_nth in H15.
        rewrite nth_selN_eq; eauto.
        rewrite H13.
        eapply nth_error_some_lt; eauto.
      }
      {
        eexists.
        rewrite nth_error_updN_ne,
        Mem.upd_ne; eauto.
        unfold inode_map_rep, inode_map_valid in *; cleanup.
        apply H20 in H7; unfold inode_valid in *; cleanup.
        eapply nth_error_nth in H15; rewrite <- H15.
        rewrite <- nth_selN_eq; eauto.
        eapply NoDup_selN_ne; eauto.
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
      eapply selN_not_In_ne; eauto.
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
    files_inner_rep fm (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (read_inner off inum) (Finished s' t) ->
    files_inner_rep fm (fst s')
    /\ snd s' = snd s.
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
  forall u o s s' inum T (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) fm,
    files_rep fm s -> 
    exec AuthenticatedDiskLang u o s (auth_then_exec inum p) (Crashed s') ->
    (forall s s' o, 
    files_inner_rep fm (fst s) ->
    files_inner_rep fm (snd s) ->
    exec (TransactionalDiskLang data_length) u o s (p inum) (Crashed s') ->
    files_inner_rep fm (snd s')) ->
    forall fm',
    (forall s s' o t, files_inner_rep fm (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (p inum) (Finished s' t) ->
    ( t <> None -> 
    files_inner_rep fm' (fst s')) /\ snd s' = snd s) ->    
    files_crash_rep fm s' \/ files_crash_rep fm' s'.
Proof.
  unfold auth_then_exec,
  files_rep, files_crash_rep; intros;
  repeat (cleanup; repeat invert_exec; eauto;
          try split_ors);
  unfold files_inner_rep in *; cleanup; eauto;
    repeat cleanup_pairs; simpl in *;
    try eapply get_owner_crashed in H5; eauto;
    try eapply get_owner_finished in H6; eauto;
    try eapply H1 in H9; eauto;
    try eapply H2 in H10; simpl in *; cleanup; eauto;
    repeat cleanup_pairs; simpl in *; eauto;
    try solve [left; eauto];
    try solve [right; eauto];
    try solve[
    eexists; split; eauto;
    eexists; split; eauto;
    eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; solve_bounds];
    try solve [right; apply H6; congruence].
Qed.

Lemma read_inner_crashed:
  forall u s s' o inum off fm,
    files_inner_rep fm (fst s) ->
    files_inner_rep fm (snd s) ->
    exec (TransactionalDiskLang data_length) u o s (read_inner off inum) (Crashed s') ->
    files_inner_rep fm (snd s').
Proof.
  unfold read_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_crashed in H1; cleanup; eauto.
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
        eapply DiskAllocator.read_finished in H2; eauto; cleanup_no_match.
        repeat cleanup_pairs; eauto.
        2: {
          clear H3.
          eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
          intros; solve_bounds. 
        }
        cleanup; repeat invert_exec; eauto.
      }
    }
    {
      unfold inode_rep in *; cleanup; 
      eexists; split; eauto;
      eexists; split; eauto.
    }
  }
Qed.

Lemma write_inner_crashed:
  forall u s s' o inum off v fm,
    files_inner_rep fm (fst s) ->
    files_inner_rep fm (snd s) ->
    exec (TransactionalDiskLang data_length) u o s (write_inner off v inum) (Crashed s') ->
    files_inner_rep fm (snd s').
Proof.
  unfold write_inner; intros; repeat invert_exec_no_match.
  split_ors; cleanup; repeat invert_exec.
  {
    unfold files_rep, files_inner_rep in *; simpl in *; cleanup_no_match.
    eapply get_block_number_crashed in H1; cleanup; eauto.
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
    {
      unfold inode_rep in *; cleanup; 
      eexists; split; eauto;
      eexists; split; eauto.
    }
  }
Qed.




Lemma read_crashed:
  forall u o s s' inum off fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (read inum off) (Crashed s') ->
    files_crash_rep fm s'.
Proof.
  unfold read; intros; cleanup.
  eapply auth_then_exec_crashed in H0; cleanup; eauto.
  2: {
    intros. 
    eapply read_inner_crashed in H3; eauto.
  }
  2: {
    intros.
    eapply read_inner_finished in H2; eauto.
    cleanup; intuition eauto.
  }
  split_ors; eauto.
Qed.

  

Lemma write_crashed:
  forall u o s s' inum off v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (write inum off v) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          off < length f.(blocks) /\
          files_crash_rep (Mem.upd fm inum (update_file f off v)) s').
Proof.
  unfold write; intros; cleanup.
  destruct_fresh (fm inum);
  eapply auth_then_exec_crashed in H0; cleanup; eauto;
  try solve [ intros; eapply write_inner_crashed; eauto];
  try solve [ intros;
  eapply write_inner_finished in H2; eauto;
  cleanup; split_ors; cleanup; intuition eauto];
  split_ors; intuition eauto.
  right; eexists; intuition eauto.
  XXX
Qed.

Lemma extend_crashed:
  forall u o s s' inum v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (extend inum v) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_crash_rep (Mem.upd fm inum (extend_file f v)) s').
Admitted.

Lemma delete_crashed:
  forall u o s s' inum fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (delete inum) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_crash_rep (Mem.delete fm inum) s').
Admitted.

Lemma create_crashed:
  forall u o s s' own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (create own) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists inum, fm inum = None /\
             inum < inode_count /\
             files_crash_rep (Mem.upd fm inum (new_file own)) s').
Admitted.

Lemma change_owner_crashed:
  forall u o s s' inum own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (change_owner inum own) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f,
       fm inum = Some f /\
       inum < inode_count /\
       f.(BaseTypes.owner) = u /\
       files_crash_rep (Mem.upd fm inum (change_file_owner f own)) s').
Admitted.

Lemma recover_crashed:
  forall u o s s' fm,
    files_reboot_rep fm s ->
    exec AuthenticatedDiskLang u o s (recover) (Crashed s') ->
    files_crash_rep fm s'.
Admitted.



