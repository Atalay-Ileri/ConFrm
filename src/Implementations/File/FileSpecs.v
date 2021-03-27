Require Import Framework FSParameters AuthenticatedDiskLayer.
Require Import BlockAllocator Inode File FileInnerSpecs.
Require Import Compare_dec FunctionalExtensionality Lia.
Import IfNotations.

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
        rewrite bits_to_value_to_bits_exact.
        simpl.  
        unfold valid_bits; simpl. 
        apply valid_bits'_zeroes.
        pose proof InodeAllocatorParams.num_of_blocks_in_bounds; eauto.
        unfold zero_bitlist; rewrite repeat_length; eauto.
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
        rewrite bits_to_value_to_bits_exact.
        simpl.  
        unfold DiskAllocator.valid_bits; simpl. 
        apply DiskAllocator.valid_bits'_zeroes.
        pose proof DiskAllocatorParams.num_of_blocks_in_bounds; eauto.
        unfold zero_bitlist; rewrite repeat_length; eauto.
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
        rewrite nth_seln_eq in H11;
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
      eapply Forall_forall in H15; [| apply in_seln; eauto].
      unfold file_map_rep in *; cleanup.
      destruct_fresh (fd inum).
      eapply_fresh f in H5; eauto.
      unfold file_rep in *; cleanup.
      unfold DiskAllocator.block_allocator_rep in *; cleanup.
      eapply_fresh (DiskAllocator.valid_bits_extract x1 x7
       (value_to_bits (fst s0 DiskAllocatorParams.bitmap_addr))
       (seln (block_numbers x) off 0)) in v; eauto.
      cleanup; try congruence.

      split_ors; cleanup.
      edestruct H17; eauto; cleanup.
      apply nth_error_nth'; eauto.
      rewrite nth_seln_eq in H11; cleanup.
      rewrite H21 in H11; cleanup.

      {
        edestruct H17; eauto; cleanup.
        apply nth_error_nth'; eauto.
        destruct (lt_dec (seln (block_numbers x) off 0)
                         DiskAllocatorParams.num_of_blocks); eauto.
      }
      rewrite value_to_bits_length.
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
            rewrite updn_length; eauto.
            eapply_fresh H16 in H17; cleanup.

            

            destruct (addr_dec off i); subst.
            {
              eexists.
              rewrite nth_error_updn_eq,
              Mem.upd_eq; eauto.
              eapply nth_error_nth in H17.
              rewrite nth_seln_eq; eauto.
              rewrite H15.
              eapply nth_error_some_lt; eauto.
            }
            {
              eexists.
              rewrite nth_error_updn_ne,
              Mem.upd_ne; eauto.
              unfold inode_map_rep, inode_map_valid in *; cleanup.
              apply H24 in H5; unfold inode_valid in *; cleanup.
              eapply nth_error_nth in H17; rewrite <- H17.
              rewrite <- nth_seln_eq; eauto.
              
              

              eapply NoDup_seln_ne; eauto.
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
              eapply seln_not_In_ne; eauto.
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



(*** Crash specs ***)

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
    eapply read_inner_crashed in H2; eauto.
  }
  2: {
    intros.
    eapply read_inner_finished in H2; eauto.
    cleanup; intuition eauto.
  }
  split_ors; cleanup; eauto.
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
  try solve [
   intros;
    eapply write_inner_finished in H2; eauto;
    cleanup; split_ors; cleanup; intuition eauto];
  try solve [
      cleanup; split_ors; cleanup; intuition eauto;
    right; eexists; intuition eauto].
  Unshelve.
  all: eauto.
  exact True.
Qed.

Lemma extend_crashed:
  forall u o s s' inum v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (extend inum v) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f, 
    fm inum = Some f /\
    inum < inode_count /\
    f.(BaseTypes.owner) = u /\
    files_crash_rep (Mem.upd fm inum (extend_file f v)) s').
Proof.
  unfold extend; intros; cleanup.
  destruct_fresh (fm inum);
  eapply auth_then_exec_crashed in H0; cleanup; eauto;
  try solve [ intros; eapply extend_inner_crashed; eauto];
  try solve [
    intros;
    eapply extend_inner_finished in H2; eauto;
    cleanup; split_ors; cleanup; intuition eauto];
  try solve [
      cleanup; split_ors; cleanup; intuition eauto;
    right; eexists; intuition eauto].
  Unshelve.
  all: eauto.
  exact True.
Qed.

Lemma delete_crashed:
  forall u o s s' inum fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (delete inum) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists f, fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_crash_rep (Mem.delete fm inum) s').
Proof.
unfold delete; intros; cleanup.
destruct_fresh (fm inum);
eapply auth_then_exec_crashed in H0; cleanup; eauto;
try solve [ intros; eapply delete_inner_crashed; eauto];
try solve [
  intros;
  eapply delete_inner_finished in H2; eauto;
  cleanup; split_ors; cleanup; intuition eauto];
try solve [
    cleanup; split_ors; cleanup; intuition eauto;
  right; eexists; intuition eauto].
Qed.

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
Proof. 
  unfold change_owner; intros; cleanup.
  destruct_fresh (fm inum);
  eapply auth_then_exec_crashed in H0; cleanup; eauto;
  try solve [ intros; eapply change_owner_inner_crashed; eauto];
  try solve [
  intros;
  eapply change_owner_inner_finished in H2; eauto;
  cleanup; split_ors; cleanup; intuition eauto];
  try solve [
    cleanup; split_ors; cleanup; intuition eauto;
  right; eexists; intuition eauto].
  Unshelve.
  eauto.
  exact True.
Qed.


Lemma create_crashed:
  forall u o s s' own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (create own) (Crashed s') ->
    files_crash_rep fm s' \/
    (exists inum, 
    fm inum = None /\
    inum < inode_count /\
    files_crash_rep (Mem.upd fm inum (new_file own)) s').
Proof.
  unfold create, files_rep, files_crash_rep; intros; 
  cleanup; repeat invert_exec_no_match.
  split_ors; cleanup_no_match; repeat invert_exec_no_match.
  {
    eapply alloc_crashed in H3; cleanup; eauto.
  }
  {
    unfold files_inner_rep in *; cleanup_no_match.
    eapply alloc_finished in H4; cleanup_no_match; eauto.
    split_ors; cleanup_no_match; repeat cleanup_pairs;
    repeat invert_exec.
    {
      split_ors; cleanup_no_match; repeat cleanup_pairs;
      repeat invert_exec_no_match; simpl; eauto.
      {
        simpl; left; eauto.
      }
      {
        simpl in *; cleanup.
        right.
        eapply inode_missing_then_file_missing in H8; eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; repeat solve_bounds.
        
        {
          unfold file_map_rep; intuition eauto.
          {
            unfold file_map_rep,
            addrs_match_exactly in *; intros; cleanup.
            destruct (addr_dec x a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.            
          }
          {
            destruct (addr_dec inum x); subst;
            [rewrite Mem.upd_eq in H;
             rewrite Mem.upd_eq in H0; eauto |
             rewrite Mem.upd_ne in H;
             rewrite Mem.upd_ne in H0; eauto];
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
      {
        simpl in *; cleanup.
        right.
        eapply inode_missing_then_file_missing in H8; eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; repeat solve_bounds.
        
        {
          unfold file_map_rep; intuition eauto.
          {
            unfold file_map_rep,
            addrs_match_exactly in *; intros; cleanup.
            destruct (addr_dec x a); subst.
            repeat rewrite Mem.upd_eq; eauto.
            split; intros; congruence.
            repeat rewrite Mem.upd_ne; eauto.            
          }
          {
            destruct (addr_dec inum x); subst;
            [rewrite Mem.upd_eq in H;
             rewrite Mem.upd_eq in H0; eauto |
             rewrite Mem.upd_ne in H;
             rewrite Mem.upd_ne in H0; eauto];
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
  }
  {
    split_ors; cleanup_no_match; repeat cleanup_pairs;
      repeat invert_exec_no_match; simpl; left; eauto.
  }
  }
Qed.

Lemma recover_crashed:
  forall u o s s' fm,
    files_reboot_rep fm s ->
    exec AuthenticatedDiskLang u o s (recover) (Crashed s') ->
    files_crash_rep fm s'.
Proof.
  unfold recover, files_reboot_rep; intros; repeat invert_exec; 
  repeat cleanup_pairs; eauto.
Qed.
