Require Import Framework FSParameters AuthenticatedDiskLayer.
Require Import BlockAllocator Inode.
Require Import Compare_dec FunctionalExtensionality Lia.
Import IfNotations.

Module DiskAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := file_blocks_start.
  Definition num_of_blocks := file_blocks_count.
  Definition num_of_blocks_in_bounds := file_blocks_count_in_bounds.
  Definition blocks_fit_in_disk := file_blocks_fit_in_disk.
End DiskAllocatorParams.

Module DiskAllocator := BlockAllocator DiskAllocatorParams.

(*** Rep Invariants ***)
Definition file_rep (file: File) (inode: Inode) (file_block_map: disk value) :=
  file.(BaseTypes.owner) = inode.(Inode.owner) /\
  length file.(blocks) = length inode.(block_numbers) /\
  (forall i block_number,
       nth_error inode.(block_numbers) i = Some block_number ->
       exists block,
         nth_error file.(blocks) i = Some block /\
         file_block_map block_number = Some block).

Definition file_map_rep (file_disk: @mem Inum addr_dec File) inode_map file_block_map :=
   addrs_match_exactly file_disk inode_map /\
   (forall inum inode file,
     inode_map inum  = Some inode ->
     file_disk inum = Some file ->
     file_rep file inode file_block_map).

Definition files_inner_rep (file_disk: disk File) (d: @total_mem addr addr_dec value):=
  exists inode_map,
    inode_rep inode_map d /\
    
  exists file_block_map,
    DiskAllocator.block_allocator_rep file_block_map d /\
    file_map_rep file_disk inode_map file_block_map.

Definition files_rep (file_disk: disk File) (d: AuthenticatedDiskLang.(state)) :=
  fst (snd d) = snd (snd d) /\
  files_inner_rep file_disk (fst (snd d)).

Definition files_crash_rep (file_disk: disk File) (d: AuthenticatedDiskLang.(state)) :=
  files_inner_rep file_disk (snd (snd d)).

Definition files_reboot_rep := files_crash_rep.


(*** Functions ***)
Definition auth_then_exec {T} (inum: Inum) (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) :=
  mo <- |ADDP| get_owner inum;
  if mo is Some owner then
    ok <- |ADAO| Auth owner;
    if ok is Some tt then
      r <- |ADDP| p inum;
      if r is Some v then
        _ <- |ADDO| Commit;
        Ret (Some v)
      else
        _ <- |ADDO| Abort;
        Ret None
    else
      _ <- |ADDO| Abort;
      Ret None
  else
    _ <- |ADDO| Abort;
    Ret None.
        
Definition read_inner off inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
    if r is Some v then
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Definition write_inner off v inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    DiskAllocator.write block_number v
  else
    Ret None.

Definition change_owner_inner owner inum :=
  change_owner inum owner.


Fixpoint free_all_blocks block_nums :=
  match block_nums with
  | nil =>
    Ret (Some tt)
  | bn :: block_nums' =>
    ok <- DiskAllocator.free bn;
    if ok is Some tt then
      free_all_blocks block_nums'
    else
      Ret None
end.

Definition delete_inner inum :=
  mbl <- get_all_block_numbers inum;
  if mbl is Some block_numbers then
    ok <- free_all_blocks block_numbers;
    if ok is Some tt then
      free inum
    else
      Ret None
  else
    Ret None.

Definition extend_inner v inum :=
  mbn <- DiskAllocator.alloc v;
  if mbn is Some block_num then
    extend inum block_num
  else
    Ret None.


Definition read inum off := auth_then_exec inum (read_inner off).
Definition write inum off v := auth_then_exec inum (write_inner off v).
Definition extend inum v := auth_then_exec inum (extend_inner v).
Definition change_owner inum owner := auth_then_exec inum (change_owner_inner owner).
Definition delete inum := auth_then_exec inum delete_inner.

Definition create owner :=
  r <- |ADDP| alloc owner;
  if r is Some inum then
     _ <- |ADDO| Commit;
     Ret (Some inum)
  else
    _ <- |ADDO| Abort;
    Ret None.

Definition recover := |ADDO| Recover.

Definition init :=
 |ADDO| Init [(Inode.InodeAllocatorParams.bitmap_addr, bits_to_value zero_bitlist);
             (DiskAllocatorParams.bitmap_addr, bits_to_value zero_bitlist)].

Definition update_file f off v := Build_File f.(BaseTypes.owner) (updN f.(blocks) off v).
Definition extend_file f v := Build_File f.(BaseTypes.owner) (f.(blocks) ++ [v]).
Definition new_file o := Build_File o [].
Definition change_file_owner f o := Build_File o f.(blocks).

(*** Lemmas ***)
Set Nested Proofs Allowed.
Lemma Some_injective:
  forall A (a1 a2: A),
    Some a1 = Some a2 ->
    a1 = a2.
Proof.
  intros; congruence.
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
    {
      intros.
      pose proof inodes_before_data.
      apply H10;
      unfold DiskAllocatorParams.bitmap_addr,
      DiskAllocatorParams.num_of_blocks,
      InodeAllocatorParams.bitmap_addr,
      InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
        destruct (lt_dec (selN (block_numbers x) off 0) DiskAllocatorParams.num_of_blocks); eauto.
        rewrite e7 in H9; cleanup.
        instantiate (1:= 0);
        rewrite <- nth_selN_eq; lia.
      }
      rewrite bitlist_length.      
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      unfold DiskAllocatorParams.num_of_blocks in *;
      lia.

      - edestruct a.
        exfalso; apply H16; eauto; congruence.
    }
    {
      intros.
      pose proof inodes_before_data.
      apply H10;
      unfold DiskAllocatorParams.bitmap_addr,
      DiskAllocatorParams.num_of_blocks,
      InodeAllocatorParams.bitmap_addr,
      InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
  }
  Unshelve.
  eauto.
Qed.    
     
  

Lemma write_finished:
  forall u o s s' r inum off v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (write inum off v) (Finished s' r) ->
    (r = None /\
     (inum >= inode_count \/
      fm inum = None \/
      (exists file,
         fm inum = Some file /\
         file.(BaseTypes.owner) <> u)) /\
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
    {
      intros.
      pose proof inodes_before_data.
      apply H10;
      unfold DiskAllocatorParams.bitmap_addr,
      DiskAllocatorParams.num_of_blocks,
      InodeAllocatorParams.bitmap_addr,
      InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
        destruct (lt_dec (selN (block_numbers x) off 0) DiskAllocatorParams.num_of_blocks); eauto.
        rewrite e7 in H9; cleanup.
        instantiate (1:= 0);
        rewrite <- nth_selN_eq; lia.
      }
      rewrite bitlist_length.      
      pose proof DiskAllocatorParams.num_of_blocks_in_bounds.
      unfold DiskAllocatorParams.num_of_blocks in *;
      lia.

      - edestruct a.
        exfalso; apply H16; eauto; congruence.
    }
    {
      intros.
      pose proof inodes_before_data.
      apply H10;
      unfold DiskAllocatorParams.bitmap_addr,
      DiskAllocatorParams.num_of_blocks,
      InodeAllocatorParams.bitmap_addr,
      InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      rewrite H7. apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
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
    {
      intros.
      pose proof inodes_before_data.
      apply H4.
      all:
        unfold DiskAllocatorParams.bitmap_addr,
        DiskAllocatorParams.num_of_blocks,
        InodeAllocatorParams.bitmap_addr,
        InodeAllocatorParams.num_of_blocks in *;
      try lia.
    }
  }
  Unshelve.
  eauto.
Qed.  



Lemma extend_finished:
  forall u o s s' r inum v fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (extend inum v) (Finished s' r) ->
    (r = None /\
     (inum >= inode_count \/
      fm inum = None \/
      (exists file, fm inum = Some file /\ file.(BaseTypes.owner) <> u)) /\
     files_rep fm s') \/
    (exists f, r = Some tt /\ fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_rep (Mem.upd fm inum (extend_file f v)) s').
Admitted.



Lemma delete_finished:
  forall u o s s' r inum fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (delete inum) (Finished s' r) ->
    (r = None /\
     (inum >= inode_count \/
      fm inum = None \/
      (exists file, fm inum = Some file /\ file.(BaseTypes.owner) <> u)) /\
     files_rep fm s') \/
    (exists f, r = Some tt /\ fm inum = Some f /\
          inum < inode_count /\
          f.(BaseTypes.owner) = u /\
          files_rep (Mem.delete fm inum) s').
Admitted.

Lemma create_finished:
  forall u o s s' r own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (create own) (Finished s' r) ->
    (r = None /\
     (forall inum : nat, inum < inode_count -> fm inum <> None) /\
     files_rep fm s') \/
    (exists inum, r = Some inum /\
             fm inum = None /\
             inum < inode_count /\
             files_rep (Mem.upd fm inum (new_file own)) s').
Admitted.





Lemma change_owner_finished:
  forall u o s s' r inum own fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (change_owner inum own) (Finished s' r) ->
    (r = None /\
     (inum >= inode_count \/
      fm inum = None \/
      (exists file, fm inum = Some file /\ file.(BaseTypes.owner) <> u)) /\
     files_rep fm s') \/
    (exists f,
       r = Some tt /\
       fm inum = Some f /\
       inum < inode_count /\
       f.(BaseTypes.owner) = u /\
       files_rep (Mem.upd fm inum (change_file_owner f own)) s').
Admitted.





Lemma recover_finished:
  forall u o s s' r fm,
    files_reboot_rep fm s ->
    exec AuthenticatedDiskLang u o s (recover) (Finished s' r) ->
    files_rep fm s'.
Admitted.



(*** Crash Specs ***)

Lemma read_crashed:
  forall u o s s' inum off fm,
    files_rep fm s ->
    exec AuthenticatedDiskLang u o s (read inum off) (Crashed s') ->
    files_crash_rep fm s'.
Admitted.

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
Admitted.

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





(*
Set Nested Proofs Allowed.
Local Lemma get_owner_files_rep_ok :
  forall inum t sx F fmap,
    strongest_postcondition
      AuthenticatedDiskLang
      (|ADDP| get_owner inum)
      (fun o s =>
         exists s0 : disk value * disk value,
           ((F * files_rep fmap)%predicate
            (mem_union (fst s0) (snd s0)) /\ 
            fst s0 = empty_mem) /\
           tt = tt /\ snd s = (empty_mem, snd s0)) 
      t sx ->
    exists imap fbmap,
      (exists inode : Inode,
         imap inum = Some inode /\
         t = Some (Inode.owner inode) /\
         (F * DiskAllocator.block_allocator_rep fbmap *
          [[files_inner_rep fmap  imap fbmap ]] * inode_rep imap)%predicate
           (mem_union (fst (snd sx)) (snd (snd sx)))) \/
      t = None /\
      imap inum = None /\
      (F * DiskAllocator.block_allocator_rep fbmap *
       [[files_inner_rep fmap imap fbmap ]] * inode_rep imap)%predicate
        (mem_union (fst (snd sx)) (snd (snd sx))).
Proof.
  intros.
  repeat (apply sp_exists_extract in H; cleanup).
  apply sp_lift2 in H; simpl in H; cleanup.
        
  eapply sp_impl in H.
  apply (sp_exists_extract (disk Inode)) with
      (P:= fun (inode_map: disk Inode) o (sx : state') =>
             (F * inode_rep inode_map *
              (exists* (file_block_map : disk value),
  
              DiskAllocator.block_allocator_rep file_block_map *
              [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
             tt = tt /\ sx = (empty_mem, snd x)) in H; cleanup.

  2: {
    simpl; intros; cleanup.            
    unfold files_rep in H0.
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x0; simpl; eauto.
    intuition eauto.
    pred_apply; cancel.
  }
          
  eapply sp_impl in H.
  apply (sp_exists_extract (disk value)) with
      (P:= fun (file_block_map: disk value) o (sx : state') =>
             (F *
              (inode_rep x0 *
               DiskAllocator.block_allocator_rep file_block_map *
               [[files_inner_rep fmap x0 file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
             tt = tt /\ sx = (empty_mem, snd x)) in H; cleanup.

  2: {
    simpl; intros; cleanup.            
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x1; simpl in *; eauto.
    intuition eauto.
    pred_apply; cancel.
  }
  
  eapply sp_impl in H.
  apply get_owner_ok in H; eauto.

  simpl; intros; cleanup.
  simpl in *.
  instantiate (1:= x0).
  instantiate (1:= x1).
  pred_apply; cancel.
  exact AuthenticationLang.
Qed.  
           

Theorem auth_then_exec_ok:
  forall inum T (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) s' t fmap F (Q: option T -> state  (TransactionalDiskLang data_length) -> Prop),
    
    (forall t' s'',
       strongest_postcondition
         (TransactionalDiskLang data_length) (p inum)
         (fun o s => (F * files_rep fmap)%predicate
                                      (mem_union (fst s) (snd s)) /\
                  exists file, fmap inum = Some file) t' s'' ->
       (t' = None /\ Q t' (empty_mem, snd s'')) \/
       (t' <> None /\ Q t' (empty_mem, mem_union (fst s'') (snd s'')))) -> 
    (strongest_postcondition AuthenticatedDiskLang (auth_then_exec inum p)
     (fun o s => (F * files_rep fmap)%predicate (mem_union (fst (snd s)) (snd (snd s))) /\ (fst (snd s)) = empty_mem) t s' ->
     (exists file, fmap inum = Some file /\ fst s' = file.(owner) /\ fst (snd s') = empty_mem /\ Q t (snd s')) \/
     (fst (snd s') = empty_mem /\ (fmap inum = None \/ (exists file, fmap inum = Some file /\ fst s' <> file.(owner))))).
Proof.
  unfold auth_then_exec; intros.
  apply sp_bind in H0; simpl in *.
  cleanup; simpl in *.
  {(* Valid inum *)
    cleanup; simpl in *.
    { (* Auth success *)
      cleanup; simpl in *.
      cleanup; simpl in *.
      { (* After p *)
        cleanup; simpl in *.
        cleanup; simpl in *.
        { (* p success *)
          cleanup; simpl in *.
          repeat (apply sp_exists_extract in H1; cleanup).
          apply sp_lift2 in H1; simpl in H1.
          apply sp_extract_precondition in H1; cleanup.
          apply get_owner_files_rep_ok in H2.
          repeat (split_ors; cleanup; simpl in * ).
          
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.
          
          left; eexists; intuition eauto.
          specialize H7 with (1:= H2)(2:=D).
          unfold file_rep in *; cleanup; eauto.
          eapply sp_impl in H1; eauto.
          eapply H in H1; simpl in *; eauto.
          split_ors; cleanup; eauto.

          intros; simpl in *; cleanup.
          eapply get_owner_files_rep_ok in H4.
          repeat (split_ors; cleanup; simpl in * ); eauto.

          intuition eauto.
          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x1.
          pred_apply; cancel.
          exists x2.
          pred_apply; cancel.
          all: exact AuthenticationLang.
        }
        { (* p Failed. *)
          cleanup; simpl in *.
          repeat (apply sp_exists_extract in H1; cleanup).
          apply sp_lift2 in H1; simpl in H1.
          apply sp_extract_precondition in H1; cleanup.
          apply get_owner_files_rep_ok in H2.
          repeat (split_ors; cleanup; simpl in * ).
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.
          
          left; eexists; intuition eauto.
          specialize H7 with (1:= H2)(2:=D).
          unfold file_rep in *; cleanup; eauto.
          eapply sp_impl in H1; eauto.
          eapply H in H1; simpl in *; eauto.        
          split_ors; cleanup; intuition eauto.
          
          
          simpl; intros; cleanup.
          apply get_owner_files_rep_ok in H4.
          repeat (split_ors; cleanup; simpl in * ).
          intuition eauto.
          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x1.
          pred_apply; cancel.
          exists x2.
          pred_apply; cancel.
          all: exact AuthenticationLang.
        }
      }
      { (* Auth Fail *)
        simpl in *; cleanup.
        split_ors; cleanup.
        
        apply get_owner_files_rep_ok in H1.
        cleanup.
        repeat (split_ors; cleanup; simpl in * ).
        destruct_lifts; cleanup.
        unfold files_inner_rep in *; cleanup.
        specialize (H4 inum).
        destruct_fresh (fmap inum); intuition eauto.
        
        right; intuition eauto.
        specialize H7 with (1:= H1)(2:=D).
        unfold file_rep in *; cleanup; eauto.
        right; eexists; intuition eauto.
        apply H2; cleanup; eauto.
      }
    }
    { (* Invalid Inum *)
      cleanup; simpl in *.
      
      apply get_owner_files_rep_ok in H1; cleanup.
          
      split_ors; cleanup.
      destruct_lifts; cleanup.
      unfold files_inner_rep in *; cleanup.
      specialize (H4 inum).
      destruct_fresh (fmap inum); intuition eauto.
      
      exfalso; apply H7; intuition eauto; congruence.
    }      
  }
Qed.

Open Scope predicate_scope.
                            
Local Lemma get_block_number_files_rep_ok :
  forall inum t sx x F fmap file off,
    strongest_postcondition (TransactionalDiskLang data_length)
      (get_block_number inum off)
      (fun o s => (F * files_rep fmap)%predicate
                (mem_union (fst s) (snd s)) /\
               fmap inum = Some file /\
               fst s = x) t sx ->
    exists imap fbmap,
      (exists inode : Inode,
         imap inum = Some inode /\
         fmap inum = Some file /\
         t = nth_error inode.(block_numbers) off /\
         (t = None -> off >= length inode.(block_numbers)) /\
         (F * DiskAllocator.block_allocator_rep fbmap *
          [[files_inner_rep fmap  imap fbmap ]] * inode_rep imap)%predicate
          (mem_union (fst sx) (snd sx))) /\
      fst sx = x.
Proof. Admitted. (*
  intros.
        
  eapply sp_impl in H.
  apply (sp_exists_extract (disk Inode)) with
      (P:= fun (inode_map: disk Inode) o (sx : state') =>
             (F * inode_rep inode_map *
              (exists* (file_block_map : disk value),  
              DiskAllocator.block_allocator_rep file_block_map *
              [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\ fmap inum = Some file /\ fst sx = x) in H; cleanup.

  2: {
    simpl; intros; cleanup.            
    unfold files_rep in H0.
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x; simpl; eauto.
    intuition eauto.
    pred_apply; cancel.
  }
          
  eapply sp_impl in H.
  apply (sp_exists_extract (disk value)) with
      (P:= fun (file_block_map: disk value) o (sx : state') =>
             (F *
              (inode_rep x0 *
               DiskAllocator.block_allocator_rep file_block_map *
               [[files_inner_rep fmap x0 file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\ fmap inum = Some file /\ fst sx = x) in H; cleanup.

  2: {
    simpl; intros; cleanup.            
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x; simpl in *; eauto.
    intuition eauto.
    pred_apply; cancel.
  }
  
  apply sp_extract_precondition in H; cleanup.
  destruct_lifts.
  destruct_fresh (x0 inum).
  {
    eapply sp_impl in H.
    apply get_block_number_ok in H; eauto.

    2: {
      simpl; intros; cleanup.
      pred_apply; cancel.
      instantiate (1:= x0); cancel.
    }
    split_ors; cleanup.
    unfold files_inner_rep in *; cleanup.
    specialize H2 with (1:= D)(2:= H1) as Hx.
    unfold file_rep in *; cleanup.
    do 2 eexists; intuition eauto.
    apply nth_error_None; eauto.
    pred_apply; cancel; eauto.
  }    
  {
    unfold files_inner_rep in *; cleanup.
    specialize (H2 inum); cleanup; exfalso; intuition eauto.
    apply H4; congruence.
  }
Qed.
*)
Theorem read_inner_ok:
  forall inum off x s' t fmap F file,
    strongest_postcondition (TransactionalDiskLang data_length) (read_inner off inum)
     (fun o s => (F * files_rep fmap)%predicate (mem_union (fst s) (snd s)) /\ fmap inum = Some file /\ fst s =x) t s' ->
    (t = nth_error file.(blocks) off /\ (F * files_rep fmap)%predicate (mem_union (fst s') (snd s')) /\
    fst s' = x).
Proof. Admitted. (*
  unfold read_inner; simpl; intros.
  repeat (cleanup; simpl in * ).
  {
    apply sp_extract_precondition in H; cleanup.
    apply get_block_number_files_rep_ok in H0; cleanup.
    eapply sp_impl in H.
    2: {
      simpl; intros.
      eapply get_block_number_files_rep_ok; eauto.
      rewrite H1; eauto.
    }
    
    repeat (apply sp_exists_extract in H; cleanup).
    apply sp_extract_precondition in H; cleanup.
    
    
    eapply sp_impl in H.
    eapply DiskAllocator.read_ok in H; cleanup.
    rewrite <- H.
    2: {
      simpl. intros; cleanup.
      pred_apply; cancel.
      instantiate (1:=x6); cancel; eauto.
    }
    destruct_lifts.
    unfold files_inner_rep in *; cleanup.
    specialize H13 with (1:= H5)(2:= H1) as Hx.
    unfold file_rep in *; cleanup.
    erewrite H16; eauto.
    intuition eauto.
    pred_apply; cancel; eauto.
    
    unfold files_rep.         
    exists x5.
    pred_apply; cancel.
    exists x6.
    pred_apply; cancel.
    unfold files_inner_rep in *; intuition eauto.
    eauto.
  }

  {
    apply sp_extract_precondition in H; cleanup.
    apply get_block_number_files_rep_ok in H0; cleanup.
    eapply sp_impl in H.
    2: {
      simpl; intros.
      eapply get_block_number_files_rep_ok; eauto.
      rewrite H1; eauto.
    }
    
    repeat (apply sp_exists_extract in H; cleanup).
    apply sp_extract_precondition in H; cleanup.
    
    
    eapply sp_impl in H.
    eapply DiskAllocator.read_ok in H; cleanup.
    rewrite <- H.
    2: {
      simpl. intros; cleanup.
      pred_apply; cancel.
      instantiate (1:=x5); cancel; eauto.
    }
    destruct_lifts.
    unfold files_inner_rep in *; cleanup.
    specialize H13 with (1:= H5)(2:= H1) as Hx.
    unfold file_rep in *; cleanup.
    erewrite H16; eauto.
    intuition eauto.
    pred_apply; cancel; eauto.
    
    unfold files_rep.         
    exists x4.
    pred_apply; cancel.
    exists x5.
    pred_apply; cancel.
    unfold files_inner_rep in *; intuition eauto.
  }
  {    
    apply get_block_number_files_rep_ok in H; cleanup.
    destruct_lifts.
    unfold files_inner_rep in *; cleanup.
    specialize H5 with (1:= H)(2:= H0) as Hx.
    unfold file_rep in *; cleanup.
    split; [symmetry; apply nth_error_None; rewrite H7; apply H2; eauto|].
    pred_apply; cancel; eauto.
    
    unfold files_rep.         
    exists x.
    pred_apply; cancel.
    exists x0.
    pred_apply; cancel.
    unfold files_inner_rep in *; intuition eauto.
  }
Qed.
*)
Global Opaque read_inner.
          
Theorem read_ok:
  forall inum off s' t fmap F,
    strongest_postcondition AuthenticatedDiskLang (read inum off)
     (fun o s => (F * files_rep fmap)%predicate (snd (snd s)) /\ fst (snd s) = empty_mem) t s' ->
    (exists file, fmap inum = Some file /\
             t = nth_error file.(blocks) off /\
             owner file = fst s' /\
             (F * files_rep fmap)%predicate (snd (snd s')) /\
             (fst (snd s')) = empty_mem) \/
    (t = None /\
     (fmap inum = None \/
      (exists file : File,
         fmap inum = Some file /\ fst s' <> owner file)) /\
     (F * files_rep fmap)%predicate (snd (snd s')) /\
     fst (snd s') = empty_mem).
Proof. Admitted. (*
  unfold read; intros.
  eapply auth_then_exec_ok in H.
  2: {
    simpl; intros.
    apply sp_extract_precondition in H0; cleanup.
    eapply sp_impl in H0.
    eapply read_inner_ok in H0.
    2: simpl; intros; cleanup; eauto.
    
    instantiate (1:= fun t' s'' =>
       exists file, fmap inum = Some file /\
       t' = nth_error (blocks file) off /\
       (F * files_rep fmap)%predicate
                           (mem_union (fst s'') (snd s''))).
    simpl.
    repeat rewrite mem_union_empty_mem.
    destruct t'; intuition eauto.
    right; intuition eauto; congruence.
    left; intuition eauto.
    eexists; intuition eauto.
    admit.
  }
  
  simpl in *.
  split_ors; cleanup.
  left; eexists; intuition eauto.
  right; intuition eauto.
Admitted.
*)

Theorem write_ok:
  forall inum off s' t fmap F v,
    strongest_postcondition AuthenticatedDiskLang (write inum off v)
     (fun o s => (F * files_rep fmap)%predicate (snd (snd s)) /\ fst (snd s) = empty_mem) t s' ->
    (exists file, fmap inum = Some file /\
             t = Some tt /\
             owner file = fst s' /\
             off < length (blocks file) /\
             let new_file := Build_File (owner file) (updN (blocks file) off v) in
             (F * files_rep (upd fmap inum new_file))%predicate (snd (snd s')) /\
             (fst (snd s')) = empty_mem) \/
    (t = None /\
     (fmap inum = None \/
      (exists file : File,
         fmap inum = Some file /\ (fst s' <> owner file \/ off >= length (blocks file)))) /\
     (F * files_rep fmap)%predicate (snd (snd s')) /\
     fst (snd s') = empty_mem).
Proof. Admitted.
*)
