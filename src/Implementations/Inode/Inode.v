Require Import Framework FSParameters TransactionalDiskLayer BlockAllocator.
Require Import FunctionalExtensionality Lia.
Import IfNotations.

(*** Definitions ***)
Definition Inum := addr.

Record Inode :=
  {
    owner: user;
    block_numbers : list addr;
  }.

Variable encode_inode : Inode -> value.
Variable decode_inode: value -> Inode.
Axiom inode_encode_decode:
  forall i,
    decode_inode (encode_inode i) = i.
Axiom inode_decode_encode:
  forall b,
    encode_inode (decode_inode b) = b.
  
Module InodeAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := inode_blocks_start.
  Definition num_of_blocks := inode_count.
  Definition num_of_blocks_in_bounds := inode_count_in_bounds.
  Definition blocks_fit_in_disk := inodes_fit_in_disk.
End InodeAllocatorParams.

Module InodeAllocator := BlockAllocator InodeAllocatorParams.

Export InodeAllocator.


(*** Rep Invariants ***)
Definition free_block_number (inode_map: disk Inode) bn :=
  forall i inode, inode_map i = Some inode -> ~ In bn inode.(block_numbers).

Definition inode_valid inode :=
  NoDup inode.(block_numbers) /\
  Forall (fun bn => bn < data_length) inode.(block_numbers).

Definition inode_map_valid (inode_map: disk Inode) :=
  (forall i inode_i, inode_map i = Some inode_i -> inode_valid inode_i) /\
  (forall i j inode_i inode_j,
     i <> j ->
     inode_map i = Some inode_i ->
     inode_map j = Some inode_j ->
     NoDup (inode_i.(block_numbers) ++ inode_j.(block_numbers))).
  
Definition inode_map_rep inode_block_map (inode_map: disk Inode) :=
  (forall i, inode_map i = option_map decode_inode (inode_block_map i)) /\
       inode_map_valid inode_map.

Definition inode_rep (inode_map: disk Inode) (d: @total_mem addr addr_dec value):=
  exists inode_block_map,
    block_allocator_rep inode_block_map d /\
    inode_map_rep inode_block_map inode_map.


(*** Functions ***)
Local Definition get_inode inum :=
  r <- read inum;
  if r is Some i then
    Ret (Some (decode_inode i))
  else
    Ret None.

Local Definition set_inode inum inode:= write inum (encode_inode inode).

Definition alloc user := alloc (encode_inode (Build_Inode user [])).

Definition free inum := free inum.

Definition extend inum block_num :=
  r <- get_inode inum;
  if r is Some inode then
    set_inode inum (Build_Inode inode.(owner) (inode.(block_numbers)++[block_num]))
  else
    Ret None.

Definition change_owner inum user :=
  r <- get_inode inum;
  if r is Some inode then
    set_inode inum (Build_Inode user inode.(block_numbers))
  else
    Ret None.

Definition get_block_number inum off:=
  r <- get_inode inum;
  if r is Some inode then
    Ret (nth_error inode.(block_numbers) off)
  else
    Ret None.

Definition get_all_block_numbers inum :=
  r <- get_inode inum;
  if r is Some inode then
    Ret (Some inode.(block_numbers))
  else
    Ret None.

Definition get_owner inum :=
  r <- get_inode inum;
  if r is Some inode then
    Ret (Some inode.(owner))
  else
    Ret None.


(*** Lemmas ***)
Theorem inode_rep_eq:
  forall im1 im2 d,
    inode_rep im1 d ->
    inode_rep im2 d ->
    im1 = im2.
Proof.
  unfold inode_rep; intros; extensionality inum.
  cleanup.
  eapply block_allocator_rep_eq in H; eauto; subst.
  unfold inode_map_rep in *; cleanup.
  rewrite H2, H; eauto.
Qed.

Lemma nth_error_some_lt:
  forall T (l: list T) n t,
    nth_error l n = Some t ->
    n < length l.
Proof.
  induction l; simpl; intros; eauto;
  destruct n; simpl in *; cleanup.
  lia.
  apply IHl in H; lia.
Qed.

(*** Specs ***)
Theorem alloc_finished:
  forall dh u o s user t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (alloc user) (Finished s' t) ->
    ((exists a, t = Some a /\
          dh a = None /\
          inode_rep (Mem.upd dh a (Build_Inode user [])) (fst s')) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
     snd s' = snd s.
Proof.
  unfold alloc, inode_rep; intros; cleanup.
  eapply alloc_finished in H0; eauto.
  cleanup; split_ors; cleanup; eauto;
  split; eauto.
  {
    left; eexists; intuition eauto.
    {
      unfold inode_map_rep in *; cleanup.
      rewrite H0, H4; simpl; eauto.
    }
    {
      eexists; intuition eauto.
      unfold inode_map_rep in *; cleanup.
      split; eauto.
      {
        intros.
        destruct (addr_dec x0 i); subst.
        - repeat rewrite Mem.upd_eq; simpl; eauto.
          rewrite inode_encode_decode; eauto.
        - repeat rewrite Mem.upd_ne; simpl; eauto.
      }
      {
        unfold inode_map_valid in *; cleanup.
        split; intros.
        {
          destruct (addr_dec x0 i); subst.
          - rewrite Mem.upd_eq in H7; simpl; eauto.
            cleanup.
            unfold inode_valid; simpl; eauto.
            split; constructor.
          - rewrite Mem.upd_ne in H7; simpl; eauto.
        }
        {
          destruct (addr_dec x0 i); subst.
          - rewrite Mem.upd_eq in H8; simpl; eauto.
            cleanup; simpl.
            rewrite Mem.upd_ne in H9; simpl; eauto.
            apply H1 in H9.
            unfold inode_valid in *;
            cleanup; eauto.
            
          - rewrite Mem.upd_ne in H8; simpl; eauto.
            destruct (addr_dec x0 j); subst.
            rewrite Mem.upd_eq in H9; simpl; eauto.
            cleanup; simpl.
            rewrite app_nil_r.
            apply H1 in H8.
            unfold inode_valid in *;
            cleanup; eauto.
            rewrite Mem.upd_ne in H9; simpl; eauto.
        }
      }
    }
  }
Qed.

Theorem free_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (free inum) (Finished s' t) ->
    ((t = Some tt /\ inode_rep (Mem.delete dh inum) (fst s')) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
     snd s' = snd s.
Proof.
  unfold free, inode_rep; intros; cleanup.
  eapply free_finished in H0; eauto.
  cleanup; split_ors; cleanup; eauto;
  split; eauto.
  {
    left; split; eauto.
    eexists; intuition eauto.
    {
      unfold inode_map_rep in *; cleanup.
      split; intros.
      {
        destruct (addr_dec inum i); subst.
        repeat rewrite delete_eq; simpl; eauto.
        repeat rewrite delete_ne; simpl; eauto.
      }
      {
        unfold inode_map_valid in *; cleanup.
        split; intros.
        {
          destruct (addr_dec inum i); subst.
          - rewrite Mem.delete_eq in H6; simpl; eauto; congruence.
          - rewrite Mem.delete_ne in H6; simpl; eauto.
        }
        {
          destruct (addr_dec inum i); subst.
          - rewrite Mem.delete_eq in H7; simpl; eauto; congruence.
            
          - rewrite Mem.delete_ne in H7; simpl; eauto.
            destruct (addr_dec inum j); subst.
            rewrite Mem.delete_eq in H8; simpl; eauto; congruence.
            rewrite Mem.delete_ne in H8; simpl; eauto.
        }
      }
    }
  }  
Qed.



Theorem get_inode_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_inode inum) (Finished s' t) ->
    ((exists inode, t = Some inode /\ dh inum = Some inode) \/
     (t = None /\ dh inum = None)) /\
    inode_rep dh (fst s') /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold get_inode, inode_rep; intros; cleanup.
  repeat invert_exec;
  eapply read_finished in H0; eauto;
  cleanup; split_ors; cleanup; eauto;
  split; eauto.
  {
    unfold inode_map_rep in *; cleanup.
    left; rewrite H0; cleanup; simpl; eauto.
  }
  {
    unfold inode_map_rep in *; cleanup.
    right; split; eauto.
    rewrite H0, H5; simpl; eauto.
  }    
Qed.


Theorem set_inode_finished:
  forall dh u o s inum inode t s',
    inode_rep dh (fst s) ->
    inode_valid inode ->
    (forall i inode_i,
     i <> inum ->
     dh i = Some inode_i ->
     NoDup (inode.(block_numbers) ++ inode_i.(block_numbers))) ->
    exec (TransactionalDiskLang data_length) u o s (set_inode inum inode) (Finished s' t) ->
    ((t = Some tt /\ inode_rep (Mem.upd dh inum inode) (fst s')) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold set_inode, inode_rep; intros; cleanup.
  repeat invert_exec;
  eapply write_finished in H2; eauto;
  cleanup; split_ors; cleanup; eauto;
  split; eauto.
  {
    unfold inode_map_rep in *; cleanup.
    left; split; eauto.
    intuition eauto.
    eexists; intuition eauto.
     {
        intros.
        destruct (addr_dec inum i); subst.
        - repeat rewrite Mem.upd_eq; simpl; eauto.
          rewrite inode_encode_decode; eauto.
        - repeat rewrite Mem.upd_ne; simpl; eauto.
      }
      {
        unfold inode_map_valid in *; cleanup.
        split; intros.
        {
          destruct (addr_dec inum i); subst.
          - rewrite Mem.upd_eq in H8; simpl; eauto.
            cleanup.
            unfold inode_valid; simpl; eauto.
          - rewrite Mem.upd_ne in H8; simpl; eauto.
        }
        {
          destruct (addr_dec inum i); subst.
          - rewrite Mem.upd_eq in H9; simpl; eauto.
            cleanup; simpl.
            rewrite Mem.upd_ne in H10; simpl; eauto.
            
          - rewrite Mem.upd_ne in H9; simpl; eauto.
            destruct (addr_dec inum j); subst.
            rewrite Mem.upd_eq in H10; simpl; eauto.
            cleanup; simpl.
            apply NoDup_app_comm; eauto.
            rewrite Mem.upd_ne in H10; simpl; eauto.
        }
      }
  }
Qed.

Theorem extend_finished:
  forall dh u o s inum block_num t s',
    inode_rep dh (fst s) ->
    (forall i inode_i,
     dh i = Some inode_i ->
     ~In block_num inode_i.(block_numbers)) ->
    block_num < data_length ->
    exec (TransactionalDiskLang data_length) u o s (extend inum block_num) (Finished s' t) ->
    ((exists inode,
        t = Some tt /\
        dh inum = Some inode /\
        (inode_rep (Mem.upd dh inum (Build_Inode inode.(owner) (inode.(block_numbers) ++ [block_num]))) (fst s'))) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold extend; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H2; eauto;
  cleanup; eauto.
  split_ors; cleanup;
  eapply set_inode_finished in H3; simpl; eauto; cleanup.
  split_ors; cleanup;
  repeat (split; eauto).
  {
    intros.
    rewrite H3; eauto.    
  }
  {
    intros.
    rewrite H3; eauto.    
  }
  {
    unfold inode_valid; simpl.
    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup.
    eapply_fresh H11 in H7;
    unfold inode_valid in Hx; cleanup; eauto.    
    split; eauto.
    - apply NoDup_app_comm; simpl.
      constructor; eauto.
    - apply Forall_app; eauto.
  }
  {
    intros.
    apply NoDup_app_comm.
    rewrite app_assoc.
    apply NoDup_app_comm.
    simpl; constructor; eauto.
    intros Hx.
    apply in_app_iff in Hx; split_ors;
    solve [eapply H0; [| eauto]; eauto ].

    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup; eauto.
  }
Qed.


Theorem change_owner_finished:
  forall dh u o s inum new_owner t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (change_owner inum  new_owner) (Finished s' t) ->
    ((exists inode,
        t = Some tt /\
        dh inum = Some inode /\
        (inode_rep (Mem.upd dh inum (Build_Inode new_owner inode.(block_numbers))) (fst s'))) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold change_owner; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto.
  split_ors; cleanup;
  eapply set_inode_finished in H1; simpl; eauto; cleanup.
  split_ors; cleanup;
  repeat (split; eauto).
  { intros; rewrite H1; eauto. }
  { intros; rewrite H1; eauto. }
  {
    unfold inode_valid; simpl.
    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup.
    eapply_fresh H9 in H5;
    unfold inode_valid in Hx; cleanup; eauto.
  }
  {
    intros.
    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup; eauto.
  }
Qed.

Theorem get_block_number_finished:
  forall dh u o s inum off t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_block_number inum off) (Finished s' t) ->
    ((exists inode, off < length (inode.(block_numbers)) /\
               t = Some (selN (inode.(block_numbers)) off 0) /\ dh inum = Some inode) \/
     (t = None /\ (dh inum = None \/
                  (exists inode, dh inum = Some inode /\ off >= length (inode.(block_numbers)))))) /\
    inode_rep dh (fst s') /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold get_block_number; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto;
  split; eauto;
  split_ors; cleanup.
  {    
    destruct_fresh (nth_error (block_numbers x0) off); eauto.  
    {
      left; eexists; split; eauto.
      eapply nth_error_some_lt; eauto.
      rewrite nth_selN_eq.
      erewrite nth_error_nth; eauto.
    }
    {
      right; intuition eauto.
      right; eexists; split; eauto.
      apply nth_error_None; eauto.
    }
  }
  right; intuition eauto.  
Qed.

Theorem get_all_block_numbers_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_all_block_numbers inum) (Finished s' t) ->
    ((exists inode, t = Some (inode.(block_numbers)) /\ dh inum = Some inode) \/ t = None) /\
    inode_rep dh (fst s') /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold get_all_block_numbers; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto;
  split; eauto.
  split_ors; cleanup; eauto.
Qed.

Theorem get_owner_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_owner inum) (Finished s' t) ->
    ((exists inode, t = Some inode.(owner) /\ dh inum = Some inode) \/
     (t = None /\ dh inum = None)) /\
    inode_rep dh (fst s') /\
    (forall a, a < InodeAllocatorParams.bitmap_addr \/
          a > InodeAllocatorParams.bitmap_addr + InodeAllocatorParams.num_of_blocks ->
          fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold get_owner; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto;
  split; eauto.
  split_ors; cleanup; eauto.
  split_ors; cleanup; intuition eauto.
Qed.

Global Opaque alloc free extend change_owner get_block_number get_all_block_numbers get_owner.

