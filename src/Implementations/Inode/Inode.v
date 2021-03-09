Require Import Framework FSParameters TransactionalDiskLayer BlockAllocator.
Require Import FunctionalExtensionality.
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


(*** Specs ***)
Theorem alloc_finished:
  forall dh u o s user t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (alloc user) (Finished s' t) ->
    ((exists a, t = Some a /\
          dh a = None /\
          inode_rep (Mem.upd dh a (Build_Inode user [])) (fst s')) \/
    (t = None /\ inode_rep dh (fst s'))) /\
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
      rewrite H0, H3; simpl; eauto.
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
          - rewrite Mem.upd_eq in H6; simpl; eauto.
            cleanup.
            unfold inode_valid; simpl; eauto.
            split; constructor.
          - rewrite Mem.upd_ne in H6; simpl; eauto.
        }
        {
          destruct (addr_dec x0 i); subst.
          - rewrite Mem.upd_eq in H7; simpl; eauto.
            cleanup; simpl.
            rewrite Mem.upd_ne in H8; simpl; eauto.
            apply H1 in H8.
            unfold inode_valid in *;
            cleanup; eauto.
            
          - rewrite Mem.upd_ne in H7; simpl; eauto.
            destruct (addr_dec x0 j); subst.
            rewrite Mem.upd_eq in H8; simpl; eauto.
            cleanup; simpl.
            rewrite app_nil_r.
            apply H1 in H7.
            unfold inode_valid in *;
            cleanup; eauto.
            rewrite Mem.upd_ne in H8; simpl; eauto.
        }
      }
    }
  }
Qed.

Theorem free_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (free inum) (Finished s' t) ->
    ((t = Some tt /\
      (inode_rep dh (fst s') \/ inode_rep (Mem.delete dh inum) (fst s'))) \/
    (t = None /\ inode_rep dh (fst s'))) /\
     snd s' = snd s.
Proof.
  unfold free, inode_rep; intros; cleanup.
  eapply free_finished in H0; eauto.
  cleanup; split_ors; cleanup; eauto;
  split; eauto.
  {
    left; split; eauto.
    split_ors.
    {
      left; eexists; intuition eauto.
    }
    {
      right; eexists; intuition eauto.
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
             - rewrite Mem.delete_eq in H5; simpl; eauto; congruence.
             - rewrite Mem.delete_ne in H5; simpl; eauto.
           }
           {
             destruct (addr_dec inum i); subst.
             - rewrite Mem.delete_eq in H6; simpl; eauto; congruence.
               
             - rewrite Mem.delete_ne in H6; simpl; eauto.
               destruct (addr_dec inum j); subst.
               rewrite Mem.delete_eq in H7; simpl; eauto; congruence.
               rewrite Mem.delete_ne in H7; simpl; eauto.
           }
         }
      }
    }
  }
Qed.



Theorem get_inode_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_inode inum) (Finished s' t) ->
    ((exists inode, t = Some inode /\ dh inum = Some inode) \/ t = None) /\
    inode_rep dh (fst s') /\
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
    ((t = Some tt /\
      (inode_rep dh (fst s') \/ inode_rep (Mem.upd dh inum inode) (fst s'))) \/
     (t = None /\ inode_rep dh (fst s'))) /\
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
    right; eexists; intuition eauto.
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
          - rewrite Mem.upd_eq in H7; simpl; eauto.
            cleanup.
            unfold inode_valid; simpl; eauto.
          - rewrite Mem.upd_ne in H7; simpl; eauto.
        }
        {
          destruct (addr_dec inum i); subst.
          - rewrite Mem.upd_eq in H8; simpl; eauto.
            cleanup; simpl.
            rewrite Mem.upd_ne in H9; simpl; eauto.
            
          - rewrite Mem.upd_ne in H8; simpl; eauto.
            destruct (addr_dec inum j); subst.
            rewrite Mem.upd_eq in H9; simpl; eauto.
            cleanup; simpl.
            apply NoDup_app_comm; eauto.
            rewrite Mem.upd_ne in H9; simpl; eauto.
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
        (inode_rep dh (fst s') \/
         inode_rep (Mem.upd dh inum (Build_Inode inode.(owner) (inode.(block_numbers) ++ [block_num]))) (fst s'))) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    snd s' = snd s.
Proof.
  unfold extend; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H2; eauto;
  cleanup; eauto.
  split_ors; cleanup;
  eapply set_inode_finished in H3; simpl; eauto; cleanup.
  split_ors; cleanup;
  split; eauto.
  {
    unfold inode_valid; simpl.
    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup.
    eapply_fresh H10 in H6;
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
        (inode_rep dh (fst s') \/
         inode_rep (Mem.upd dh inum (Build_Inode new_owner inode.(block_numbers))) (fst s'))) \/
     (t = None /\ inode_rep dh (fst s'))) /\
    snd s' = snd s.
Proof.
  unfold change_owner; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto.
  split_ors; cleanup;
  eapply set_inode_finished in H1; simpl; eauto; cleanup.
  split_ors; cleanup;
  split; eauto.
  {
    unfold inode_valid; simpl.
    unfold inode_rep, inode_map_rep,
    inode_map_valid in *; cleanup.
    eapply_fresh H8 in H4;
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
    ((exists inode, t = Some (selN (inode.(block_numbers)) off 0) /\ dh inum = Some inode) \/ t = None) /\
    inode_rep dh (fst s') /\
    snd s' = snd s.
Proof.
  unfold get_block_number; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto;
  split; eauto.
  destruct_fresh (nth_error (block_numbers i) off); eauto.
  split_ors; cleanup.
  left; eexists; split; eauto.
  rewrite nth_selN_eq.
  erewrite nth_error_nth; eauto.
Qed.

Theorem get_all_block_numbers_finished:
  forall dh u o s inum t s',
    inode_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (get_all_block_numbers inum) (Finished s' t) ->
    ((exists inode, t = Some (inode.(block_numbers)) /\ dh inum = Some inode) \/ t = None) /\
    inode_rep dh (fst s') /\
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
    ((exists inode, t = Some inode.(owner) /\ dh inum = Some inode) \/ t = None) /\
    inode_rep dh (fst s') /\
    snd s' = snd s.
Proof.
  unfold get_owner; intros; cleanup.
  repeat invert_exec;
  eapply get_inode_finished in H0; eauto;
  cleanup; eauto;
  split; eauto.
  split_ors; cleanup; eauto.
Qed.

(*
Theorem get_inode_ok:
  forall inum s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (get_inode inum)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s))) t s' ->
    (t = imap inum /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold inode_rep; intros; simpl in *; cleanup.
  destruct x; simpl in *; cleanup.
  -    
    eapply sp_impl in H.
    eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]] *
    [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]))%predicate
    (mem_union (fst s) (snd s))) in H.
    cleanup.
    eapply sp_impl in H.
    apply read_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x i)]] * [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]).
      pred_apply' H0; cancel.
    }
    
    cleanup.
    destruct_lift H0.
    rewrite H5; cleanup.
    rewrite <- H; simpl.
    intuition eauto.
    pred_apply; cancel.
    exists x; pred_apply; cancel.

    simpl; intros; cleanup.
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x; eauto.
    
  -
    eapply sp_impl in H.
    eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]] *  [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]))%predicate
    (mem_union (fst s) (snd s))) in H.
    cleanup.
    eapply sp_impl in H.
    apply read_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x i)]] * [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]).
      pred_apply' H0; cancel.
    }
    
    cleanup.
    destruct_lift H0.
    rewrite H5; cleanup.
    rewrite <- H; simpl.
    intuition eauto.
    pred_apply; cancel.
    exists x; pred_apply; cancel.

    simpl; intros; cleanup.
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x; eauto.
Qed.


Theorem set_inode_ok:
  forall inum inode s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (set_inode inum inode)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
                                     compatible_inode imap inum inode /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists i, imap inum = Some i /\ t = Some tt /\ (F * inode_rep (upd imap inum inode))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold inode_rep; intros; simpl in *; cleanup.
  eapply sp_impl in H.
  eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]] * [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]))%predicate
                                                             (mem_union (fst s) (snd s)) /\
                                                                            compatible_inode imap inum inode /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply write_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]] *
     [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]] * [[compatible_inode imap inum inode ]]).
      split; eauto.
      pred_apply' H0; cancel.
    }
    split_ors; cleanup.
    
  -    destruct_lift H1.
    left; eexists; intuition eauto.
    rewrite H6, H; simpl; eauto.
    pred_apply; cancel.
    exists (upd x0 inum (encode_inode inode)).
    pred_apply; cancel.
    destruct (addr_dec inum i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite inode_encode_decode; eauto.

    unfold compatible_inode in *;
    destruct (addr_eq_dec inum i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite upd_eq in H2; eauto; cleanup.
    intuition.
    rewrite upd_ne in H7; eauto.

    rewrite upd_ne in H2; eauto; cleanup.
    specialize H5 with (1:= H2); cleanup.
    intuition.
     destruct (addr_eq_dec inum j); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
     rewrite upd_eq in H9; eauto; cleanup.
     apply NoDup_app_comm;
     eapply H4; eauto.
     rewrite upd_ne in H9; eauto.
    
  - right; intuition cleanup.
    pred_apply; cancel.
    exists x0.
    pred_apply; cancel.
    
 - simpl; intros; cleanup.
   apply pimpl_exists_l_star_r in H0.
   destruct H0.
   exists x0; intuition eauto.
Qed.

Global Opaque get_inode set_inode.

Theorem alloc_ok:
  forall user s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (alloc user)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists inum, t = Some inum /\ imap inum = None /\ (F * inode_rep (upd imap inum (Build_Inode user [])))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
    unfold inode_rep; intros; simpl in *; cleanup.
  eapply sp_impl in H.
  eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]] *
    [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]))%predicate
                                                                          (mem_union (fst s) (snd s)) /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply alloc_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]]  *
    [[forall (i : addr) (inode : Inode),
      imap i = Some inode -> compatible_inode imap i inode]]).
      split; eauto.
      pred_apply' H0; cancel.
    }
    split_ors; cleanup.
    - left; exists x1; intuition cleanup.
      destruct_lifts.
      rewrite H5, H0; simpl; eauto.
    pred_apply; cancel.
    exists (upd x0 x1 (encode_inode (Build_Inode user []))).
    pred_apply; cancel.
    destruct (addr_dec x1 i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite inode_encode_decode; eauto.

    unfold compatible_inode in *;
    destruct (addr_eq_dec x1 i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite upd_eq in H2; eauto; cleanup.
    simpl; intuition eauto.
    constructor.
    rewrite upd_ne in H3; eauto.
    specialize H4 with (1:=H3); cleanup; eauto.

    rewrite upd_ne in H2; eauto; cleanup.
    specialize H4 with (1:= H2); cleanup.
    intuition.
     destruct (addr_eq_dec x1 j); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
     rewrite upd_eq in H7; eauto; cleanup.
     simpl.
     rewrite app_nil_r.
     specialize H4 with (2:= H2); cleanup; eauto.
     rewrite upd_ne in H7; eauto.
    
  - right; intuition cleanup.
    pred_apply; cancel.
    exists x0.
    pred_apply; cancel.

  - simpl; intros; cleanup.
   apply pimpl_exists_l_star_r in H0.
   destruct H0.
   exists x0; eauto.    
Qed.


Theorem free_ok:
  forall inum s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (free inum)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (t = Some tt /\ (F * inode_rep (delete imap inum))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
    unfold inode_rep; intros; simpl in *; cleanup.
  eapply sp_impl in H.
  eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]] *
           [[forall (i : addr) (inode : Inode),
             imap i = Some inode -> compatible_inode imap i inode]]))%predicate
                                                                          (mem_union (fst s) (snd s)) /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply free_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]] *
           [[forall (i : addr) (inode : Inode),
             imap i = Some inode -> compatible_inode imap i inode]]).
      split; eauto.
      pred_apply' H0; cancel.
    }
    
    split_ors; cleanup.
  - left; intuition cleanup.
    pred_apply; cancel.
    exists (delete x0 inum).
    pred_apply; cancel.
    unfold delete.
    destruct (addr_dec i inum); eauto.

    unfold delete, compatible_inode in *;
    destruct (addr_dec i inum); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    cleanup.
    
    specialize H3 with (1:=H1); cleanup; eauto.
    simpl; intuition eauto.
     destruct (addr_dec j inum); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto; cleanup.
    
  - right; intuition cleanup.
    pred_apply; cancel.
    exists x0.
    pred_apply; cancel.

  - simpl; intros; cleanup.
   apply pimpl_exists_l_star_r in H0.
   destruct H0.
   exists x0; eauto.   
Qed.

Theorem extend_ok:
  forall inum block_num s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (extend inum block_num)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\ free_block_number imap block_num /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists inode, imap inum = Some inode /\ t = Some tt /\ (F * inode_rep (upd imap inum (Build_Inode inode.(owner) (inode.(block_numbers)++[block_num]))))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold extend; intros; cleanup.
  apply sp_bind in H.
  simpl in *; cleanup.
  
  eapply sp_impl in H;
  [> eapply get_inode_ok in H; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].
  cleanup.

  apply sp_bind in H0.
  simpl in *; cleanup.
  eapply sp_impl in H2;
  [> eapply set_inode_ok in H2; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].  
  split_ors; cleanup.
  
  + cleanup; left; eexists; intuition eauto.
    cleanup; eauto.
  + right; intuition eauto.
  + simpl; intros.
    eapply sp_impl in H3;
    [> eapply get_inode_ok in H3; eauto
    |].
    instantiate (2:= F * [[forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull]%list ]] *
                     [[ free_block_number imap block_num ]] ) in H3.
    cleanup; destruct_lift H4.
    split; eauto.
    
    unfold inode_rep in *; destruct_lifts.
    apply pimpl_exists_l_star_r in H4.
    destruct H4.
    destruct_lift H4.
    split; unfold compatible_inode in *; simpl.
    unfold free_block_number in *.
    split.
    apply NoDup_app_comm; simpl.
    constructor; eauto.    
    symmetry in H;
    specialize H10 with (1:= H);
    cleanup; eauto.
    
    intros.
    apply NoDup_app_comm.
    rewrite app_assoc.
    apply NoDup_app_comm.
    simpl in *.
    constructor.
    unfold not; intros.
    apply in_app_or in H7; split_ors;    
    try solve [eapply H8; [|eauto]; eauto].
    edestruct H10; eauto.
    
    simpl; intros; eauto.

    simpl; intros; cleanup.
    pred_apply; cancel.
    eapply H6; eauto.
    
  + simpl in *; cleanup.
    eapply sp_impl in H0;
    [> eapply get_inode_ok in H0; eauto
    |try solve [intros; cleanup; simpl; intuition eauto] ].
    cleanup.
    right; intuition.
Qed.


Theorem change_owner_ok:
  forall inum user s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (change_owner inum user)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists inode, imap inum = Some inode /\ t = Some tt /\ (F * inode_rep (upd imap inum (Build_Inode user (inode.(block_numbers)))))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold change_owner; intros; cleanup.
  apply sp_bind in H.
  simpl in *; cleanup.
  
  eapply sp_impl in H;
  [> eapply get_inode_ok in H; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].
  cleanup.

  apply sp_bind in H0.
  simpl in *; cleanup.
  eapply sp_impl in H2;
  [> eapply set_inode_ok in H2; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].  
  split_ors; cleanup.
  
  + cleanup; left; eexists; intuition eauto.
    cleanup; eauto.
  + right; intuition eauto.
  + simpl; intros.
    eapply sp_impl in H3;
    [> eapply get_inode_ok in H3; eauto
    |].
    instantiate (2:= F * [[forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull]%list ]] *
                [[forall (i : addr) (inode : Inode),
             imap i = Some inode -> compatible_inode imap i inode]]) in H3.
    cleanup; destruct_lift H4.
    split; eauto.
    symmetry in H; specialize H8 with (1:= H).
    unfold compatible_inode in *; simpl; cleanup; eauto.

    simpl; intros; eauto.

    simpl; intros; cleanup.
    pred_apply; cancel.
    eapply H5; eauto.

    unfold inode_rep in *; destruct_lifts.
    apply pimpl_exists_l_star_r in H4.
    destruct H4.
    destruct_lift H4; eauto.
    
  + simpl in *; cleanup.
    eapply sp_impl in H0;
    [> eapply get_inode_ok in H0; eauto
    |try solve [intros; cleanup; simpl; intuition eauto] ].
    cleanup.
    right; intuition.
Qed.

Theorem get_block_number_ok:
  forall inum off s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (get_block_number inum off)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s))) t s' ->
    (exists inode, imap inum = Some inode /\ t = nth_error inode.(block_numbers) off /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ imap inum = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold get_block_number; intros; cleanup.
  apply sp_bind in H.
  simpl in *; cleanup.
    
  eapply sp_impl in H;
  [> eapply get_inode_ok in H; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].
  cleanup.
  
  + simpl in *; cleanup; left; eexists; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
  + simpl in *; cleanup; right; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
Qed.


Theorem get_block_numbers_ok:
  forall inum s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (get_block_numbers inum)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s))) t s' ->
    (exists inode, imap inum = Some inode /\ t = Some inode.(block_numbers) /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ imap inum = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold get_block_numbers; intros; cleanup.
  apply sp_bind in H.
  simpl in *; cleanup.
    
  eapply sp_impl in H;
  [> eapply get_inode_ok in H; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].
  cleanup.
  
  + simpl in *; cleanup; left; eexists; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
    
  + simpl in *; cleanup; right; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
Qed.

Theorem get_owner_ok:
  forall inum s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (get_owner inum)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s))) t s' ->
    (exists inode, imap inum = Some inode /\ t = Some inode.(owner) /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ imap inum = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold get_block_numbers; intros; cleanup.
  apply sp_bind in H.
  simpl in *; cleanup.
    
  eapply sp_impl in H;
  [> eapply get_inode_ok in H; eauto
  |try solve [intros; cleanup; simpl; intuition eauto] ].
  cleanup.
  
  + simpl in *; cleanup; left; eexists; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
    
  + simpl in *; cleanup; right; intuition eauto.
    eapply get_inode_ok in H0; eauto.
    cleanup; eauto.
Qed.
*)
Global Opaque alloc free extend change_owner get_block_number get_block_numbers get_owner.

