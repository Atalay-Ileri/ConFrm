Require Import Framework FSParameters TransactionalDiskLayer BlockAllocator.
Import IfNotations.

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

Import InodeAllocator.

Open Scope predicate_scope.

Definition inode_map_rep inode_block_map (inode_map: disk Inode) :=
  forall i, inode_map i = option_map decode_inode (inode_block_map i).

Definition inode_rep (inode_map: disk Inode) : @predicate addr addr_dec value :=
  exists* inode_block_map,
    block_allocator_rep inode_block_map *
    [[ forall i, inode_map i = option_map decode_inode (inode_block_map i) ]].

Local Definition get_inode inum :=
  r <- read inum;
  if r is Some i then
    Ret (Some (decode_inode i))
  else
    Ret None.

Local Definition set_inode inum inode:=
  r <- write inum (encode_inode inode);
  Ret r.

Definition alloc user :=
  r <- alloc (encode_inode (Build_Inode user []));
  Ret r.

Definition free inum :=
  r <- free inum;
  Ret r.

Definition extend inum block_num :=
  r <- get_inode inum;
  if r is Some inode then
    r <- set_inode inum (Build_Inode inode.(owner) (inode.(block_numbers)++[block_num]));
      Ret r
  else
    Ret None.

Definition change_owner inum user :=
  r <- get_inode inum;
  if r is Some inode then
    r <- set_inode inum (Build_Inode user inode.(block_numbers));
      Ret r
  else
    Ret None.

Definition get_block_number inum off:=
  r <- get_inode inum;
  if r is Some inode then
    Ret (nth_error inode.(block_numbers) off)
  else
    Ret None.

Definition get_block_numbers inum :=
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
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]]))%predicate
    (mem_union (fst s) (snd s))) in H.
    cleanup.
    eapply sp_impl in H.
    apply read_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x i)]]).
      pred_apply' H0; cancel.
    }
    
    cleanup.
    destruct_lift H0.
    rewrite H4; cleanup.
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
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]]))%predicate
    (mem_union (fst s) (snd s))) in H.
    cleanup.
    eapply sp_impl in H.
    apply read_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x i)]]).
      pred_apply' H0; cancel.
    }
    
    cleanup.
    destruct_lift H0.
    rewrite H4; cleanup.
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
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists i, imap inum = Some i /\ t = Some tt /\ (F * inode_rep (upd imap inum inode))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold inode_rep; intros; simpl in *; cleanup.
  eapply sp_impl in H.
  eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]]))%predicate
                                                                          (mem_union (fst s) (snd s)) /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply write_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]]).
      split; eauto.
      pred_apply' H0; cancel.
    }
    split_ors; cleanup.
    
  -    destruct_lift H1.
    left; eexists; intuition eauto.
    rewrite H4, H; simpl; eauto.
    pred_apply; cancel.
    exists (upd x0 inum (encode_inode inode)).
    pred_apply; cancel.
    destruct (addr_dec inum i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite inode_encode_decode; eauto.

  - right; intuition cleanup.
    pred_apply; cancel.
    exists x0.
    pred_apply; cancel.
    
 - simpl; intros; cleanup.
   apply pimpl_exists_l_star_r in H0.
   destruct H0.
   exists x0; eauto.
Qed.

Global Opaque get_inode set_inode.

Theorem alloc_ok:
  forall user s' t imap F,
    strongest_postcondition (TransactionalDiskLang data_length) (alloc user)
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
                            (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists inum, t = Some inum /\ (F * inode_rep (upd imap inum (Build_Inode user [])))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * inode_rep imap)%predicate (mem_union (fst s') (snd s'))).
Proof.
    unfold inode_rep; intros; simpl in *; cleanup.
  eapply sp_impl in H.
  eapply (sp_exists_extract (disk value)) with (P:=fun inode_block_map o s =>  (F *
   (block_allocator_rep inode_block_map *
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]]))%predicate
                                                                          (mem_union (fst s) (snd s)) /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply alloc_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]]).
      split; eauto.
      pred_apply' H0; cancel.
    }
    split_ors; cleanup.
  - left; exists x1; intuition cleanup.
    pred_apply; cancel.
    exists (upd x0 x1 (encode_inode (Build_Inode user []))).
    pred_apply; cancel.
    destruct (addr_dec x1 i); subst;
    [ repeat rewrite upd_eq | repeat rewrite upd_ne]; simpl; eauto.
    rewrite inode_encode_decode; eauto.
    
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
    [[forall i : addr, imap i = option_map decode_inode (inode_block_map i)]]))%predicate
                                                                          (mem_union (fst s) (snd s)) /\
                                               (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list) in H.
    cleanup.
    eapply sp_impl in H.
    apply free_ok in H.
    2: {
      intros; cleanup.
      simpl; eauto.
      instantiate (1:= x0).
      instantiate (1:= F * [[forall i : addr, imap i = option_map decode_inode (x0 i)]]).
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
                            (fun o s => (F * inode_rep imap)%predicate (mem_union (fst s) (snd s)) /\
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
    instantiate (2:= F * [[forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull]%list ]] ) in H3.
    cleanup; destruct_lift H4.
    split; eauto.

    simpl; intros; cleanup.
    pred_apply; cancel.
    eapply H5; eauto.
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
    instantiate (2:= F * [[forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull]%list ]] ) in H3.
    cleanup; destruct_lift H4.
    split; eauto.

    simpl; intros; cleanup.
    pred_apply; cancel.
    eapply H5; eauto.
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

Global Opaque alloc free extend change_owner get_block_number get_block_numbers get_owner.
