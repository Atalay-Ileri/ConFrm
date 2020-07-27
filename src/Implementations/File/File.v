Require Import Framework FSParameters AuthenticatedDiskLayer BlockAllocator Inode.
Import IfNotations.

Open Scope predicate_scope.

Module DiskAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := file_blocks_start.
  Definition num_of_blocks := file_blocks_count.
  Definition num_of_blocks_in_bounds := file_blocks_count_in_bounds.
  Definition blocks_fit_in_disk := file_blocks_fit_in_disk.
End DiskAllocatorParams.

Module DiskAllocator := BlockAllocator DiskAllocatorParams.

Record File := {
    owner: user;
    blocks: list value;
  }.

Definition file_rep (file: File) (inode: Inode) (file_block_map: disk value) :=
  file.(owner) = inode.(Inode.owner) /\
  length file.(blocks) = length inode.(block_numbers) /\
  (forall i block_number,
       nth_error inode.(block_numbers) i = Some block_number ->
       nth_error file.(blocks) i = file_block_map block_number).

Definition files_inner_rep (file_map: @mem Inum addr_dec File) inode_map file_block_map :=
   addrs_match_exactly file_map inode_map /\
   (forall inum inode file,
     inode_map inum  = Some inode ->
     file_map inum = Some file ->
     file_rep file inode file_block_map).

Definition files_rep (file_map: disk File) :=
  exists* inode_map,
    inode_rep inode_map *
    exists* file_block_map,
    DiskAllocator.block_allocator_rep file_block_map *
    [[ files_inner_rep file_map inode_map file_block_map ]].

Local Definition auth_then_exec {T} (inum: Inum) (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) :=
  _ <- |ADDO| Start;
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
        
Local Definition read_inner off inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
    if r is Some v then
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Local Definition write_inner off v inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.write block_number v;
    if r is Some tt then
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Local Definition change_owner_inner owner inum :=
  r <- change_owner inum owner;
  if r is Some tt then
     Ret (Some tt)
  else
    Ret None.

Local Fixpoint free_all_blocks block_nums :=
  match block_nums with
  | nil =>
    Ret (Some tt)
  | bn :: block_nums' =>
    ok <- DiskAllocator.free bn;
    if ok is Some tt then
      r <- free_all_blocks block_nums';
      Ret r
    else
      Ret None
end.

Local Definition delete_inner inum :=
  mbl <- get_block_numbers inum;
  if mbl is Some block_numbers then
    ok <- free_all_blocks block_numbers;
    if ok is Some tt then
      r <- free inum;
      if r is Some tt then
        Ret (Some tt)
      else
        Ret None
    else
      Ret None
  else
    Ret None.

Local Definition extend_inner v inum :=
  mbn <- DiskAllocator.alloc v;
  if mbn is Some block_num then
    r <- extend inum block_num;
    if r is Some tt then
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.


Definition read inum off := auth_then_exec inum (read_inner off).
Definition write inum off v := auth_then_exec inum (write_inner off v).
Definition extend inum v := auth_then_exec inum (extend_inner v).
Definition change_owner inum owner := auth_then_exec inum (change_owner_inner owner).
Definition delete inum := auth_then_exec inum delete_inner.

Definition create owner :=
  _ <- |ADDO| Start;
  r <- |ADDP| alloc owner;
  if r is Some inum then
     _ <- |ADDO| Commit;
     Ret (Some inum)
  else
    _ <- |ADDO| Abort;
    Ret None.

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
          repeat (split_ors; cleanup; simpl in *).
          
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
          repeat (split_ors; cleanup; simpl in *); eauto.

          intuition eauto.
          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x1.
          pred_apply; cancel.
          exists x2.
          pred_apply; cancel.
          eauto.
          all: exact AuthenticationLang.
        }
        { (* p Failed. *)
          cleanup; simpl in *.
          repeat (apply sp_exists_extract in H1; cleanup).
          apply sp_lift2 in H1; simpl in H1.
          apply sp_extract_precondition in H1; cleanup.
          apply get_owner_files_rep_ok in H2.
          repeat (split_ors; cleanup; simpl in *).
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
          repeat (split_ors; cleanup; simpl in *).
          intuition eauto.
          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x1.
          pred_apply; cancel.
          exists x2.
          pred_apply; cancel.
          eauto.
          all: exact AuthenticationLang.
        }
      }
      { (* Auth Fail *)
        simpl in *; cleanup.
        split_ors; cleanup.
        
        apply get_owner_files_rep_ok in H1.
        cleanup.
        repeat (split_ors; cleanup; simpl in *).
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
  forall inum t sx F fmap file off,
    strongest_postcondition (TransactionalDiskLang data_length)
      (get_block_number inum off)
      (fun o s => (F * files_rep fmap)%predicate
                (mem_union (fst s) (snd s)) /\
               fmap inum = Some file) t sx ->
    exists imap fbmap,
      (exists inode : Inode,
         imap inum = Some inode /\
         fmap inum = Some file /\
         t = nth_error inode.(block_numbers) off /\
         (t = None -> off >= length inode.(block_numbers)) /\
         (F * DiskAllocator.block_allocator_rep fbmap *
          [[files_inner_rep fmap  imap fbmap ]] * inode_rep imap)%predicate
           (mem_union (fst sx) (snd sx))).
Proof.
  intros.
        
  eapply sp_impl in H.
  apply (sp_exists_extract (disk Inode)) with
      (P:= fun (inode_map: disk Inode) o (sx : state') =>
             (F * inode_rep inode_map *
              (exists* (file_block_map : disk value),  
              DiskAllocator.block_allocator_rep file_block_map *
              [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\ fmap inum = Some file) in H; cleanup.

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
              (inode_rep x *
               DiskAllocator.block_allocator_rep file_block_map *
               [[files_inner_rep fmap x file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\ fmap inum = Some file) in H; cleanup.

  2: {
    simpl; intros; cleanup.            
    apply pimpl_exists_l_star_r in H0.
    destruct H0.
    exists x0; simpl in *; eauto.
    intuition eauto.
    pred_apply; cancel.
  }
  
  apply sp_extract_precondition in H; cleanup.
  destruct_lifts.
  destruct_fresh (x inum).
  {
    eapply sp_impl in H.
    apply get_block_number_ok in H; eauto.

    2: {
      simpl; intros; cleanup.
      pred_apply; cancel.
      instantiate (1:= x); cancel.
    }
    split_ors; cleanup.
    unfold files_inner_rep in *; cleanup.
    specialize H2 with (1:= D)(2:= H1) as Hx.
    unfold file_rep in *; cleanup.
    do 3 eexists; intuition eauto.
    apply nth_error_None; eauto.
    pred_apply; cancel; eauto.
  }    
  {
    unfold files_inner_rep in *; cleanup.
    specialize (H2 inum); cleanup; exfalso; intuition eauto.
    apply H4; congruence.
  }
Qed.

Theorem read_inner_ok:
  forall inum off s' t fmap F file,
    strongest_postcondition (TransactionalDiskLang data_length) (read_inner off inum)
     (fun o s => (F * files_rep fmap)%predicate (mem_union (fst s) (snd s)) /\ fmap inum = Some file) t s' ->
     ( t = nth_error file.(blocks) off /\ (F * files_rep fmap)%predicate (mem_union (fst s') (snd s'))).
Proof.
  unfold read_inner; simpl; intros.
  repeat (cleanup; simpl in *).
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

Global Opaque read_inner.
          
Theorem read_ok:
  forall inum off s' t fmap F,
    strongest_postcondition AuthenticatedDiskLang (read inum off)
     (fun o s => (F * files_rep fmap)%predicate (mem_union (fst (snd s)) (snd (snd s))) /\ (fst (snd s)) = empty_mem) t s' ->
    (exists file, fmap inum = Some file /\
             t = nth_error file.(blocks) off /\
             (F * files_rep fmap)%predicate (mem_union (fst (snd s')) (snd (snd s'))) /\
             (fst (snd s')) = empty_mem) \/
((fmap inum = None \/
       (exists file : File,
          fmap inum = Some file /\ fst s' <> owner file)) /\
         (fst (snd s')) = empty_mem).
Proof.
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
    admit.
  }
  
  simpl in *.
  split_ors; cleanup.
  left; eexists; intuition eauto.
  right; intuition eauto.
Admitted.
