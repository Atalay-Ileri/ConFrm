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

Record File :=
  {
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
  exists* inode_map file_block_map,
    inode_rep inode_map *
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



Theorem sp_lift1_ok:
  forall O1 O2 (L1 : Language O1) (L2: Language O2) (HL: Language (HorizontalComposition O1 O2))
    T (p: prog L1 T) s t P,
    strongest_postcondition HL (lift_L1 O2 p) P t s ->
    strongest_postcondition L1 p (fun o sx => P (map (fun o' =>
                                                     match o' with
                                                     |OpOracle _ o1 =>
                                                      OpOracle (HorizontalComposition O1 O2) [Oracle1 O1 O2 o1]%list
                                                     |Language.Cont _ =>
                                                      Language.Cont _
                                                     |Language.Crash _ =>
                                                      Language.Crash _
                                                     end) o) (sx, snd s)) t (fst s).
Proof.
  induction p; destruct s; simpl in *; intros; cleanup; eauto.
  eapply H in H0; simpl in *.
  eapply sp_to_exec in H0; cleanup.
  eapply IHp in H1; simpl in *.
  setoid_rewrite <- map_app in H1.
  exists x; intuition eauto.
  eapply exec_to_sp; eauto.
Qed.

Theorem sp_lift2_ok:
  forall O1 O2 (L1 : Language O1) (L2: Language O2) (HL: Language (HorizontalComposition O1 O2))
    T (p: prog L2 T) s t P,
    strongest_postcondition HL (lift_L2 O1 p) P t s ->
    strongest_postcondition L2 p (fun o sx => P (map (fun o' =>
                                                     match o' with
                                                     |OpOracle _ o2 =>
                                                      OpOracle (HorizontalComposition O1 O2) [Oracle2 O1 O2 o2]%list
                                                     |Language.Cont _ =>
                                                      Language.Cont _
                                                     |Language.Crash _ =>
                                                      Language.Crash _
                                                     end) o) (fst s, sx)) t (snd s).
Proof.
  induction p; destruct s; simpl in *; intros; cleanup; eauto.
  eapply H in H0; simpl in *.
  eapply sp_to_exec in H0; cleanup.
  eapply IHp in H1; simpl in *.
  setoid_rewrite <- map_app in H1.
  exists x; intuition eauto.
  eapply exec_to_sp; eauto.
Qed.

Theorem sp_extract_precondition:
  forall O (L : Language O) T (p: prog L T) s t P,
    strongest_postcondition L p P t s ->
    strongest_postcondition L p P t s /\ (exists o s, P o s).
Proof.
  intros; eapply_fresh sp_to_exec in H; cleanup; eauto.
Qed.

Theorem auth_then_exec_ok:
  forall inum T (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) s' t fmap F (Q: option T -> state  (TransactionalDiskLang data_length) -> Prop),
    
    (forall fmap' t' s'',
       strongest_postcondition (TransactionalDiskLang data_length) (p inum)
                               (fun o s => (F * files_rep fmap')%predicate (mem_union (fst s) (snd s))) t' s'' ->
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
          apply sp_lift2_ok in H1; simpl in H1.
          apply sp_extract_precondition in H1; cleanup.
          repeat (apply sp_exists_extract in H2; cleanup).
          split_ors; cleanup.
          apply sp_lift2_ok in H2; simpl in H2; cleanup.
          
          eapply sp_impl in H2.
          apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H2; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H5.
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x6; simpl; eauto.
          }
          
          eapply sp_impl in H2.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x6 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x6 file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H2; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x7; simpl; eauto.
          }
          
          apply sp_extract_precondition in H2; cleanup.
          simpl in *.
          eapply sp_impl in H2.
          apply get_owner_ok in H2.
          
          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x6).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x7 * [[files_inner_rep fmap x6 x7]])).
            pred_apply; cancel.
          }
          
          split_ors; cleanup.
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.
          
          left; eexists; intuition eauto.
          specialize H8 with (1:= H2)(2:=D).
          unfold file_rep in *; cleanup; eauto.
          eapply sp_impl in H1; eauto.
          eapply H in H1; simpl in *; eauto.
          split_ors; cleanup; eauto.

          intros; simpl in *; cleanup.
          apply sp_lift2_ok in H4; simpl in H4; cleanup.

          eapply sp_impl in H4.
          apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H4; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H12.
            apply pimpl_exists_l_star_r in H12.
            destruct H12.
            exists x1; simpl; eauto.
          }
          
          eapply sp_impl in H4.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x0 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x0 file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H4; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H12.
            destruct H12.
            exists x1; simpl in *; eauto.
          }
          
          
          apply sp_extract_precondition in H4; cleanup.
          simpl in *.
          eapply sp_impl in H4.
          apply get_owner_ok in H4.
          split_ors; cleanup.

          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x0).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x1 * [[files_inner_rep fmap x0 x1]])).
            pred_apply; cancel.
          }

          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x0.
          apply pimpl_exists_r_star.
          exists x1.
          pred_apply; cancel.
          all: exact AuthenticationLang.
        }
        { (* p Failed. *)
          cleanup; simpl in *.
          repeat (apply sp_exists_extract in H1; cleanup).
          apply sp_lift2_ok in H1; simpl in H1.
          apply sp_extract_precondition in H1; cleanup.
          repeat (apply sp_exists_extract in H2; cleanup).
          split_ors; cleanup.
          apply sp_lift2_ok in H2; simpl in H2; cleanup.
          
          eapply sp_impl in H2.
          apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H2; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H5.
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x6; simpl; eauto.
          }
          
          eapply sp_impl in H2.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x6 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x6 file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H2; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x7; simpl; eauto.
          }
          
          apply sp_extract_precondition in H2; cleanup.
          simpl in *.
          eapply sp_impl in H2.
          apply get_owner_ok in H2.
          
          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x6).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x7 * [[files_inner_rep fmap x6 x7]])).
            pred_apply; cancel.
          }
          
          split_ors; cleanup.
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.
          
          left; eexists; intuition eauto.
          specialize H8 with (1:= H2)(2:=D).
          unfold file_rep in *; cleanup; eauto.
          eapply sp_impl in H1; eauto.
          eapply H in H1; simpl in *; eauto.        
          split_ors; cleanup; intuition eauto.
          
          simpl; intros; cleanup.
          repeat (apply sp_exists_extract in H4; cleanup).
          apply sp_lift2_ok in H4; simpl in H4; cleanup.

          eapply sp_impl in H4.
          apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H4; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H12.
            apply pimpl_exists_l_star_r in H12.
            destruct H12.
            exists x1; simpl; eauto.
          }
          
          eapply sp_impl in H4.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x1 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x1 file_block_map]]))%predicate (mem_union (fst sx) (snd sx)) /\
                                                           tt = tt /\ sx = (empty_mem, snd x0)) in H4; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H12.
            destruct H12.
            exists x2; simpl in *; eauto.
          }
          
          
          apply sp_extract_precondition in H4; cleanup.
          simpl in *.
          eapply sp_impl in H4.
          apply get_owner_ok in H4.
          split_ors; cleanup.

          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x1).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x2 * [[files_inner_rep fmap x1 x2]])).
            pred_apply; cancel.
          }

          unfold files_rep.         
          apply sep_star_comm.
          repeat apply pimpl_exists_r_star.
          exists x1.
          apply pimpl_exists_r_star.
          exists x2.
          pred_apply; cancel.
          all: exact AuthenticationLang.
        }
      }
      { (* Auth Fail *)
        simpl in *; cleanup.
        split_ors; cleanup.

        apply sp_lift2_ok in H1; simpl in H1; cleanup.        
        repeat (apply sp_exists_extract in H1; cleanup).
        eapply sp_impl in H1.
          apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H1; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H5.
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x4; simpl; eauto.
          }
          
          eapply sp_impl in H1.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x4 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x4 file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H1; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H5.
            destruct H5.
            exists x0; simpl; eauto.
          }
          
          eapply sp_impl in H1.
          apply get_owner_ok in H1.
          
          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x4).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x0 * [[files_inner_rep fmap x4 x0]])).
            pred_apply; cancel.
          }
          
          split_ors; cleanup.
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.
          
          right; intuition eauto.
          specialize H7 with (1:= H1)(2:=D).
          unfold file_rep in *; cleanup; eauto.
          right; eexists; intuition eauto.
          apply H2; cleanup; eauto.
          all: exact AuthenticationLang.
      }
    }
    { (* Invalid Inum *)
      cleanup; simpl in *.
       apply sp_lift2_ok in H1; simpl in H1; cleanup.        
       repeat (apply sp_exists_extract in H1; cleanup).
       eapply sp_impl in H1.
       apply (sp_exists_extract (disk Inode)) with
          (P:= fun (inode_map: disk Inode) o (sx : state') => (F *
           (exists* (file_block_map : disk value),
            inode_rep inode_map * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap inode_map file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H1; cleanup.

          2: {
            simpl; intros; cleanup.            
            unfold files_rep in H2.
            apply pimpl_exists_l_star_r in H2.
            destruct H2.
            exists x4; simpl; eauto.
          }
          
          eapply sp_impl in H1.
          apply (sp_exists_extract (disk value)) with
          (P:= fun (file_block_map: disk value) o (sx : state') => (F *
           (inode_rep x4 * DiskAllocator.block_allocator_rep file_block_map *
            [[files_inner_rep fmap x4 file_block_map]]))%predicate (mem_union (fst sx) (snd sx))) in H1; cleanup.

          2: {
            simpl; intros; cleanup.            
            apply pimpl_exists_l_star_r in H2.
            destruct H2.
            exists x0; simpl; eauto.
          }
          
          eapply sp_impl in H1.
          apply get_owner_ok in H1.
          
          2: {
            simpl; intros; cleanup.
            simpl in *.
            instantiate (1:= x4).
            instantiate (1:= (F * DiskAllocator.block_allocator_rep x0 * [[files_inner_rep fmap x4 x0]])).
            pred_apply; cancel.
          }
          
          split_ors; cleanup.
          destruct_lifts; cleanup.
          unfold files_inner_rep in *; cleanup.
          specialize (H4 inum).
          destruct_fresh (fmap inum); intuition eauto.

          exfalso; apply H7; intuition eauto; congruence.
          all: exact AuthenticationLang.
    }      
  }
Qed.
