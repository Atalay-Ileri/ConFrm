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
Fixpoint count_somes_up_to {V} n (m: @mem nat _ V) :=
  match n with
  | 0 => 0
  | S x => 
    match m x with
    | None => count_somes_up_to x m 
    | Some _ => S (count_somes_up_to x m)
    end
  end.

  Fixpoint get_all_file_sizes_up_to fm n :=
    match n with
    | 0 => 0
    | S n' =>
      match fm n' with
      |Some f => length (f.(blocks))
      |None => 0
      end + get_all_file_sizes_up_to fm n'
    end.

  
  Lemma get_all_file_sizes_0_empty_disk:
  forall n fm,
  (forall i, fm i = None) ->
  get_all_file_sizes_up_to fm n = 0.
  Proof.
    induction n; simpl; intros; eauto.
    rewrite H; eauto.
  Qed.

  Lemma get_all_file_sizes_up_to_empty_mem:
  forall n,
  get_all_file_sizes_up_to empty_mem n = 0.
  Proof.
    induction n; simpl; intros; eauto.
  Qed.
  
  Lemma get_all_file_sizes_equal_after_disk:
  forall a n fm,
  (forall i, i >= n -> fm i = None) ->
  get_all_file_sizes_up_to fm n = get_all_file_sizes_up_to fm (n + a).
  Proof.
    induction a; simpl; intros.
    {
      rewrite PeanoNat.Nat.add_0_r; eauto.
    }
    {
      replace (n + S a) with (S n + a) by lia.
      rewrite IHa; simpl; eauto.
      setoid_rewrite H; eauto; simpl.
      lia.
    }
  Qed.

  Lemma count_somes_up_to_empty_mem:
  forall V n,
  count_somes_up_to n (@empty_mem _ _ V) = 0.
  Proof.
    induction n; simpl; intros; eauto.
  Qed.

  Lemma count_somes_up_to_upd_oob:
    forall V n a (v: V) m,
    a >= n ->
    count_somes_up_to n (Mem.upd m a v) = count_somes_up_to n m.
    Proof.
      induction n; simpl; intros.
      eauto.
      rewrite Mem.upd_ne.
      rewrite IHn; eauto.
      all: lia.
    Qed. 

    Lemma count_somes_up_to_some_upd:
    forall V n a (v: V) m,
    (exists v, m a = Some v) ->
    count_somes_up_to n (Mem.upd m a v) = count_somes_up_to n m.
    Proof.
      induction n; simpl; intros.
      eauto.
      destruct (lt_dec a n).
      rewrite Mem.upd_ne.
      rewrite IHn; eauto.
      lia.

      rewrite count_somes_up_to_upd_oob.
      destruct H; subst.
      destruct (addr_dec a n).
      rewrite Mem.upd_eq; subst; eauto.
      rewrite H; simpl; eauto.

      rewrite Mem.upd_ne; eauto.
      lia.
    Qed. 

    Lemma count_somes_up_to_none_upd:
    forall V n a (v: V) m,
    m a = None ->
    a < n ->
    count_somes_up_to n (Mem.upd m a v) = count_somes_up_to n m + 1.
    Proof.
      induction n; simpl; intros.
      lia; eauto.
      destruct (addr_dec a n); subst.
      rewrite Mem.upd_eq; subst; eauto.
      rewrite H; simpl; eauto.
      rewrite count_somes_up_to_upd_oob.
      lia.
      eauto.

      rewrite Mem.upd_ne; eauto.
      rewrite IHn; eauto.
      destruct (m n); simpl; lia.
      lia.
    Qed. 

    Lemma count_somes_up_to_delete_oob:
    forall V n a (m: @mem _ _ V),
    a >= n ->
    count_somes_up_to n (Mem.delete m a) = count_somes_up_to n m.
    Proof.
      induction n; simpl; intros.
      eauto.
      rewrite Mem.delete_ne.
      rewrite IHn; eauto.
      all: lia.
    Qed. 

    Lemma count_somes_up_to_some_nonzero:
    forall V n a (m: @mem _ _ V),
    a < n ->
    (exists v, m a = Some v) ->
    count_somes_up_to n m > 0.
    Proof.
      induction n; simpl; intros.
      lia.
      destruct H0.
      destruct (addr_dec a n); subst.
      rewrite H0; simpl; eauto.
      lia.
      destruct (m n); simpl; try lia.
      eapply IHn; eauto.
      lia.
    Qed.

    Lemma count_somes_up_to_some_delete:
    forall V n a (m: @mem _ _ V),
    a < n ->
    (exists v, m a = Some v) ->
    count_somes_up_to n (Mem.delete m a) = 
    count_somes_up_to n m - 1.
    Proof.
      induction n; simpl; intros.
      lia.
      destruct H0.
      destruct (addr_dec a n); subst.
      rewrite Mem.delete_eq; subst; eauto.
      rewrite H0; simpl; eauto.
      rewrite count_somes_up_to_delete_oob.
      lia.
      eauto.

      rewrite Mem.delete_ne; eauto.
      rewrite IHn; eauto.
      destruct (m n); simpl; try lia.
      assert (A: a < n) by lia.
      eapply count_somes_up_to_some_nonzero in A; eauto.
      lia.
      lia.
    Qed.

    Lemma count_somes_up_to_some_repeated_delete:
    forall V l_a n (m: @mem _ _ V),
    Forall (fun a => a < n) l_a ->
    Forall (fun a => exists v, m a = Some v) l_a ->
    NoDup l_a ->
    count_somes_up_to n (repeated_apply
    (Mem.delete (AEQ:=addr_dec)) m l_a) = 
    count_somes_up_to n m -length l_a.
    Proof.
      induction l_a; simpl; intros.
      lia.
      inversion H; inversion H0; inversion H1; cleanup.
      rewrite count_somes_up_to_some_delete; eauto.
      rewrite IHl_a; eauto.
      lia.
      eexists; rewrite repeated_apply_delete_not_in; eauto.
    Qed.

    Lemma count_somes_up_to_some_delete_list:
    forall V l n (m1 m2: @mem _ _ V),
    (forall a, In a l -> a < n) ->
    (forall a, In a l -> exists v, m1 a = Some v) ->
    (forall a, In a l -> m2 a = None) ->
    (forall a, ~In a l -> m1 a = m2 a) ->
    NoDup l -> 
    count_somes_up_to n m2 = count_somes_up_to n m1 - length l.
    Proof.
      induction l; simpl; intros.
      assert (m1 = m2). {
        extensionality x.
        eauto.
      }
      subst; lia.
      erewrite IHl.
      instantiate (1:= Mem.delete m1 a).
      erewrite count_somes_up_to_some_delete; eauto.
      lia.
      all: intuition.
      inversion H3; subst.
      rewrite Mem.delete_ne; eauto.
      congruence.
      inversion H3; subst.
      destruct (addr_dec a a0); subst.
      rewrite Mem.delete_eq; eauto.
      symmetry.
      apply H1; intuition.
      rewrite Mem.delete_ne; eauto.
      apply H2; intuition.
      inversion H3; subst; eauto.
    Qed.

    Lemma get_all_file_sizes_up_to_upd_oob:
      forall n a f m,
      a >= n ->
      get_all_file_sizes_up_to (Mem.upd m a f) n = 
      get_all_file_sizes_up_to m n.
      Proof.
        induction n; simpl; intros.
        eauto.
        rewrite Mem.upd_ne.
        rewrite IHn; eauto.
        all: lia.
      Qed. 

    Lemma get_all_file_sizes_up_to_in_le:
      forall n f1 a m,
      m a = Some f1 ->
      a < n ->
      length (blocks f1) <= get_all_file_sizes_up_to m n.
      Proof.
        induction n; simpl; intros.
        lia; eauto.
        destruct (addr_dec a n).
        subst; rewrite H; simpl; eauto.
        lia.

        erewrite IHn; eauto.
        lia.
        lia.
      Qed.


    Lemma get_all_file_sizes_up_to_upd_some:
      forall n f1 f2 a m,
      m a = Some f1 ->
      a < n ->
      get_all_file_sizes_up_to (Mem.upd m a f2) n = 
      (get_all_file_sizes_up_to m n - length (blocks f1)) + length (blocks f2).
    Proof.
      induction n; simpl; intros.
      lia; eauto.
      destruct (addr_dec a n).
      rewrite Mem.upd_eq; subst; eauto.
      rewrite H; simpl; eauto.
      rewrite get_all_file_sizes_up_to_upd_oob.
      lia.
      eauto.
      
      rewrite Mem.upd_ne; eauto.
      erewrite IHn; eauto.
      rewrite <- PeanoNat.Nat.add_sub_assoc.
      lia.
      eapply get_all_file_sizes_up_to_in_le; eauto.
      all: lia.
    Qed. 

    Lemma get_all_file_sizes_up_to_upd_none:
      forall n f1 a m,
      m a = None ->
      a < n ->
      get_all_file_sizes_up_to (Mem.upd m a f1) n = 
      get_all_file_sizes_up_to m n + length (blocks f1).
    Proof.
      induction n; simpl; intros.
      lia; eauto.
      destruct (addr_dec a n).
      rewrite Mem.upd_eq; subst; eauto.
      rewrite H; simpl; eauto.
      rewrite get_all_file_sizes_up_to_upd_oob.
      lia.
      eauto.
      
      rewrite Mem.upd_ne; eauto.
      erewrite IHn; eauto.
      all: lia.
    Qed. 

    Lemma get_all_file_sizes_up_to_delete_oob:
      forall n a m,
      a >= n ->
      get_all_file_sizes_up_to (Mem.delete m a) n = 
      get_all_file_sizes_up_to m n.
      Proof.
        induction n; simpl; intros.
        eauto.
        rewrite Mem.delete_ne.
        rewrite IHn; eauto.
        all: lia.
      Qed. 

    Lemma get_all_file_sizes_up_to_delete:
      forall n f1 a m,
      m a = Some f1 ->
      a < n ->
      get_all_file_sizes_up_to (Mem.delete m a) n = 
      get_all_file_sizes_up_to m n - length (blocks f1).
    Proof.
      induction n; simpl; intros.
      lia; eauto.
      destruct (addr_dec a n); subst.
      rewrite Mem.delete_eq; subst; eauto.
      rewrite H; simpl; eauto.
      rewrite get_all_file_sizes_up_to_delete_oob.
      lia.
      eauto.
      
      rewrite Mem.delete_ne; eauto.
      erewrite IHn; eauto.
      rewrite <- PeanoNat.Nat.add_sub_assoc.
      lia.
      eapply get_all_file_sizes_up_to_in_le; eauto.
      all: lia.
    Qed. 

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
     file_rep file inode file_block_map) /\
     count_somes_up_to DiskAllocatorParams.num_of_blocks file_block_map = get_all_file_sizes_up_to file_disk Inode.InodeAllocatorParams.num_of_blocks.

Definition files_inner_rep (file_disk: disk File) (d: @total_mem addr addr_dec value):=
  exists inode_map,
    inode_rep inode_map d /\
    
  exists file_block_map,
    DiskAllocator.block_allocator_rep file_block_map d /\
    file_map_rep file_disk inode_map file_block_map.

Definition files_rep (file_disk: disk File) (d: ADLang.(state)) :=
  fst (snd d) = Empty /\
  fst (snd (snd d)) = snd (snd (snd d)) /\
  files_inner_rep file_disk (fst (snd (snd d))).

Definition files_crash_rep (file_disk: disk File) (d: ADLang.(state)) :=
  files_inner_rep file_disk (snd (snd (snd d))).

Definition files_reboot_rep := files_crash_rep.


(*** Functions ***)
Definition auth_then_exec {T} (inum: Inum) (p: Inum -> prog (TDLang data_length) (option T)) :=
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
  r <- Inode.get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
    if r is Some v then
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Definition write_inner off v inum :=
  r <- Inode.get_block_number inum off;
  if r is Some block_number then
    DiskAllocator.write block_number v
  else
    Ret None.

Definition change_owner_inner owner inum :=
  Inode.change_owner inum owner.


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
  mbl <- Inode.get_all_block_numbers inum;
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
    Inode.extend inum block_num
  else
    Ret None.

(* For Implementation Purposes *)
Definition get_file_size_inner inum :=
  mbl <- Inode.get_all_block_numbers inum;
  if mbl is Some block_numbers then
    Ret (Some (length block_numbers))
  else
    Ret None.


Definition read inum off := auth_then_exec inum (read_inner off).
Definition write inum off v := auth_then_exec inum (write_inner off v).
Definition extend inum v := auth_then_exec inum (extend_inner v).
Definition change_owner inum owner := auth_then_exec inum (change_owner_inner owner).
Definition delete inum := auth_then_exec inum delete_inner.
Definition get_file_size inum := auth_then_exec inum get_file_size_inner.

Definition create owner :=
  r <- |ADDP| Inode.alloc owner;
  if r is Some inum then
     _ <- |ADDO| Commit;
     Ret (Some inum)
  else
    _ <- |ADDO| Abort;
    Ret None.

Definition recover := |ADDO| Recover.

Definition init :=
|ADDO| Init [(Inode.InodeAllocatorParams.bitmap_addr,
              bits_to_value zero_bitmap);
            (DiskAllocatorParams.bitmap_addr,
             bits_to_value zero_bitmap)].

Definition update_file f off v := Build_File f.(BaseTypes.owner) (updn f.(blocks) off v).
Definition extend_file f v := Build_File f.(BaseTypes.owner) (f.(blocks) ++ [v]).
Definition new_file o := Build_File o [].
Definition change_file_owner f o := Build_File o f.(blocks).
