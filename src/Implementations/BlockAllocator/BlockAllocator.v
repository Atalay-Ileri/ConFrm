Require Import Framework FSParameters TransactionalDiskLayer.
Require Import Arith Lia FunctionalExtensionality.
Import IfNotations.

Set Nested Proofs Allowed.

Notation "| p |" := (Op (TransactionalDiskOperation data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (TransactionalDiskOperation data_length) p1) (fun x => p2))(right associativity, at level 60).

Lemma upd_valid_length:
  forall T (l: list T) n v m,
    length l = m ->
    length (updn l n v) = m.
Proof.
  intros; rewrite updn_length; eauto.
Qed.

Module Type BlockAllocatorParameters.
  Parameter bitmap_addr: addr.
  Parameter num_of_blocks: nat.
  Parameter num_of_blocks_in_bounds: num_of_blocks <= block_size.
  Parameter blocks_fit_in_disk: bitmap_addr + num_of_blocks < data_length.
End BlockAllocatorParameters.
  
(** This is a generic block allocator which has a 1 block bitmap and num_of_blocks blocks following it *)  
Module BlockAllocator (Params : BlockAllocatorParameters).

Import Params.


(*** Functions ***)
(** Returns index instead of data address.
If you want data address, make sure to convert to data address 
by adding (S bitmap_addr)  **) 
Definition alloc (v': value) :=
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  let index := get_first_zero_index (firstn num_of_blocks bits) in
  
  if lt_dec index num_of_blocks then
    r <-| Write (bitmap_addr + S index) v';
    if r is Some tt then
      r <-| Write bitmap_addr
        (bits_to_value (Build_bitlist (updn bits index true)
                     (upd_valid_length _ bits index true _ valid)));
      if r is Some tt then
        Ret (Some index)
      else
        Ret None
    else
      Ret None
  else
    Ret None.

(** Takes index instead of data address. **) 
Definition free a :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some true then
      | Write bitmap_addr
          (bits_to_value (Build_bitlist (updn bits a false)
          (upd_valid_length _ bits a false _ valid)))|
    else
      Ret None
  else
    Ret None.

(** Takes index instead of data address. **) 
Definition read a :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some true then
      v <-| Read (bitmap_addr + S a);
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

(** Takes index instead of data address. **) 
Definition write a b :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some true then
      | Write (bitmap_addr + S a) b|
    else
      Ret None
  else
    Ret None.


(*** Rep Invariants ***)
Fixpoint valid_bits' (dh: disk value) values bits n (d: @total_mem addr addr_dec value) :=
  match values, bits with
  | v::values', b::bits' =>
    d (bitmap_addr + S n) = v /\
    ((b = false /\ dh n = None) \/
    (b = true /\  dh n = Some v)) /\
    valid_bits' dh values' bits' (S n) d
   | _, _ =>
     True
  end.
      
Definition valid_bits dh values bits := valid_bits' dh values bits 0.

Definition block_allocator_rep (dh: disk value) (d: @total_mem addr addr_dec value)  :=
  exists bitmap values,
     let bits := bits (value_to_bits bitmap) in
     d bitmap_addr = bitmap /\
     valid_bits dh values bits d /\
     length values = num_of_blocks /\
     (forall i, i >= num_of_blocks -> dh i = None).


(*** Lemmas ***)
Lemma valid_bits'_split:
  forall dh d a l1 l2 n,
    a < length l1 ->
    length l1 <= length l2 ->
    valid_bits' dh l1 l2 n d ->
    valid_bits' dh (firstn a l1) (firstn a l2) n d /\ valid_bits' dh (skipn a l1) (skipn a l2) (n + a) d.
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r; eauto.
  destruct l1; simpl in *; try lia.
  destruct l2; simpl in *; try lia.
  cleanup.
  edestruct (IHa l1 l2 (S n)); eauto; try lia.   
  repeat split; eauto.
  rewrite <- Nat.add_succ_comm; eauto.
Qed.

Lemma valid_bits'_merge:
  forall dh d a l1 l2 n,
    a < length l1 ->
    length l1 <= length l2 ->
    valid_bits' dh (firstn a l1) (firstn a l2) n d /\ valid_bits' dh (skipn a l1) (skipn a l2) (n + a) d ->
    valid_bits' dh l1 l2 n d.
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r in *; cleanup; eauto.
  destruct l1; simpl in *; try lia.
  destruct l2; simpl in *; try lia.
  cleanup.
  rewrite <- Nat.add_succ_comm in *.
  repeat split; eauto.
  eapply IHa; eauto; try lia.
Qed.


Lemma valid_bits_extract :
  forall dh values bits n d,
    n < length values ->
    length values <= length bits ->
    valid_bits dh values bits d ->
    d (bitmap_addr + S n) = seln values n value0 /\
    ((seln bits n false = false /\ dh n = None) \/
    (seln bits n false = true /\  dh n = Some (seln values n value0))).
Proof.
  intros.
  eapply valid_bits'_split in H1; eauto; simpl in *.
  destruct_fresh (skipn n values).
  - apply length_zero_iff_nil in D.
    rewrite skipn_length in D.
    lia.
  - destruct_fresh (skipn n bits).
    apply length_zero_iff_nil in D0.
    rewrite skipn_length in D0.
    lia.
    simpl in *.
    cleanup.
    rewrite <- Nat.add_0_r with (n:= n).
    rewrite <- skipn_seln.
    rewrite Nat.add_0_r with (n:= n).
    rewrite D; simpl; eauto.
    split; eauto.
    setoid_rewrite <- (firstn_skipn n).
    repeat rewrite seln_app2.
    repeat rewrite D0.
    repeat rewrite firstn_length_l by lia.
    repeat rewrite Nat.sub_diag; simpl; eauto.
    rewrite firstn_length_l; lia.
Qed.

Lemma valid_bits'_inbound_same:
  forall values l_b n dh s1 s2,
    valid_bits' dh values l_b n s1 ->      
    (forall a, bitmap_addr + n + length values >= a
          /\ a >= bitmap_addr + n -> s2 a = s1 a) ->
    valid_bits' dh values l_b n s2.
Proof.
  induction values; simpl; intros; eauto.
  cleanup; eauto.
  repeat (split; eauto).
  eapply H0; lia.
  eapply IHvalues; eauto.
  intros.
  eapply H0; lia.
Qed.

Lemma valid_bits'_zeroes:
  forall s count count2 n,
  count <= count2 ->
    valid_bits' empty_mem (map s (seq (bitmap_addr + S n) count)) (repeat false count2) n s.
Proof.
  induction count; simpl; intros; eauto.
  destruct count2; try lia; simpl.
  intuition eauto.
  rewrite <- Nat.add_succ_r; eauto.
  eapply IHcount; lia.
Qed.

Lemma block_allocator_rep_eq:
  forall dh1 dh2 s,
    block_allocator_rep dh1 s ->
    block_allocator_rep dh2 s ->
    dh1 = dh2.
Proof.
  unfold block_allocator_rep; intros; extensionality x.
  cleanup.
  destruct (le_dec num_of_blocks x); eauto.
  rewrite H6, H3; eauto.
  eapply (valid_bits_extract _ _ _ x) in H4; try lia; cleanup.
  2: rewrite bitlist_length;  pose proof num_of_blocks_in_bounds; lia.
  eapply (valid_bits_extract _ _ _ x) in H1; try lia; cleanup.
  2: rewrite bitlist_length;  pose proof num_of_blocks_in_bounds; lia.
  repeat split_ors; cleanup; eauto; try congruence.
Qed.

Lemma block_allocator_rep_inbounds_eq:
  forall dh s1 s2,
    block_allocator_rep dh s1 ->
    (forall a, bitmap_addr + num_of_blocks >= a /\ a >= bitmap_addr -> s2 a = s1 a) ->
    block_allocator_rep dh s2.
Proof.
  unfold block_allocator_rep; intros.
  cleanup.
  do 2 eexists; intuition eauto.
  rewrite H0; eauto; try lia.
  eapply valid_bits'_inbound_same; eauto.
  rewrite Nat.add_0_r.
  rewrite H2; eauto.
Qed.

(*** Specs ***)
Theorem alloc_finished:
  forall dh u o s v t s',
    block_allocator_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (alloc v) (Finished s' t) ->
    ((exists a, t = Some a /\
           dh a = None /\
           a < num_of_blocks /\
          block_allocator_rep (Mem.upd dh a v) (fst s')) \/
     (t = None /\ block_allocator_rep dh (fst s'))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst s' a = fst s a) /\
     snd s' = snd s.
Proof. 
  unfold alloc; simpl; intros.
  pose proof num_of_blocks_in_bounds.
  pose proof blocks_fit_in_disk.
  cleanup; simpl in *.

  do 2 invert_exec; simpl in *; cleanup;
  [| try solve[repeat invert_exec; split; eauto;
               right; repeat split; eauto] ].

  invert_exec'' H10; simpl in *; cleanup; try lia.
  do 2 invert_exec; simpl in *; cleanup.
  invert_exec'' H11; simpl in *; cleanup; try lia. (** 2: TxnFull? **)
  {
     do 2 invert_exec; simpl in *; cleanup.
     do 2 invert_exec; simpl in *; cleanup.
     {
       split; eauto.
       unfold block_allocator_rep in *; cleanup.
       eapply_fresh valid_bits_extract in H0; eauto; try lia.
       instantiate (1:= (get_first_zero_index (firstn num_of_blocks (bits (value_to_bits (fst x1 bitmap_addr)))))) in Hx.
       logic_clean.      
       {
         setoid_rewrite get_first_zero_index_firstn in H5; eauto.
         rewrite nth_seln_eq in *.
         setoid_rewrite get_first_zero_index_false in H5; eauto.
         split_ors; cleanup; try congruence.
         left; eexists; intuition eauto.
         rewrite get_first_zero_index_firstn; eauto.         
         do 2 eexists; intuition eauto.
         (** valid bits upd lemma **)
         admit.
         clear D.
         rewrite Mem.upd_ne; eauto.  
         lia.         
       }
       rewrite H3; eauto.
       rewrite bitlist_length; lia.
       {
         split; eauto.
         intros.
         repeat rewrite upd_ne; try lia; eauto.
       }
     }
     do 2 invert_exec; simpl in *; cleanup.
     {
       split; eauto.
       unfold block_allocator_rep in *; cleanup.
       eapply_fresh valid_bits_extract in H0; eauto; try lia.
       instantiate (1:= (get_first_zero_index (firstn num_of_blocks (bits (value_to_bits (fst x1 bitmap_addr)))))) in Hx.
       logic_clean.      
       {
         setoid_rewrite get_first_zero_index_firstn in H5; eauto.
         rewrite nth_seln_eq in *.
         setoid_rewrite get_first_zero_index_false in H5; eauto.
         split_ors; cleanup; try congruence.
         right; eexists; intuition eauto.
         
         rewrite get_first_zero_index_firstn; eauto.
         do 2 eexists; intuition eauto.
         (** valid bits upd lemma **)
         admit.
       }
       rewrite H3; eauto.
       rewrite bitlist_length; lia.
       {
         split; eauto.
         intros.
         repeat rewrite upd_ne; try lia; eauto.
       }
     }
     lia.
  }
  do 2 invert_exec; simpl in *; cleanup;
  eauto.
Admitted.
   
       
Theorem free_finished:
  forall dh u o s a t s',
    block_allocator_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (free a) (Finished s' t) ->
    ((t = Some tt /\
       block_allocator_rep (Mem.delete dh a) (fst s')) \/
    (t = None /\ block_allocator_rep dh (fst s'))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst s' a = fst s a) /\
     snd s' = snd s.
Proof.
  unfold free; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia.
  {
    left; split; eauto.
    unfold block_allocator_rep in *; cleanup.
    simpl; do 2 eexists; intuition eauto.
    (** valid bits delete lemma **)
    admit.
    rewrite delete_ne; eauto; lia.
  }
  all: simpl; rewrite upd_ne; eauto; lia.
Admitted.

Theorem read_finished:
  forall dh u o s a t s',
    block_allocator_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (read a) (Finished s' t) ->
    ((exists v, t = Some v /\ dh a = Some v) \/
     (t = None /\ dh a = None)) /\
    block_allocator_rep dh (fst s') /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst s' a = fst s a) /\
    snd s' = snd s.
Proof.
  unfold read; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia;
  try solve [ pose proof blocks_fit_in_disk; lia ].
  {
    left; eexists; intuition eauto.
    unfold block_allocator_rep in *; cleanup.
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    eapply nth_error_nth in D0.
    rewrite <- nth_seln_eq in D0.
    split_ors; cleanup; eauto.
    rewrite e in D0; congruence.
    rewrite bitlist_length; eauto.
    pose proof num_of_blocks_in_bounds; lia.
  }
  {
    unfold block_allocator_rep in *; cleanup.    
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    eapply nth_error_nth in D0.
    rewrite <- nth_seln_eq in D0.
    split_ors; cleanup; eauto.
    rewrite e in D0; congruence.
    rewrite bitlist_length; eauto.
    pose proof num_of_blocks_in_bounds; lia.
  }
  {
    apply nth_error_None in D0.
    rewrite bitlist_length in D0.
    pose proof num_of_blocks_in_bounds; lia.
  }
  {
    unfold block_allocator_rep in *; cleanup.
    right; split; eauto.
    eapply H2; lia.
  }
Qed.

Theorem write_finished:
  forall dh u o s a v t s',
    block_allocator_rep dh (fst s) ->
    exec (TransactionalDiskLang data_length) u o s (write a v) (Finished s' t) ->
    ((t = Some tt /\
      block_allocator_rep (Mem.upd dh a v) (fst s')) \/
    (t = None /\ block_allocator_rep dh (fst s'))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst s' a = fst s a) /\
     snd s' = snd s.
Proof.
  unfold write; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia.
  {
    left; split; eauto.
    unfold block_allocator_rep in *; cleanup.
    simpl; do 2 eexists; intuition eauto.
    (** valid bits upd lemma **)
    admit.
    rewrite Mem.upd_ne; eauto; lia.
  }  
  all: simpl; rewrite upd_ne; eauto; lia.
Admitted.


(*** Crashed ***)
Theorem alloc_crashed:
  forall u o s s' own,
    exec (TransactionalDiskLang data_length) u o s (alloc own) (Crashed s') ->
     snd s' = snd s.
Proof.
  unfold alloc; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem free_crashed:
  forall u o s s' a,
    exec (TransactionalDiskLang data_length) u o s (free a) (Crashed s') ->
     snd s' = snd s.
Proof.
  unfold free; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem read_crashed:
  forall u o s s' a,
    exec (TransactionalDiskLang data_length) u o s (read a) (Crashed s') ->
     snd s' = snd s.
Proof.
  unfold read; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem write_crashed:
  forall u o s s' a v,
    exec (TransactionalDiskLang data_length) u o s (write a v) (Crashed s') ->
     snd s' = snd s.
Proof.
  unfold write; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

End BlockAllocator.


