Require Import Framework FSParameters TransactionalDiskLayer.
Require Import Arith Lia FunctionalExtensionality.
Import IfNotations.

Set Nested Proofs Allowed.

Notation "| p |" := (Op (TDCore data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (TDCore data_length) p1) (fun x => p2))(right associativity, at level 60).

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
  Parameter num_of_blocks_in_bounds: num_of_blocks <= bitmap_size.
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
  let bits := value_to_bits v in
  let index := get_first_zero_index bits in
  
  if lt_dec index num_of_blocks then
    r <-| Write (bitmap_addr + S index) v';
    if r is Some tt then
      r <-| Write bitmap_addr
        (bits_to_value (set_bit index bits));
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
  let bits := value_to_bits v in
  if test_bit a bits then
      | Write bitmap_addr (bits_to_value (unset_bit a bits))|
    else
      Ret None
  else
    Ret None.

(** No duplicates in l_a *)
Fixpoint free_bits_rec bits l_a:=
  match l_a with
  |[] => Some bits
  |a::l_a' =>
    if test_bit a bits then
      match free_bits_rec bits l_a' with
      |Some bits' => Some (unset_bit a bits')
      |None => None
      end
    else
      None
  end.

(** Takes index instead of data address. **) 
Definition free_all l_a :=
  v <-| Read bitmap_addr;
  let bits := value_to_bits v in
  if free_bits_rec bits l_a is Some bits' then
      | Write bitmap_addr (bits_to_value bits')|
  else
    Ret None.

(** Takes index instead of data address. **) 
Definition read a :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := value_to_bits v in
  if test_bit a bits then
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
  let bits := value_to_bits v in
  if test_bit a bits then
      | Write (bitmap_addr + S a) b|
    else
      Ret None
  else
    Ret None.


(*** Rep Invariants ***)
Fixpoint valid_bits' (dh: disk value) values bits n (d: @total_mem addr addr_dec value) :=
  match values with
  | v::values' =>
    d (bitmap_addr + S n) = v /\
    ((test_bit n bits = false /\ dh n = None) \/
    (test_bit n bits = true /\  dh n = Some v)) /\
    valid_bits' dh values' bits (S n) d
   | _ =>
     True
  end.
      
Definition valid_bits dh values bits := valid_bits' dh values bits 0.

Definition block_allocator_rep (dh: disk value) (d: @total_mem addr addr_dec value)  :=
  exists bitmap values,
     let bits := value_to_bits bitmap in
     d bitmap_addr = bitmap /\
     valid_bits dh values bits d /\
     length values = num_of_blocks /\
     (forall i, i >= num_of_blocks -> dh i = None /\ test_bit i bits = false).


(*** Lemmas ***)
Lemma valid_bits'_split:
  forall dh d a l1 l2 n,
    a < length l1 ->
    length l1 <= num_of_blocks ->
    valid_bits' dh l1 l2 n d ->
    valid_bits' dh (firstn a l1) l2 n d /\ valid_bits' dh (skipn a l1) l2 (n + a) d.
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r; eauto.
  destruct l1; simpl in *; try lia.
  cleanup.
  edestruct (IHa l1 l2 (S n)); eauto; try lia.   
  repeat split; eauto.
  rewrite <- Nat.add_succ_comm; eauto.
Qed.

Lemma valid_bits'_merge:
  forall dh d a l1 l2 n,
    a < length l1 ->
    length l1 <= num_of_blocks ->
    valid_bits' dh (firstn a l1) l2 n d /\ valid_bits' dh (skipn a l1) l2 (n + a) d ->
    valid_bits' dh l1 l2 n d.
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r in *; cleanup; eauto.
  destruct l1; simpl in *; try lia.
  cleanup.
  rewrite <- Nat.add_succ_comm in *.
  repeat split; eauto.
  eapply IHa; eauto; try lia.
Qed.


Lemma valid_bits_extract :
  forall dh values bits n d,
    n < length values ->
    length values <= num_of_blocks ->
    valid_bits dh values bits d ->
    d (bitmap_addr + S n) = seln values n value0 /\
    ((test_bit n bits = false /\ dh n = None) \/
    (test_bit n bits = true /\  dh n = Some (seln values n value0))).
Proof.
  intros.
  eapply valid_bits'_split in H1; eauto; simpl in *.
  destruct_fresh (skipn n values).
  - apply length_zero_iff_nil in D.
    rewrite skipn_length in D.
    lia.
  - simpl in *.
    cleanup.
    rewrite <- Nat.add_0_r with (n:= n).
    rewrite <- skipn_seln.
    rewrite Nat.add_0_r with (n:= n).
    rewrite D; simpl; eauto.
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
  forall s count n,
  count <= num_of_blocks ->
    valid_bits' empty_mem (map s (seq (bitmap_addr + S n) count)) zero_bitmap n s.
Proof.
  induction count; simpl; intros; eauto.
  intuition eauto.
  left; intuition; eauto.
  destruct (Compare_dec.lt_dec n bitmap_size). 
  apply zero_bitmap_empty; eauto.
  apply test_bit_oob; lia.
  rewrite <- Nat.add_succ_r; eauto.
  eapply IHcount; lia.
Qed.

Lemma valid_bits'_upd_before:
forall values bl dh s i v n,
valid_bits' dh values bl n s ->
i < n ->
valid_bits' (Mem.upd dh i v) values bl n s.
Proof.
  induction values; simpl; intros; eauto.
  simpl in *; try lia; cleanup.
  rewrite Mem.upd_ne; try lia.
  repeat (split; eauto).
Qed.

Lemma valid_bits'_state_upd_before:
forall values bl dh s i v n,
valid_bits' dh values bl n s ->
i <= n ->
valid_bits' dh values bl n (upd s (bitmap_addr + i) v).
Proof.
  induction values; simpl; intros; eauto.
  simpl in *; try lia; cleanup.
  rewrite upd_ne; try lia.
  repeat (split; eauto).
Qed.

Lemma valid_bits'_bitmap_set_before:
forall values bl dh s i n,
valid_bits' dh values bl n s ->
i < n ->
valid_bits' dh values (set_bit i bl) n (upd s bitmap_addr (bits_to_value (set_bit i bl))).
Proof.
  induction values; simpl; intros; eauto.
  simpl in *; try lia; cleanup.
  rewrite upd_ne; try lia.
  repeat (split; eauto).
  repeat rewrite set_test_ne; eauto; lia.
Qed.

(*
Lemma valid_bits'_bitlist_upd_after:
  forall values bl1 bl2 dh s n i,
  valid_bits' dh values bl1 n s ->
  i <= n ->
  bl1 = skipn i bl2 ->
  valid_bits' dh values bl1 n (upd s bitmap_addr (bits_to_value bl2)).
  Proof.
    induction values; simpl; intros; eauto.
    destruct bl1; simpl in *; try lia; cleanup.
    split.
    rewrite upd_ne; eauto; lia.
    repeat (split; eauto).
    eapply IHvalues.
    eauto.
    instantiate (1:= S i); lia.
    clear H0 H2 H3. 
    generalize dependent bl1.
    generalize dependent bl2.
    generalize dependent b.
    generalize dependent i.
    induction i; intros; cleanup; eauto.
    simpl in *; cleanup; try congruence.
    destruct bl2; simpl in *; try congruence.
    eauto.

  Qed.

  Lemma valid_bits'_bitlist_upd_after_rev:
  forall values bl1 bl2 dh s n i,
  valid_bits' dh values bl1 n (upd s bitmap_addr (bits_to_value bl2)) ->
  i <= n ->
  bl1 = skipn i bl2 ->
  valid_bits' dh values bl1 n s.
  Proof.
    induction values; simpl; intros; eauto.
    destruct bl1; simpl in *; try lia; cleanup.
    split.
    rewrite upd_ne; eauto; lia.
    repeat (split; eauto).
    eapply IHvalues.
    eauto.
    instantiate (1:= S i); lia.
    clear H0 H2 H3. 
    generalize dependent bl1.
    generalize dependent bl2.
    generalize dependent b.
    generalize dependent i.
    induction i; intros; cleanup; eauto;
    try solve [ simpl in *; congruence];
    simpl in *;
    destruct bl2; try congruence. 
    eauto.
  Qed.



  Lemma valid_bits'_bitlist_upd_after_2:
  forall values bl1 bl2 dh s n i,
  valid_bits' dh values bl1 n (upd s bitmap_addr (bits_to_value bl1)) ->
  i <= n ->
  bl1 = skipn i bl2 ->
  valid_bits' dh values bl1 n (upd s bitmap_addr (bits_to_value bl2)).
  Proof.
    induction values; simpl; intros; eauto.
    destruct bl1; simpl in *; try lia; cleanup.
    split.
    repeat rewrite upd_ne; eauto; lia.
    repeat (split; eauto).
    eapply IHvalues.
    eapply valid_bits'_bitlist_upd_after_rev.
    rewrite upd_repeat.
    eauto.
    instantiate (1:= 1); lia.
    rewrite <- H1; simpl; eauto.
    instantiate (1:= S i); lia.
    clear H0 H2 H3. 
    generalize dependent bl1.
    generalize dependent bl2.
    generalize dependent b.
    generalize dependent i.
    induction i; simpl; intros; cleanup; eauto.
    try congruence.
    simpl in *; eauto.
  Qed.
  *)
  Lemma valid_bits'_upd_values_empty:
  forall values bl1 i dh s n v,
  valid_bits' dh values bl1 n s ->
  test_bit (n + i) bl1 = false -> 
  valid_bits' dh (updn values i v) bl1 n (upd s (bitmap_addr + S n + i) v).
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.
    destruct i; simpl; eauto.

    {
    split_ors; cleanup; try congruence.
    simpl.
    repeat rewrite Nat.add_0_r in *.
    repeat rewrite upd_eq; eauto. 
    repeat (split; eauto).
    eapply valid_bits'_state_upd_before; eauto.
    simpl.
    repeat rewrite Nat.add_0_r in *.
    congruence.
    }

    simpl.
    repeat rewrite upd_ne; eauto; try lia. 
    repeat (split; eauto).
    replace (bitmap_addr + S n + S i) 
    with (bitmap_addr + S (S n) + i) by lia.
    eapply IHvalues; eauto.
    rewrite Nat.add_succ_comm; eauto. 
  Qed.


  Lemma valid_bits'_upd_values_allocated:
  forall values bl1 dh s n i v,
  valid_bits' dh values bl1 n s ->
  test_bit (n + i) bl1 = true -> 
  valid_bits' (Mem.upd dh (n + i) v) (updn values i v) bl1 n (upd s (bitmap_addr + S n + i) v).
  Proof.
    induction values; simpl; intros; eauto.
    destruct i; simpl in *; try lia; cleanup;
    try congruence.

    {
      split_ors; cleanup; try congruence.
      simpl.
      repeat rewrite Nat.add_0_r in *.
      congruence.
      simpl.
      repeat rewrite Nat.add_0_r in *.
      repeat rewrite upd_eq; 
      repeat rewrite Mem.upd_eq;eauto. 
      repeat (split; eauto).
      eapply valid_bits'_state_upd_before; eauto.
      eapply valid_bits'_upd_before; eauto.
    }

    {
      simpl.
      repeat rewrite upd_ne; 
      repeat rewrite Mem.upd_ne; eauto; try lia. 
      repeat (split; eauto).
      rewrite <- Nat.add_succ_comm.
      replace (bitmap_addr + S n + S i) 
      with (bitmap_addr + S (S n) + i) by lia.
      eapply IHvalues; eauto.
      rewrite Nat.add_succ_comm; eauto. 
    } 
  Qed.

  Lemma valid_bits'_bitlist_upd_noop:
  forall values bl1 dh s n,
  valid_bits' dh values bl1 n s ->
  valid_bits' dh values bl1 n (upd s bitmap_addr (bits_to_value bl1)).
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.
    split.
    rewrite upd_ne; eauto; lia.
    repeat (split; eauto).
  Qed.

  Lemma valid_bits'_delete_before:
  forall values bl1 dh s n i,
  valid_bits' dh values bl1 n s ->
  i < n ->
  valid_bits' (delete dh i) values bl1 n s.
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.
    repeat rewrite delete_ne; try lia.
    repeat (split; eauto).
  Qed. 

  Lemma valid_bits'_delete_before_set:
  forall values bl1 dh s n i,
  valid_bits' dh values bl1 n s ->
  i < n ->
  valid_bits' (delete dh i) values (set_bit i bl1) n (upd s bitmap_addr
  (bits_to_value (set_bit i bl1))).
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.
    repeat rewrite delete_ne; try lia.
    repeat rewrite upd_ne; try lia.
    repeat (split; eauto).
    rewrite set_test_ne; try lia.
    eauto.
  Qed. 

  Lemma valid_bits'_delete_before_unset:
  forall values bl1 dh s n i,
  valid_bits' dh values bl1 n s ->
  i < n ->
  valid_bits' (delete dh i) values (unset_bit i bl1) n (upd s bitmap_addr
  (bits_to_value (unset_bit i bl1))).
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.
    repeat rewrite delete_ne; try lia.
    repeat rewrite upd_ne; try lia.
    repeat (split; eauto).
    rewrite unset_test_ne; try lia.
    eauto.
  Qed. 

  Lemma valid_bits'_delete:
  forall values bl1 dh s n i,
  valid_bits' dh values bl1 n s ->
  valid_bits' (delete dh (n + i)) values (unset_bit (n + i) bl1) n 
    (upd s bitmap_addr (bits_to_value (unset_bit (n + i) bl1))).
  Proof.
    induction values; simpl; intros; eauto.
    simpl in *; try lia; cleanup.

    rewrite upd_ne; eauto; try lia.
    destruct i.
    {
      repeat rewrite Nat.add_0_r in *.
    repeat rewrite delete_eq; try lia.
    destruct (Compare_dec.lt_dec n bitmap_size). 
    repeat rewrite unset_test_eq; eauto.
    repeat (split; eauto).
    apply valid_bits'_delete_before_unset; eauto.
    rewrite test_bit_oob; try lia.
    repeat (split; eauto).
    apply valid_bits'_delete_before_unset; eauto.
    }
    {
      repeat rewrite delete_ne; try lia.
    rewrite unset_test_ne; try lia.
    repeat (split; eauto).
    repeat rewrite <- Nat.add_succ_comm.
    eapply IHvalues; eauto.
    }
  Qed.

Lemma valid_bits'_upd:
forall values bl dh s i v n,
valid_bits' dh values bl n s ->
length values <= num_of_blocks ->
n + i < bitmap_size ->
valid_bits' (Mem.upd dh (n + i) v) (updn values i v) (set_bit (n + i) bl) n
(upd (upd s (bitmap_addr + S n + i) v) bitmap_addr (bits_to_value (set_bit (n + i) bl))).
Proof.
  induction values; simpl; intros; eauto.
  simpl in *; try lia; cleanup.
  destruct i; simpl in *.
  {
    repeat rewrite Nat.add_0_r in *.
    split; [rewrite upd_ne; try lia; apply upd_eq; eauto |].
    split; 
    [right; split; eauto |].
    apply set_test_eq; eauto.
    apply Mem.upd_eq; eauto.
    eapply valid_bits'_bitmap_set_before; eauto.
    eapply valid_bits'_upd_before; eauto.
    eapply valid_bits'_state_upd_before; eauto.
  }
  {
    split; [repeat rewrite upd_ne; try lia; eauto |].
    split; 
    [ repeat rewrite Mem.upd_ne; repeat rewrite set_test_ne; eauto; try lia |].
    do 2 rewrite <- Nat.add_succ_comm.
    repeat rewrite <- Nat.add_succ_r.
    apply IHvalues; eauto; try lia.
  }
Qed.

Lemma valid_bits_upd:
forall values bl dh s i v,
valid_bits dh values bl s ->
length values <= num_of_blocks ->
i < bitmap_size -> 
valid_bits (Mem.upd dh i v) (updn values i v) (set_bit i bl) 
(upd (upd s (bitmap_addr + S i) v) bitmap_addr (bits_to_value (set_bit i bl))).
Proof.
  unfold valid_bits; intros.
  eapply valid_bits'_upd in H; eauto.
  simpl in *.
  replace (bitmap_addr + S i)  with (bitmap_addr + 1 + i) by lia.
  eauto.
Qed.
(*
Lemma get_first_zero_index_lt_true:
forall l_b i, 
i < get_first_zero_index l_b -> 
nth i l_b false = true.
Proof.
  induction l_b; simpl; intros; eauto.
  lia.
  destruct a; try lia.
  destruct i; eauto.
  eapply IHl_b; lia.
Qed.
*)
Lemma block_allocator_rep_eq:
  forall dh1 dh2 s,
    block_allocator_rep dh1 s ->
    block_allocator_rep dh2 s ->
    dh1 = dh2.
Proof.
  unfold block_allocator_rep; intros; extensionality x.
  cleanup.
  destruct (le_dec num_of_blocks x); eauto.
  edestruct H6; edestruct H3; eauto; congruence.
  eapply (valid_bits_extract _ _ _ x) in H4; try lia; cleanup.
  eapply (valid_bits_extract _ _ _ x) in H1; try lia; cleanup.
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
  edestruct H3; eauto.
  rewrite H0; eauto; try lia.
  edestruct H3; eauto.
Qed.

Lemma block_allocator_rep_upd:
forall x4 t0 a v1,
block_allocator_rep x4 t0 ->
test_bit a (value_to_bits (t0 bitmap_addr)) = true ->
a < num_of_blocks ->
block_allocator_rep (Mem.upd x4 a v1)
(upd t0 (bitmap_addr + S a) v1).
Proof.
  unfold block_allocator_rep; intros.
  cleanup.
  exists (t0 bitmap_addr), (updn x0 a v1).
  intuition eauto.
  rewrite upd_ne; eauto; lia.
  setoid_rewrite <- Nat.add_0_l in H0.
  eapply valid_bits'_upd_values_allocated in H0.
  simpl in *; eauto.
  replace (bitmap_addr + S a) with (bitmap_addr + 1 + a) by lia.
  eauto.
  simpl; eauto.
  rewrite updn_length; eauto.
  rewrite Mem.upd_ne; eauto; try lia.
  edestruct H4; eauto.
  edestruct H4; eauto.
Qed.

Lemma block_allocator_rep_upd_noop:
forall x4 t0 a v1,
block_allocator_rep x4 t0 ->
a < bitmap_addr \/ a > bitmap_addr + num_of_blocks ->
block_allocator_rep x4
(upd t0 a v1).
Proof.
  intros.
  eapply block_allocator_rep_inbounds_eq; eauto.
  intros; cleanup.
  rewrite upd_ne; eauto. 
  intuition.
Qed.


Lemma block_allocator_rep_delete :
  forall bm s a,
  block_allocator_rep bm s ->
  block_allocator_rep (Mem.delete bm a) 
  (upd s bitmap_addr 
  (bits_to_value (unset_bit a (value_to_bits (s bitmap_addr))))).
  Proof.
    intros.
    unfold block_allocator_rep in *; cleanup.
    simpl; do 2 eexists; intuition eauto.
    {
      rewrite upd_eq; eauto.
      rewrite bits_to_value_to_bits.
      unfold valid_bits in *.
      eapply valid_bits'_delete in H0; simpl in *; eauto.
    }
    destruct (PeanoNat.Nat.eq_dec a i); subst.
    rewrite delete_eq; eauto.
    rewrite delete_ne; eauto; try lia.
    edestruct H2; eauto.
    edestruct H2; eauto.
    rewrite upd_eq; eauto.
    rewrite bits_to_value_to_bits.
    destruct (lt_dec a bitmap_size).
    destruct (Nat.eq_dec i a); subst.
    apply unset_test_eq; eauto.
    rewrite unset_test_ne; eauto.
    destruct (Nat.eq_dec i a); subst.
    rewrite test_bit_oob; eauto.
    lia.
    rewrite unset_test_ne; eauto.
  Qed.

  Lemma repeated_apply_unset_bit_comm:
  forall l a bm,
  unset_bit a (repeated_apply (fun l a => unset_bit a l) bm l) =
  repeated_apply (fun l a => unset_bit a l) (unset_bit a bm) l.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite <- IHl.
    rewrite unset_bit_comm; eauto.
  Qed.



  Lemma block_allocator_rep_delete_list :
  forall (l_a: list addr) (bm: @mem addr addr_dec value) s,
    block_allocator_rep bm s ->
    NoDup l_a ->
  block_allocator_rep (repeated_apply (@Mem.delete addr value addr_dec) bm l_a) 
  (upd s bitmap_addr 
  (bits_to_value (repeated_apply (fun l a => unset_bit a l) (value_to_bits (s bitmap_addr)) l_a))).
  Proof.
    induction l_a; simpl; intros; eauto.
    {
      rewrite value_to_bits_to_value.
      rewrite upd_nop; eauto.
    }
    {
      inversion H0; clear H0; cleanup.
      rewrite repeated_apply_delete_comm, repeated_apply_unset_bit_comm; eauto.
      eapply block_allocator_rep_delete with (a:= a) in H.
      eapply IHl_a in H; eauto.
      rewrite upd_eq in H; eauto.
      rewrite upd_repeat in H; eauto.
      rewrite bits_to_value_to_bits in H; eauto.
    }
  Qed.

(*** Specs ***)
Theorem alloc_finished:
  forall dh u o s v t s',
    block_allocator_rep dh (fst (snd s)) ->
    exec (TDLang data_length) u o s (alloc v) (Finished s' t) ->
    ((exists a, t = Some a /\
           dh a = None /\
           a < num_of_blocks /\
           (forall i, i < a -> dh i <> None ) /\ 
          block_allocator_rep (Mem.upd dh a v) (fst (snd s'))) \/
     (t = None /\ block_allocator_rep dh (fst (snd s')))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst (snd s') a = fst (snd s) a) /\
     snd (snd s') = snd (snd s).
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
       instantiate (1:= (get_first_zero_index (value_to_bits (fst (snd x1) bitmap_addr)))) in Hx.
       logic_clean.      
       {
         rewrite nth_seln_eq in *.
         edestruct get_first_zero_index_correct.
         erewrite H6 in H5; eauto.
         split_ors; cleanup; try congruence.
         left; eexists; intuition eauto.
         eapply valid_bits_extract with (n:= i) in H0; try lia.
         cleanup.
         split_ors; cleanup.
         rewrite H7 in H12; eauto; congruence.

         eexists; 
         exists (updn x0 (get_first_zero_index
         (value_to_bits (fst (snd x1) bitmap_addr))) v).
         intuition eauto.
        
         {
          rewrite upd_eq; eauto.
          rewrite bits_to_value_to_bits.
          eapply valid_bits_upd; eauto.
          all: try rewrite updn_length;
          repeat rewrite value_to_bits_length; lia. 
         }  
          {
            rewrite updn_length; eauto.
          }
         clear D.
         rewrite Mem.upd_ne; eauto.
          edestruct H4; eauto.
         lia.
         rewrite upd_eq.
         rewrite bits_to_value_to_bits.
         rewrite set_test_ne; eauto.
         edestruct H4; eauto.
         lia.
         eauto.
         lia.         
       }
       rewrite H3; eauto.
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
       instantiate (1:= (get_first_zero_index (value_to_bits (fst (snd x1) bitmap_addr)))) in Hx.
       logic_clean.      
       {
         rewrite nth_seln_eq in *.
         edestruct get_first_zero_index_correct.
         erewrite H6 in H5; eauto.
         split_ors; cleanup; try congruence.
         right; eexists; intuition eauto.
         
         eexists; 
         exists (updn x0 (get_first_zero_index (value_to_bits (fst (snd x1) bitmap_addr))) v).
         do 2 eexists; intuition eauto.
         {
          rewrite upd_ne; eauto; try lia.
          unfold valid_bits in *.
          replace (bitmap_addr +
          S (get_first_zero_index (value_to_bits (fst (snd x1) bitmap_addr))))
          with (bitmap_addr + 1 +
          (get_first_zero_index (value_to_bits (fst (snd x1) bitmap_addr)))) by lia.
          eapply valid_bits'_upd_values_empty; eauto.
          simpl; apply H6; eauto.
          lia.
         }
         {
            rewrite updn_length; eauto.
         }
         edestruct H4; eauto.
         rewrite upd_ne.
         edestruct H4; eauto.
         lia.
         lia.
       }
       rewrite H3; eauto.
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
Qed.
       
Theorem free_finished:
  forall dh u o s a t s',
    block_allocator_rep dh (fst (snd s)) ->
    exec (TDLang data_length) u o s (free a) (Finished s' t) ->
    ((t = Some tt /\
       block_allocator_rep (Mem.delete dh a) (fst (snd s'))) \/
    (t = None /\ block_allocator_rep dh (fst (snd s')))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst (snd s') a = fst (snd s) a) /\
     snd (snd s') = snd (snd s).
Proof.
  unfold free; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia.
  {
    left; split; eauto.
    unfold block_allocator_rep in *; cleanup.
    simpl; do 2 eexists; intuition eauto.
    {
      rewrite upd_eq; eauto.
      rewrite bits_to_value_to_bits.
      unfold valid_bits in *.
      eapply valid_bits'_delete in H0; simpl in *; eauto.
    }
    rewrite delete_ne; eauto; try lia.
    edestruct H2; eauto.
    erewrite upd_eq; eauto.
    rewrite bits_to_value_to_bits; eauto.
    destruct (PeanoNat.Nat.eq_dec a i); subst.
    lia.
    rewrite unset_test_ne; eauto.
    edestruct H2; eauto.
  }
  all: simpl; rewrite upd_ne; eauto; lia.
Qed.

Theorem read_finished:
  forall dh u o s a t s',
    block_allocator_rep dh (fst (snd s)) ->
    exec (TDLang data_length) u o s (read a) (Finished s' t) ->
    ((exists v, t = Some v /\ dh a = Some v) \/
     (t = None /\ dh a = None)) /\
    block_allocator_rep dh (fst (snd s')) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst (snd s') a = fst (snd s) a) /\
    snd (snd s') = snd (snd s) /\
    fst s' = fst s.
Proof.
  unfold read; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia;
  try solve [ pose proof blocks_fit_in_disk; lia ].
  {
    left; eexists; intuition eauto.
    unfold block_allocator_rep in *; cleanup.
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    split_ors; cleanup; eauto.
    congruence.
  }
  {
    unfold block_allocator_rep in *; cleanup.    
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    split_ors; cleanup; eauto.
    congruence.
  }
  {
    unfold block_allocator_rep in *; cleanup.
    right; split; eauto.
    eapply H2; lia.
  }
Qed.

Theorem read_finished_precise:
  forall dh u o s a t s',
    block_allocator_rep dh (fst (snd s)) ->
    exec (TDLang data_length) u o s (read a) (Finished s' t) ->
    ((exists v, t = Some v /\ dh a = Some v) \/
     (t = None /\ dh a = None)) /\
     s' = s.
Proof.
  unfold read; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia;
  try solve [ pose proof blocks_fit_in_disk; lia ].
  {
    left; eexists; intuition eauto.
    unfold block_allocator_rep in *; cleanup.
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    split_ors; cleanup; eauto.
    congruence.
  }
  {
    unfold block_allocator_rep in *; cleanup.    
    eapply (valid_bits_extract _ _ _ a) in H0; try lia.
    cleanup.
    split_ors; cleanup; eauto.
    congruence.
  }
  {
    unfold block_allocator_rep in *; cleanup.
    right; split; eauto.
    eapply H2; lia.
  }
Qed.



Theorem write_finished:
  forall dh u o s a v t s',
    block_allocator_rep dh (fst (snd s)) ->
    exec (TDLang data_length) u o s (write a v) (Finished s' t) ->
    ((t = Some tt /\
      block_allocator_rep (Mem.upd dh a v) (fst (snd s'))) \/
    (t = None /\ block_allocator_rep dh (fst (snd s')))) /\
    (forall a, a < bitmap_addr \/ a > bitmap_addr + num_of_blocks -> fst (snd s') a = fst (snd s) a) /\
     snd (snd s') = snd (snd s).
Proof.
  unfold write; intros; simpl in *.
  cleanup; repeat invert_exec; cleanup; intuition eauto; try lia.
  {
    left; split; eauto.
    unfold block_allocator_rep in *; cleanup.
    simpl; eexists; 
    exists (updn x0 a v).
    intuition eauto.
    {
      rewrite upd_ne; eauto; try lia.
      unfold valid_bits in *.
      eapply valid_bits'_upd_values_allocated in H0; simpl in *.
      replace (bitmap_addr + S a)
      with (bitmap_addr + 1 + a) by lia; eauto.
      eauto.
    }
    rewrite updn_length; eauto.
       rewrite Mem.upd_ne; eauto; try lia.
    edestruct H2; eauto.
    rewrite upd_ne; eauto.
    edestruct H2; eauto.
    lia.
  }  
  all: simpl; rewrite upd_ne; eauto; lia.
Qed.


(*** Crashed ***)
Theorem alloc_crashed:
  forall u o s s' own,
    exec (TDLang data_length) u o s (alloc own) (Crashed s') ->
     snd (snd s') = snd (snd s).
Proof.
  unfold alloc; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem free_crashed:
  forall u o s s' a,
    exec (TDLang data_length) u o s (free a) (Crashed s') ->
     snd (snd s') = snd (snd s).
Proof.
  unfold free; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem read_crashed:
  forall u o s s' a,
    exec (TDLang data_length) u o s (read a) (Crashed s') ->
     snd (snd s') = snd (snd s).
Proof.
  unfold read; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.

Theorem write_crashed:
  forall u o s s' a v,
    exec (TDLang data_length) u o s (write a v) (Crashed s') ->
     snd (snd s') = snd (snd s).
Proof.
  unfold write; intros;
  repeat (cleanup; repeat invert_exec; eauto;
  try split_ors).
Qed.


Lemma read_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 inum inum',
exec (TDLang FSParameters.data_length) 
u o s1 (read inum)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TDLang FSParameters.data_length) 
u o' s2 (read inum')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
unfold not, read.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup; split; eauto;
intuition congruence]).
Qed.

Lemma write_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 inum inum' v v',
exec (TDLang FSParameters.data_length) 
u o s1 (write inum v)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TDLang FSParameters.data_length) 
u o' s2 (write inum' v')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
unfold not, write.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec; try lia;
try solve [simpl in *; cleanup; split; eauto;
intuition congruence]).
all: pose proof blocks_fit_in_disk; lia.
Qed.

Lemma alloc_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 v v',
exec (TDLang FSParameters.data_length) 
u o s1 (alloc v)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TDLang FSParameters.data_length) 
u o' s2 (alloc v')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
unfold not, alloc.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec; try lia;
try solve [simpl in *; cleanup; split; eauto;
intuition congruence]).
Qed.

Lemma free_finished_oracle_eq:
forall u o o' o1 o2 s1 s2 s1' s2' r1 r2 a a',
exec (TDLang FSParameters.data_length) 
u o s1 (free a)
(Finished s1' r1) ->
o ++ o1 = o' ++ o2 ->
exec (TDLang FSParameters.data_length) 
u o' s2 (free a')
(Finished s2' r2) ->
o = o' /\ (r1 = None <-> r2 = None).
Proof.
unfold not, free.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec; try lia;
try solve [simpl in *; cleanup; split; eauto;
intuition congruence]).
Qed.



Lemma read_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r inum inum',
exec (TDLang FSParameters.data_length) 
u o s1 (read inum)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TDLang FSParameters.data_length) 
u o' s2 (read inum')
(Crashed s2').
Proof.
unfold not, read.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]).
Qed.

Lemma write_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r inum inum' v v',
exec (TDLang FSParameters.data_length) 
u o s1 (write inum v)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TDLang FSParameters.data_length) 
u o' s2 (write inum' v')
(Crashed s2').
Proof.
unfold not, write.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]).
Qed.

Lemma alloc_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r v v',
exec (TDLang FSParameters.data_length) 
u o s1 (alloc v)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TDLang FSParameters.data_length) 
u o' s2 (alloc v')
(Crashed s2').
Proof.
unfold not, alloc.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]).
Qed.

Lemma free_finished_not_crashed:
forall u o o' o1 o2 s1 s2 s1' s2' r v v',
exec (TDLang FSParameters.data_length) 
u o s1 (free v)
(Finished s1' r) ->
o ++ o1 = o' ++ o2 ->
~exec (TDLang FSParameters.data_length) 
u o' s2 (free v')
(Crashed s2').
Proof.
unfold not, free.
intros.
cleanup; repeat invert_exec;
repeat (try split_ors; cleanup; repeat invert_exec;
try solve [simpl in *; cleanup]).
Qed.

End BlockAllocator.


