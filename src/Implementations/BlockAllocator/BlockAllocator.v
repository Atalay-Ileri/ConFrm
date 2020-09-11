Require Import Framework FSParameters TransactionalDiskLayer.
Require Import Arith Lia.
Import IfNotations.
Close Scope predicate_scope.

Set Nested Proofs Allowed.

Notation "| p |" := (Op (TransactionalDiskOperation data_length) p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op (TransactionalDiskOperation data_length) p1) (fun x => p2))(right associativity, at level 60). 

Definition valid_bitlist l := length l = block_size /\ (forall i, In i l -> i < 2).

Record bitlist :=
  {
   bits : list nat;                
   valid : valid_bitlist bits
  }.

Fixpoint get_first_zero l :=
  match l with
  | nil => 0
  | hd::tl =>
    match hd with
    | O => 0
    | _ => S (get_first_zero tl)
    end
  end.

Theorem upd_valid_zero:
  forall i l,
    valid_bitlist l ->
    valid_bitlist (updN l i 0).
Proof.
  unfold valid_bitlist in *; intros; cleanup.
  rewrite length_updN; intuition.
  apply in_updN in H1; intuition; eauto.
Qed.

Theorem upd_valid_one:
  forall i l,
    valid_bitlist l ->
    valid_bitlist (updN l i 1).
Proof.
  unfold valid_bitlist in *; intros; cleanup.
  rewrite length_updN; intuition.
  apply in_updN in H1; intuition; eauto.
Qed.

Axiom value_to_bits: value -> bitlist.
Axiom bits_to_value: bitlist -> value.
Axiom value_to_bits_to_value : forall v, bits_to_value (value_to_bits v) = v.
Axiom bits_to_value_to_bits : forall l, value_to_bits (bits_to_value l) = l.   

Module Type BlockAllocatorParameters.
  Parameter bitmap_addr: addr.
  Parameter num_of_blocks: nat.
  Parameter num_of_blocks_in_bounds: num_of_blocks <= block_size.
  Parameter blocks_fit_in_disk: bitmap_addr + num_of_blocks < data_length.
End BlockAllocatorParameters.
  
(* This is a generic block allocator which has a 1 block bitmap and num_of_blocks blocks following it *)  
Module BlockAllocator (Params : BlockAllocatorParameters).

Import Params.
  
Definition alloc (v': value) :=
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  let index := get_first_zero (firstn num_of_blocks bits) in
  
  if lt_dec index num_of_blocks then
    _ <-| Write (S index) v';
    _ <-| Write bitmap_addr
      (bits_to_value (Build_bitlist (updN bits index 1)
                     (upd_valid_one index bits valid)));
    Ret (Some index)
  else
    Ret None.

Definition free a :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some 1 then
      _ <-| Write bitmap_addr (bits_to_value (Build_bitlist (updN bits a 0) (upd_valid_zero a bits valid)));
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Definition read a :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some 1 then
      v <-| Read (S a);
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Definition write a b :=
  if lt_dec a num_of_blocks then
  v <-| Read bitmap_addr;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if nth_error bits a is Some 1 then
      _ <-| Write (S a) b;
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Open Scope predicate_scope.
  
Fixpoint ptsto_bits' (dh: disk value) values bits n : @predicate addr addr_dec value :=
  match values, bits with
  | v::values', b::bits' =>
    (S n) |-> v *
    match b with
    | 0 => [[ dh n = None ]]
    | 1 => [[ dh n = Some v ]]
    | _ => [[ False ]]
    end *
    ptsto_bits' dh values' bits' (S n)
   | _, _ =>
    emp
  end.
      
Definition ptsto_bits dh values bits := ptsto_bits' dh values bits 0.

Definition block_allocator_rep (dh: disk value) : @predicate addr addr_dec value  :=
  (exists* bitmap values,
     let bits := bits (value_to_bits bitmap) in
     bitmap_addr |-> bitmap *
     ptsto_bits dh values bits *
     [[ length values = num_of_blocks ]] *
     [[ forall i, i >= num_of_blocks -> dh i = None ]])%predicate.

Lemma ptsto_bits'_split:
  forall dh a l1 l2 n,
    a < length l1 ->
    length l1 <= length l2 ->
    ptsto_bits' dh l1 l2 n =*=> ptsto_bits' dh (firstn a l1) (firstn a l2) n * ptsto_bits' dh (skipn a l1) (skipn a l2) (n + a).
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r; eauto.
  cancel.
  destruct l1; simpl in *; try lia.
  destruct l2; simpl in *; try lia.
  cancel.
  rewrite <- Nat.add_succ_comm.
  eapply IHa; lia.
Qed.

Lemma ptsto_bits'_merge:
  forall dh a l1 l2 n,
    a < length l1 ->
    length l1 <= length l2 ->
    ptsto_bits' dh (firstn a l1) (firstn a l2) n * ptsto_bits' dh (skipn a l1) (skipn a l2) (n + a) =*=>
    ptsto_bits' dh l1 l2 n.
Proof.
  induction a; simpl; intros; eauto.
  rewrite Nat.add_0_r; eauto.
  cancel.
  destruct l1; simpl in *; try lia.
  destruct l2; simpl in *; try lia.
  cancel.
  rewrite <- Nat.add_succ_comm.
  eapply pimpl_trans; [| eapply IHa; lia].
  cancel.  
Qed.

Lemma ptsto_bits_extract :
  forall dh values bits n,
    n < length values ->
    length values <= length bits ->
    ptsto_bits dh values bits =*=> (S n |-> (selN values n value0) --* ptsto_bits dh values bits) * (S n |-> (selN values n value0)).
Proof.
  intros.
  eapply septract_sep_star_extract.
  unfold ptsto_bits.
  intros m Hm.
  eapply ptsto_bits'_split in Hm; eauto; simpl in *.
  destruct_fresh (skipn n values).
  - apply length_zero_iff_nil in D.
    rewrite skipn_length in D.
    lia.
  - destruct_fresh (skipn n bits0).
    apply length_zero_iff_nil in D0.
    rewrite skipn_length in D0.
    lia.
    simpl in *.
    pred_apply; cancel. 
   
    rewrite <- Nat.add_0_r with (n:= n).
    rewrite <- skipn_selN.
    rewrite Nat.add_0_r with (n:= n).
    rewrite D; simpl.
    cancel.
    eexists; pred_apply; cancel.
Qed.


(** Specs **)
(*
Open Scope predicate_scope.
Theorem alloc_ok:
  forall dh v t s' F,
    (* (F * block_allocator_rep dh)%predicate m -> *)
    strongest_postcondition (TransactionalDiskLang data_length) (alloc v)
                            (fun o s => (F * block_allocator_rep dh)%predicate (mem_union (fst s) (snd s)) /\
                                     (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists a, t = Some a /\ dh a = None /\ (F * block_allocator_rep (upd dh a v))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * block_allocator_rep dh)%predicate (mem_union (fst s') (snd s'))).
Proof. (*
  unfold block_allocator_rep; simpl; intros.
  pose proof num_of_blocks_in_bounds.
  pose proof blocks_fit_in_disk.
  repeat (cleanup; simpl in * ).
  repeat (split_ors; cleanup; simpl in * ); try lia;
  try solve [ unfold not in *; exfalso; eapply H10; [| eauto]; eauto].
                  
  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
    eapply pimpl_trans; [| eauto | eapply ptsto_upd].
    2: {
      eapply sep_star_assoc.
      apply sep_star_comm.
      eapply ptsto_upd.
      apply sep_star_comm.
      eapply sep_star_assoc.
      pred_apply; cancel.
      apply ptsto_bits_extract.
      lia.
      destruct (value_to_bits x); simpl in *.
      unfold valid_bitlist in *; cleanup.
      apply num_of_blocks_in_bounds.
    }
    cancel.
    rewrite bits_to_value_to_bits; simpl.
    instantiate (1:= updN x1 (get_first_zero (firstn num_of_blocks (bits (value_to_bits x0)))) v).
    admit. (* Separation logic goal *)
    rewrite length_updN; eauto.
    rewrite upd_ne; eauto.
    lia.

  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
    eapply pimpl_trans; [| eauto | eapply ptsto_upd].
    2: {
      eapply sep_star_assoc.
      apply sep_star_comm.
      eapply ptsto_upd.
      apply sep_star_comm.
      eapply sep_star_assoc.
      pred_apply; cancel.
      apply ptsto_bits_extract.
      lia.
      destruct (value_to_bits x); simpl in *.
      unfold valid_bitlist in *; cleanup.
      apply num_of_blocks_in_bounds.
    }
    cancel.
    rewrite bits_to_value_to_bits; simpl.
    instantiate (1:= updN x1 (get_first_zero (firstn num_of_blocks (bits (value_to_bits x0)))) v).
    admit. (* Separation logic goal *)
    rewrite length_updN; eauto.
    rewrite upd_ne; eauto.
    lia.
    
  -
    split_ors; cleanup; try lia.
    right; intuition eauto.
    *)
Admitted.


Theorem free_ok:
  forall dh a t s' F,
    strongest_postcondition (TransactionalDiskLang data_length) (free a)
                            (fun o s => (F * block_allocator_rep dh)%predicate (mem_union (fst s) (snd s)) /\
                                     (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (t = Some tt /\ (F * block_allocator_rep (delete dh a))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * block_allocator_rep dh)%predicate (mem_union (fst s') (snd s'))).
Proof. (*
  unfold block_allocator_rep; simpl; intros.
  pose proof num_of_blocks_in_bounds.
  pose proof blocks_fit_in_disk.
  unfold free in *.
  repeat (cleanup; simpl in * ); try lia;
  repeat (split_ors; cleanup; simpl in * ); try lia;
  try solve [ unfold not in *; exfalso; eapply H8; [| eauto]; eauto];
  try solve [ unfold not in *; exfalso; eapply H9; [| eauto]; eauto];
  try solve [right; intuition eauto].
          
  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
    eapply ptsto_upd in H.
    pred_apply' H.
    cancel.
    rewrite bits_to_value_to_bits; simpl.
    instantiate (1:= x1).
    admit. (* Separation logic goal *)
    eauto.
    unfold delete.
    destruct (addr_dec i a); eauto.

  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
    eapply ptsto_upd in H.
    pred_apply' H.
    cancel.
    rewrite bits_to_value_to_bits; simpl.
    instantiate (1:= x1).
    admit. (* Separation logic goal *)
    eauto.
    unfold delete.
    destruct (addr_dec i a); eauto.
*)
Admitted.


Theorem read_ok:
  forall dh a t s' F,
    strongest_postcondition (TransactionalDiskLang data_length) (read a)
                            (fun o s => (F * block_allocator_rep dh)%predicate (mem_union (fst s) (snd s))) t s' ->
    (t = dh a /\ (F * block_allocator_rep dh)%predicate (mem_union (fst s') (snd s'))).
Proof. (*
  unfold block_allocator_rep; simpl; intros.
  pose proof num_of_blocks_in_bounds.
  pose proof blocks_fit_in_disk.
  unfold read in *.
  repeat (cleanup; simpl in * ); try lia;
  repeat (split_ors; cleanup; simpl in * ); eauto; try lia.
*)
Admitted.


Theorem write_ok:
  forall dh a v t s' F,
    strongest_postcondition (TransactionalDiskLang data_length) (write a v)
                            (fun o s => (F * block_allocator_rep dh)%predicate (mem_union (fst s) (snd s)) /\
                                     (forall tok, In tok o -> tok <> OpOracle (TransactionalDiskOperation data_length) [TxnFull])%list ) t s' ->
    (exists v', dh a = Some v' /\ t = Some tt /\ (F * block_allocator_rep (upd dh a v))%predicate (mem_union (fst s') (snd s'))) \/
    (t = None /\ (F * block_allocator_rep dh)%predicate (mem_union (fst s') (snd s'))).
Proof. (*
  unfold block_allocator_rep; simpl; intros.
  pose proof num_of_blocks_in_bounds.
  pose proof blocks_fit_in_disk.
  unfold write in *.
  repeat (cleanup; simpl in * ); try lia;
  repeat (split_ors; cleanup; simpl in * ); try lia;
  try solve [ unfold not in *; exfalso; eapply H8; [| eauto]; eauto];
  try solve [ unfold not in *; exfalso; eapply H9; [| eauto]; eauto];
  try solve [right; intuition eauto].
          
  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
      eapply pimpl_trans; [| eauto | eapply ptsto_upd].
    2: {
      eapply sep_star_assoc.
      apply sep_star_comm.
      pred_apply; cancel.
      instantiate (3:= bitmap_addr|-> x).
      cancel.
      intros m Hm.
     
      apply sep_star_comm.
      pred_apply. apply ptsto_bits_extract.
      lia.
      destruct (value_to_bits x); simpl in *.
      unfold valid_bitlist in *; cleanup.
      apply num_of_blocks_in_bounds.
    }
    cancel.
    instantiate (1:= updN x1 a v).
    admit. (* Separation logic goal *)
    rewrite length_updN; eauto. 
    rewrite upd_ne; eauto.
    lia.

  - left; eexists; intuition eauto.
    destruct_lifts.
    repeat rewrite mem_union_upd.
    do 2 destruct H.
    destruct_lifts.
    do 2 eexists.
      eapply pimpl_trans; [| eauto | eapply ptsto_upd].
    2: {
      eapply sep_star_assoc.
      apply sep_star_comm.
      pred_apply; cancel.
      instantiate (3:= bitmap_addr|-> x).
      cancel.
      intros m Hm.
     
      apply sep_star_comm.
      pred_apply. apply ptsto_bits_extract.
      lia.
      destruct (value_to_bits x); simpl in *.
      unfold valid_bitlist in *; cleanup.
      apply num_of_blocks_in_bounds.
    }
    cancel.
    instantiate (1:= updN x1 a v).
    admit. (* Separation logic goal *)
    rewrite length_updN; eauto. 
    rewrite upd_ne; eauto.
    lia.
*)
Admitted.

Global Opaque alloc free read write.

(*
Theorem block_allocator_rep_upd:
  forall m F dh a v,
    (F * block_allocator_rep dh)%predicate m ->
    (F * block_allocator_rep (upd dh a v))%predicate (upd m (S a) v).
Proof.
  unfold block_allocator_rep;
  intros.
  apply pimpl_exists_l_star_r in H.
  destruct H.
  apply pimpl_exists_l_star_r in H.
  destruct H.
  destruct_lifts.
  Search ptsto_bits.
  rewrite ptsto_bits_extract in H.
  apply sep_star_assoc in H.
  eapply ptsto_upd' in H.
  pred_apply' H.
  cancel.
*)
  
*)

End BlockAllocator.


