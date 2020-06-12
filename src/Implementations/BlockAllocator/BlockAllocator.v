Require Import Framework FSParameters TransactionalDiskLayer Omega.
Import IfNotations.
Close Scope pred_scope.

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

Open Scope pred_scope.
  
Fixpoint ptsto_bits' (dh: disk value) value_sets bits n : @pred addr addr_dec (set value) :=
  match value_sets, bits with
  | vs::value_sets', b::bits' =>
    (S n) |-> vs *
    match b with
    | 0 => [[ dh n = None ]]
    | 1 => [[ dh n = Some (fst vs) ]]
    | _ => [[ False ]]
    end *
    ptsto_bits' dh value_sets' bits' (S n)
   | _, _ =>
    emp
  end.
      
Definition ptsto_bits dh value_sets bits := ptsto_bits' dh value_sets bits 0.

Definition block_allocator_rep (dh: disk value) : @pred addr addr_dec (set value) :=
  (exists* bitmap bl value_sets,
     let bits := bits (value_to_bits bitmap) in
     bitmap_addr |-> (bitmap, bl) *
     ptsto_bits dh value_sets bits *
     [[ length value_sets = num_of_blocks ]] *
     [[ forall i, i >= num_of_blocks -> dh i = None ]])%pred.
End BlockAllocator.
