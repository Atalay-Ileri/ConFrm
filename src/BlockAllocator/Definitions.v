Require Import Primitives Layer1 Omega.
Close Scope pred_scope.

Axiom block_size: nat.
Axiom block_size_eq: block_size = 64.

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
Open Scope pred_scope.

Fixpoint ptsto_bits' (dh: disk value) bits n : @pred addr addr_dec (set value) :=
  match bits with
  | nil =>
    emp
  | b::l =>
    (exists vs,
    (S n) |-> vs *
    match b with
    | 0 => [[ dh n = None ]]
    | 1 => [[ dh n = Some (fst vs) ]]
    | _ => [[ False ]]
    end) *
    ptsto_bits' dh l (S n)
  end.
      
Definition ptsto_bits dh bits := ptsto_bits' dh bits 0.

Definition rep (dh: disk value) : @pred addr addr_dec (set value) :=
  (exists bitmap bl,
    let bits := bits (value_to_bits bitmap) in
    0 |-> (bitmap, bl) * ptsto_bits dh bits * [[ forall i, i >= block_size -> dh i = None ]])%pred.

Definition alloc (v': value) : prog (option addr) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  let index := get_first_zero bits in
  
  if lt_dec index block_size then
    _ <- Write (S index) v';
    _ <- Write 0 (bits_to_value (Build_bitlist (updN bits index 1) (upd_valid_one index bits valid)));
    Ret (Some index)
  else
    Ret None.

Definition read a : prog (option value) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      h <- Read (S a);
      Ret (Some h)
    else
      Ret None
  else
    Ret None.

Definition write a v' : prog (option unit) :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      _ <- Write (S a) v';
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Definition free a : prog unit :=
  v <- Read 0;
  let bits := bits (value_to_bits v) in
  let valid := valid (value_to_bits v) in
  if lt_dec a block_size then
    if addr_dec (nth a bits 0) 1 then
      Write 0 (bits_to_value (Build_bitlist (updN bits a 0) (upd_valid_zero a bits valid)))
    else
      Ret tt
  else
    Ret tt.

Hint Extern 0 (okToUnify (rep _) (rep _)) => constructor : okToUnify.
