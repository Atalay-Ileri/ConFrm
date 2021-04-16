Require Import EquivDec List PeanoNat Lia.

Class EqDec (T : Type) := eqdec : forall (a b : T), {a = b} + {a <> b}.

Definition option_dec {T} (TEQ: forall (t t': T), {t=t'}+{t<>t'}) : forall (o1 o2: option T), {o1=o2}+{o1<>o2}.
  decide equality.
Defined.

(** Disk **)
Definition addr := nat.
Axiom addr_eq_dec : EqDec addr.

Axiom value : Type.
Axiom value0 : value.
Axiom value_eq_dec: EqDec value.

Axiom block_size: nat. (** in bits **)

Axiom disk_size: addr. (** In blocks **)

Axiom addr_list_to_blocks : list addr -> list value.
Axiom blocks_to_addr_list : list value -> list addr.
Axiom addr_list_to_blocks_to_addr_list:
  forall l_a,
  exists l_a', blocks_to_addr_list (addr_list_to_blocks l_a) = app l_a l_a'.

Axiom blocks_to_addr_list_to_blocks:
  forall l_b,
    addr_list_to_blocks (blocks_to_addr_list l_b) = l_b.

Axiom addr_list_to_blocks_length_le:
  forall l,
    length (addr_list_to_blocks l) <= length l.


Axiom addr_list_to_blocks_length_le_preserve:
  forall l1 l2,
    length l1 <= length l2 ->
    length (addr_list_to_blocks l1) <= length (addr_list_to_blocks l2).

Lemma addr_list_to_blocks_length_eq:
  forall l_a l_b,
    length l_a = length l_b ->
    length (addr_list_to_blocks l_a) = length (addr_list_to_blocks l_b).
Proof.
  intros.
  apply PeanoNat.Nat.le_antisymm;
  eapply addr_list_to_blocks_length_le_preserve; lia.
Qed.


Fixpoint get_first_zero_index l :=
  match l with
  | nil => 0
  | cons hd tl =>
    match hd with
    | false => 0
    | true => S (get_first_zero_index tl)
    end
  end.


Definition zero_bitlist := (repeat false block_size).

Axiom value_to_bits: value -> list bool.
Axiom bits_to_value: list bool -> value.
Axiom value_to_bits_to_value : forall v, bits_to_value (value_to_bits v) = v.
Axiom bits_to_value_to_bits : forall l, 
length l <= block_size ->
exists l', value_to_bits (bits_to_value l) = l ++ l'.

Axiom bits_to_value_to_bits_exact : forall l, 
length l = block_size ->
value_to_bits (bits_to_value l) = l.

Axiom value_to_bits_length : forall v, length (value_to_bits v) = block_size.

Lemma get_first_zero_index_false:
  forall l_b,
    nth (get_first_zero_index l_b) l_b false = false.
Proof.
  induction l_b; simpl; intros; eauto.
  destruct a; eauto.
Qed.

Lemma get_first_zero_index_firstn:
  forall l_b n,
    get_first_zero_index (firstn n l_b) < n ->
    get_first_zero_index (firstn n l_b) = get_first_zero_index l_b.
Proof.
  induction l_b; simpl; intros; eauto.
  rewrite firstn_nil; simpl; eauto.
  destruct a, n; simpl in *; eauto.
  lia.
  rewrite IHl_b; eauto; lia.
Qed.



(** Crypto **)
Axiom hash : Type.
Axiom hash_eq_dec: EqDec hash.
Axiom hash_function: hash -> value -> hash.

Fixpoint rolling_hash h vl :=
  match vl with
  | nil => h
  | cons v vl' => rolling_hash (hash_function h v) vl'
  end.

Fixpoint rolling_hash_list h vl :=
  match vl with
  | nil => nil
  | cons v vl' =>
    let h':= hash_function h v in
    cons h' (rolling_hash_list h' vl')
  end.

Fixpoint hash_and_pair h vl :=
  match vl with
  | nil => nil
  | cons v vl' =>
    let h':= hash_function h v in
    cons (h, v) (hash_and_pair h' vl')
  end.
Axiom hash0 : hash.

Lemma rolling_hash_app:
  forall l1 l2 h,
    rolling_hash h (l1++l2) = rolling_hash (rolling_hash h l1) l2.
Proof.
  induction l1; simpl; eauto.
Qed.


Axiom key: Type.
Axiom key0: key.
Axiom key_eq_dec: EqDec key.
Axiom encrypt: key -> value -> value.
Axiom encrypt_ext: forall k v v', encrypt k v = encrypt k v' -> v = v'.
Axiom decrypt: key -> value -> value.
Axiom decrypt_ext: forall k v v', decrypt k v = decrypt k v' -> v = v'.
Axiom encrypt_decrypt: forall k v, decrypt k (encrypt k v) = v.
Axiom decrypt_encrypt: forall k ev, encrypt k (decrypt k ev) = ev.

(** Access control **) 
Axiom user : Type.
Axiom user0: user.


(** Execution Semantics **)
Inductive Result {State T: Type} :=
| Finished : State -> T -> @Result State T
| Crashed : State -> @Result State T.

Inductive Recovery_Result {State T: Type} :=
| RFinished : State -> T -> @Recovery_Result State T
| Recovered : State -> @Recovery_Result State T.

Definition results_match {State T T'} (res1: @Result State T) (res2: @Result State T') :=
  match res1, res2 with
  | Finished _ _, Finished _ _ => True
  | Crashed _, Crashed _ => True
  | _, _ => False
  end.

Definition extract_state {State T} (res: @Result State T) :=
  match res with
  | Finished s _ | Crashed s => s
  end.

Definition extract_ret {State T} (res: @Result State T) :=
  match res with
  | Finished _ r => Some r
  | Crashed _ => None
  end.

  Definition results_match_r {State T T'} (res1: @Recovery_Result State T) (res2: @Recovery_Result State T') :=
    match res1, res2 with
    | RFinished _ _, RFinished _ _ => True
    | Recovered _, Recovered _ => True
    | _, _ => False
    end.

Definition extract_state_r {State T} (res: @Recovery_Result State T) :=
  match res with
  | RFinished s _ | Recovered s => s
  end.

Definition extract_ret_r {State T} (res: @Recovery_Result State T) :=
  match res with
  | RFinished _ r => Some r
  | Recovered _ => None
  end.

Definition map_state {State1 State2 T} (f:State1 -> State2) (res: @Result State1 T) :=
  match res with
  | Finished s v => Finished (f s) v
  | Crashed s  => Crashed (f s)
  end.

Lemma extract_state_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T),
    extract_state (map_state R r) = R (extract_state r).
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Lemma extract_ret_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T),
    extract_ret (map_state R r) = extract_ret r.
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Instance addr_dec : EqDec addr := addr_eq_dec.
Instance value_dec : EqDec value := value_eq_dec.
Instance key_dec : EqDec key := key_eq_dec.
Instance hash_dec : EqDec hash := hash_eq_dec.


Record File := {
    owner: user;
    blocks: list value;
  }.
