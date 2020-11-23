Require EquivDec.
(* For disk *)
(* Axiom addr : Type. *)

Class EqDec (T : Type) := eqdec : forall (a b : T), {a = b} + {a <> b}.

Definition option_dec {T} (TEQ: forall (t t': T), {t=t'}+{t<>t'}) : forall (o1 o2: option T), {o1=o2}+{o1<>o2}.
  decide equality.
Defined.

Definition addr := nat.
Axiom addr_eq_dec : EqDec addr.

Axiom value : Type.
Axiom nat_to_value : nat -> value.
Axiom value_to_nat : value -> nat.
Definition value0 := nat_to_value 0.

Axiom nat_to_value_to_nat:
  forall n, value_to_nat (nat_to_value n) = n.
Axiom value_to_nat_to_value:
  forall v, nat_to_value (value_to_nat v) = v.
Axiom value_eq_dec: EqDec value.

(* For Crypto *)
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

(* For access control *) 
Axiom user : Type.
Axiom user0: user.

Axiom handle : Type.
Axiom handle_eq_dec: EqDec handle.

(* Axiom permission : Type. *)
Inductive permission :=
| Public
| Owned (u: user).
Axiom permission_eq_dec: EqDec permission.

Axiom can_access : user -> permission -> Prop.
Axiom can_access_dec : forall u p, {can_access u p}+{~can_access u p}.
Axiom can_access_public: forall u, can_access u Public.

Definition sealed_value := (permission * value)%type.

Inductive op :=
| Uns : user -> permission -> op
| Cho : user -> permission -> op.

Definition trace := list op.

Fixpoint trace_ok tr :=
  match tr with
  | nil =>
    True
  | cons h tl =>
    match h with
    | Uns u p =>
      can_access u p /\ trace_ok tl
    | Cho u p =>
      can_access u p /\ trace_ok tl
    end
  end.

Lemma trace_ok_app_merge:
  forall tr tr',
    trace_ok tr ->
    trace_ok tr' ->
    trace_ok (tr++tr').
Proof.
  induction tr; intros; simpl in *; eauto.
  destruct a; simpl in *; destruct H; eauto.
Qed.

Lemma trace_ok_app_split:
  forall tr tr',
    trace_ok (tr++tr') ->
    trace_ok tr /\ trace_ok tr'.
Proof.
  induction tr; simpl; intros; eauto.
  destruct a; simpl in *; intuition eauto.
  all: specialize IHtr with (1:= H1); intuition eauto.
Qed.

Inductive Result {State T: Type} :=
| Finished : State -> T -> @Result State T
| Crashed : State -> @Result State T.

Inductive Recovery_Result {State T: Type} :=
| RFinished : State -> T -> @Recovery_Result State T
| Recovered : State -> @Recovery_Result State T.

Definition extract_state {State T} (res: @Result State T) :=
  match res with
  | Finished s _ | Crashed s => s
  end.

Definition extract_ret {State T} (res: @Result State T) :=
  match res with
  | Finished _ r => Some r
  | Crashed _ => None
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

Notation "'handle_dec'" := handle_eq_dec.
Notation "'permission_dec'" := permission_eq_dec.
