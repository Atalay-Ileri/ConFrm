
(* For disk *)
(* Axiom addr : Type. *)
Definition addr := nat.
Axiom addr_eq_dec : forall (a b: addr), {a=b}+{a<>b}.

Axiom value : Type.
Axiom nat_to_value : nat -> value.
Axiom value_to_nat : value -> nat.

Axiom nat_to_value_to_nat:
  forall n, value_to_nat (nat_to_value n) = n.
Axiom value_to_nat_to_value:
  forall v, nat_to_value (value_to_nat v) = v.
Axiom value_dec: forall v v': value, {v=v'}+{v<>v'}.

(* For access control *) 
Axiom user : Type.

Axiom handle : Type.
Axiom handle_eq_dec: forall (h1 h2: handle), {h1=h2}+{h1<>h2}.

(* Axiom permission : Type. *)
Inductive permission :=
| Public
| Owned (u: user).
Axiom permission_eq_dec: forall (p1 p2: permission), {p1 = p2}+{p1<>p2}.

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

Notation "'addr_dec'" := addr_eq_dec.
Notation "'handle_dec'" := handle_eq_dec.
Notation "'permission_dec'" := permission_eq_dec.

Inductive Result {State T: Type} :=
| Finished : State -> T -> @Result State T
| Crashed : State -> @Result State T.

Definition extract_state {State T} (res: @Result State T) :=
  match res with
  | Finished s _ | Crashed s => s
  end.

Definition extract_ret {State T} def (res: @Result State T) :=
  match res with
  | Finished _ r => r
  | Crashed _ => def
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
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T) def,
    extract_ret def (map_state R r) = extract_ret def r.
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Definition result_same {State1 State2 T1 T2} (res1: @Result State1 T1) (res2: @Result State2 T2) :=
  match res1, res2 with
  | Finished _ _, Finished _ _ | Crashed _, Crashed _ => True
  | _, _ => False
  end.

Lemma result_same_transitive:
  forall State1 State2 State3 T1 T2 T3
    (res1: @Result State1 T1)
    (res2: @Result State2 T2)
    (res3: @Result State3 T3),
    result_same res1 res2 ->
    result_same res2 res3 ->
    result_same res1 res3.
Proof.
  unfold result_same; intros.
  destruct res1, res2, res3; intuition.
Qed.

Lemma result_same_symmetric:
  forall State1 State2 T1 T2
    (res1: @Result State1 T1)
    (res2: @Result State2 T2),
    result_same res1 res2 ->
    result_same res2 res1.
Proof.
  unfold result_same; intros.
  destruct res1, res2; intuition.
Qed.