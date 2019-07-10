
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

Lemma trace_ok_app:
  forall tr tr',
    trace_ok tr ->
    trace_ok tr' ->
    trace_ok (tr++tr').
Proof.
  induction tr; intros; simpl in *; eauto.
  destruct a; simpl in *; destruct H; eauto.
Qed.

Inductive token :=
| Handle : handle -> token
| Crash : token
| Cont : token
.

Definition oracle := list token.

Notation "'addr_dec'" := addr_eq_dec.
Notation "'handle_dec'" := handle_eq_dec.
Notation "'permission_dec'" := permission_eq_dec.