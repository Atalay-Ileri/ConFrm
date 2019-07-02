Require Import SepLogic.
(* For disk *)
(* Axiom addr : Type. *)
Definition addr := nat.
Axiom value : Type.
Axiom addr_eq_dec : forall (a b: addr), {a=b}+{a<>b}.

(* For access control *) 
Axiom user : Type.
Axiom handle : Type.
(* Axiom permission : Type. *)
Inductive permission :=
| Public
| Owned (u: user).
Axiom handle_eq_dec: forall (h1 h2: handle), {h1=h2}+{h1<>h2}.
Axiom can_access : user -> permission -> Prop.
Axiom can_access_dec : forall u p, can_access u p \/ ~can_access u p.
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
.

Definition oracle := list token.

Instance addr_dec : Instances.EqDec addr := addr_eq_dec.
Instance handle_dec : Instances.EqDec handle := handle_eq_dec.