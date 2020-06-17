Require Import List FunctionalExtensionality.

Set Implicit Arguments.

Class EqDec (T : Type) := eqdec : forall (a b : T), {a = b} + {a <> b}.
(* generalized memory of any address / value type *)

Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.
Definition empty_mem {A : Type} {AEQ : EqDec A} {V : Type} : @mem A AEQ V := fun a => None.

Section GenMem.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  (* Operations *)

  Definition upd (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then Some v else m a'.

  Definition updSome (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => None
      | Some _ => Some v
      end else m a'.

  Definition merge_set (m1: @mem A AEQ V)
             (m2: @mem A AEQ (V * list V)) : @mem A AEQ (V * list V) :=
  fun a =>
    match m1 a with
    | None => m2 a
    | Some v =>
      match m2 a with
      | None => None
      | Some vs =>
        Some (v, fst vs::snd vs)
      end
    end.

  Definition merge (m1: @mem A AEQ V)
             (m2: @mem A AEQ V) : @mem A AEQ V :=
  fun a =>
    match m1 a with
    | None => m2 a
    | Some v => Some v
    end.
  
  Definition sync (m: @mem A AEQ (V * list V)) :=
    fun a =>
      match m a with
      | None => None
      | Some vs => Some (fst vs, nil: list V)
      end.

  Definition shift (shift_a: A -> A) (m:@mem A AEQ V) :=
    fun a => m (shift_a a).

  Definition delete (m : @mem A AEQ V) (a : A) : @mem A AEQ V :=
    fun a' => if AEQ a' a then None else m a'.

  Definition insert (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then
      match m a with
      | None => Some v
      | Some _ => m a'
      end else m a'.

  Fixpoint upd_batch m al vl :=
    match al, vl with
    | a::al', v::vl' => upd_batch (upd m a v) al' vl'
    | _, _ => m
    end.

  Fixpoint get_all_existing (m: @mem A AEQ V) al :=
    match al with
    | nil => nil
    | a::al' =>
      match m a with
      | None => get_all_existing m al'
      | Some v => v::get_all_existing m al'
      end
    end.

  Definition mem_map {V2} (f: V -> V2) (m: @mem A AEQ V) : @mem A AEQ V2 :=
    fun a => match m a with
          | None => None
          | Some v => Some (f v)
          end.

  (* Properties *)
  Definition subset (m1 m2: @mem A AEQ V) :=
    forall a,
      (m2 a = None -> m1 a = None) /\
      (forall v, m1 a = Some v -> m2 a = Some v).

  Definition consistent (m: @mem A AEQ V) a v :=
    m a = None \/ m a = Some v.

  Definition addrs_match {V1} (m1: @mem A AEQ V)
             (m2: @mem A AEQ V1) : Prop :=
    forall a, m1 a <> None -> m2 a <> None.

  Definition addrs_match_exactly {V1} (m1: @mem A AEQ V)
             (m2: @mem A AEQ V1) : Prop :=
  forall a, m1 a <> None <-> m2 a <> None.

  Fixpoint consistent_with_upds m al vl :=
    match al, vl with
    | nil, nil => True
    | a::al', v::vl' =>
      consistent m a v /\
      consistent_with_upds (upd m a v) al' vl'
    | _, _ => False
    end.
  
  Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = Some v.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a a); tauto.
  Qed.

  Theorem updSome_eq : forall m (a : A) (v v' : V) a',
    m a = Some v' -> a' = a -> updSome m a v a' = Some v.
  Proof.
    intros; subst; unfold updSome.
    rewrite H.
    destruct (AEQ a a); tauto.
  Qed.

  Theorem insert_eq : forall m (a : A) (v v' : V) a',
    m a = None -> a' = a -> insert m a v a' = Some v.
  Proof.
    intros; subst; unfold insert.
    rewrite H.
    destruct (AEQ a a); congruence.
  Qed.

  Theorem upd_ne : forall m (a : A) (v : V) a',
    a' <> a -> upd m a v a' = m a'.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a' a); tauto.
  Qed.

  Theorem updSome_ne : forall m (a : A) (v : V) a',
    a' <> a -> updSome m a v a' = m a'.
  Proof.
    intros; subst; unfold updSome.
    destruct (AEQ a' a); tauto.
  Qed.

  Theorem insert_ne : forall m (a : A) (v : V) a',
    a' <> a -> insert m a v a' = m a'.
  Proof.
    intros; subst; unfold insert.
    destruct (AEQ a' a); congruence.
  Qed.

  Theorem upd_repeat: forall m (a : A) (v v':V),
    upd (upd m a v') a v = upd m a v.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
  Qed.

  Theorem updSome_repeat: forall m (a : A) (v v':V),
    updSome (updSome m a v') a v = updSome m a v.
  Proof.
    intros; apply functional_extensionality; unfold updSome; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
    destruct (m a); auto.
  Qed.

  Theorem insert_repeat: forall m (a : A) (v v':V),
    insert (insert m a v) a v' = insert m a v.
  Proof.
    intros; apply functional_extensionality; unfold insert at 1; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
    subst. unfold insert; simpl.
    destruct (AEQ a a); try congruence.
    destruct (m a); auto.
  Qed.

  Theorem upd_nop: forall m (a : A) (v : V),
    m a = Some v ->
    upd m a v = m.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite upd_eq; eauto.
    repeat rewrite upd_ne; auto.
  Qed.

  Theorem updSome_nop: forall m (a : A) (v : V),
    m a = Some v ->
    updSome m a v = m.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite updSome_eq; eauto.
    repeat rewrite updSome_ne; auto.
  Qed.

  Theorem updSome_none : forall m (a : A) (v : V),
    m a = None ->
    updSome m a v = m.
  Proof.
    unfold updSome; intros; apply functional_extensionality; intros.
    rewrite H.
    destruct (AEQ x a); subst; auto.
  Qed.

  Theorem upd_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem updSome_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (updSome m a0 v0) a1 v1 = updSome (updSome m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; unfold updSome; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem updSome_insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> updSome (insert m a0 v0) a1 v1 = insert (updSome m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; unfold updSome, insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem updSome_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> updSome (delete m a0) a1 v1 = delete (updSome m a1 v1) a0.
  Proof.
    intros; apply functional_extensionality; unfold updSome, delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem insert_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> insert (insert m a0 v0) a1 v1 = insert (insert m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; unfold insert; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem insert_delete_comm: forall m (a0 : A) a1 (v1 : V), a0 <> a1
    -> insert (delete m a0) a1 v1 = delete (insert m a1 v1) a0.
  Proof.
    intros; apply functional_extensionality; unfold insert, delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

  Theorem delete_comm: forall m (a0 : A) a1, a0 <> a1
    -> delete (delete m a0) a1 = delete (delete m a1) a0.
  Proof.
    intros; apply functional_extensionality; unfold delete; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.

End GenMem.

Hint Rewrite upd_eq using (solve [ auto ]) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.
