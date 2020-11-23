Require Import BaseTypes List ListUtils FunctionalExtensionality Lia PeanoNat.

Set Implicit Arguments.

Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.
Definition empty_mem {A : Type} {AEQ : EqDec A} {V : Type} : @mem A AEQ V := fun a => None.

Section GenMem.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  (** Operations **)

  Definition upd (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then Some v else m a'.

  Definition upd_set (m : @mem A AEQ (V * list V)) (a : A) (v : V) : @mem A AEQ (V * list V) :=
    fun a' =>
      if AEQ a' a then
        match m a with
        | Some vs => Some (v, fst vs :: snd vs)
        | None => Some (v, nil)
        end
      else
        m a'.

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

  Definition mem_union (m1 m2 : @mem A AEQ V) : (@mem A AEQ V) :=
    fun a =>
  match m1 a with
  | Some v => Some v
  | None => m2 a
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

  Fixpoint delete_all (m : @mem A AEQ V) (la : list A) : @mem A AEQ V :=
    match la with
    | nil => m
    | a::la' => delete (delete_all m la') a
    end.

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

  Fixpoint upd_batch_opt m al vl :=
    match al, vl with
    | a::al', v::vl' => upd_batch_opt (updSome m a v) al' vl'
    | _, _ => m
    end.

  Fixpoint upd_batch_set m al vl :=
    match al, vl with
    | a::al', v::vl' => upd_batch_set (upd_set m a v) al' vl'
    | _, _ => m
    end.

  Fixpoint list_upd_batch (m: @mem A AEQ V) l_l_a l_l_v :=
  match l_l_a, l_l_v with
  | l_a :: lla, l_v :: llv =>
    list_upd_batch (upd_batch m l_a l_v) lla llv
  | _, _ => m
  end.

  Fixpoint list_upd_batch_opt (m: @mem A AEQ V) l_l_a l_l_v :=
  match l_l_a, l_l_v with
  | l_a :: lla, l_v :: llv =>
    list_upd_batch_opt (upd_batch_opt m l_a l_v) lla llv
  | _, _ => m
  end.

  Fixpoint list_upd_batch_set (m: @mem A AEQ (V * list V)) l_l_a l_l_v :=
  match l_l_a, l_l_v with
  | l_a :: lla, l_v :: llv =>
    list_upd_batch_set (upd_batch_set m l_a l_v) lla llv
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

  Definition list_mem  al vl := upd_batch (@empty_mem A AEQ V) al vl.


  Definition select_for_addr {A AEQ V} (selection: @mem A AEQ nat) (a: A) (vs: V * list V) : V :=
  match selection a with
  | None => fst vs
  | Some n => selN (fst vs :: snd vs) n (fst vs)
  end.

  Definition select_mem {A AEQ V} (selection: @mem A AEQ nat) (m: @mem A AEQ (V * list V)) : @mem A AEQ (V * list V) :=
    fun a => match m a with
        | None => None
        | Some vs =>
          Some (select_for_addr selection a vs, nil)
        end.

   Definition select_list_shifted {V} n (selection: @mem addr addr_dec nat) (l: list (V * list V)) : list V :=
   indexed_map_shifted n (select_for_addr selection) l.
  
  (** Properties **)
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


  (** Facts **)  
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

  Theorem delete_eq : forall m (a a': A),
    a' = a -> delete m a a' = None.
  Proof.
    intros; subst; unfold delete.
    destruct (AEQ a a); tauto.
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

  Theorem delete_ne : forall m (a a': A),
    a' <> a -> delete m a a' = m a'.
  Proof.
    intros; subst; unfold delete.
    destruct (AEQ a' a); tauto.
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

  Lemma delete_all_in:
      forall (l: list A) (m: @mem A AEQ V) a,
        In a l ->
        delete_all m l a = None.
    Proof.
      induction l; simpl; intros; intuition eauto.
      subst; rewrite delete_eq; eauto.
      destruct (AEQ a a0); subst;
      [rewrite delete_eq
      |rewrite delete_ne]; eauto.
    Qed.

  Lemma delete_all_not_in:
      forall (l: list A) (m: @mem A AEQ V) a,
        ~ In a l ->
        delete_all m l a = m a.
    Proof.
      induction l; simpl; intros; eauto.
      destruct (AEQ a a0); subst;
      rewrite delete_ne in *; eauto.
    Qed.
  
End GenMem.


    
  Lemma sync_upd_set_comm:
    forall A AEQ V (m: @mem A AEQ (V * list V)) a v,
      m a <> None -> 
      sync (upd_set m a v) = upd (sync m) a (v, nil).
  Proof.
    intros.
    extensionality x; simpl.
    unfold sync, upd_set; simpl.
    destruct (AEQ x a); subst; eauto.
    destruct (m a); try congruence.
    rewrite upd_eq; eauto.
    rewrite upd_ne; eauto.
  Qed.
  

  Lemma sync_upd_batch_set_comm:
    forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)),
      (forall a, In a l_a -> m a <> None) ->
      sync (upd_batch_set m l_a l_v) = upd_batch (sync m) l_a (map (fun v => (v, nil)) l_v).
  Proof.
    induction l_a; simpl; intros; eauto.
    destruct l_v; simpl; eauto.
    rewrite IHl_a.
    rewrite sync_upd_set_comm; eauto.
    intros.
    specialize (H a0); eauto.
    unfold upd_set; simpl.
    destruct (AEQ a0 a); subst; eauto.
    destruct (m a); congruence.
  Qed.

  Lemma sync_idempotent:
    forall A AEQ V (m: @mem A AEQ (V * list V)),
      sync (sync m) = sync m.
  Proof.
    intros; extensionality x.
    unfold sync; simpl.
    destruct (m x); simpl; eauto.
  Qed.

  Lemma upd_batch_upd:
    forall A AEQ V l_a l_v a v (m: @mem A AEQ V),
      ~In a l_a ->
      upd_batch (upd m a v) l_a l_v = upd (upd_batch m l_a l_v) a v.
  Proof.
    induction l_a; simpl; intros;
    eauto.
    destruct l_v; simpl; eauto.
    destruct (AEQ a0 a); subst.
    exfalso; eauto.
    rewrite upd_comm; eauto.
  Qed.

  Lemma sync_upd_comm:
  forall A AEQ V (m: @mem A AEQ (V * list V)) a vs,
    sync (upd m a vs) = upd (sync m) a (fst vs, nil).
Proof.
  unfold sync; intros; extensionality x; simpl.
  destruct (AEQ a x); subst; eauto.
  repeat rewrite upd_eq; simpl; eauto.
  repeat rewrite upd_ne; eauto.
Qed.

Lemma upd_set_ne:
  forall A AEQ V (m: @mem A AEQ (V * list V)) a a' v,
    a <> a' ->
    upd_set m a v a' = m a'.
Proof.
  unfold upd_set; intros.
  destruct (AEQ a' a); intuition eauto.
  congruence.
Qed.

Lemma upd_batch_set_ne:
  forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)) a,
    ~In a l_a ->
    upd_batch_set m l_a l_v a = m a.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  rewrite IHl_a; eauto.
  rewrite upd_set_ne; eauto.
Qed.


Lemma upd_batch_app:
  forall A AEQ V l1 l2 l3 l4 (m: @mem A AEQ V),
    length l1 = length l3 ->
    upd_batch m (l1++l2) (l3++l4) = upd_batch (upd_batch m l1 l3) l2 l4.
Proof.
  induction l1; simpl; intros; eauto;
  destruct l3; simpl in *; try lia; eauto.
Qed.

Lemma upd_batch_ne:
  forall A AEQ V l_a l_v (m: @mem A AEQ V) a,
    ~In a l_a ->
    upd_batch m l_a l_v a = m a.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  rewrite IHl_a; eauto.
  apply upd_ne; eauto.
Qed.


Lemma upd_batch_not_none:
  forall A AEQ V l_a l_v (m: @mem A AEQ V) a,
    m a <> None ->
    upd_batch m l_a l_v a <> None.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  apply IHl_a.
  destruct (AEQ a a0).
  repeat rewrite upd_eq; eauto; congruence.
  repeat rewrite upd_ne; eauto.
Qed.

Lemma sync_not_none:
  forall A AEQ V (m: @mem A AEQ (V * list V)) a,
    m a <> None ->
    sync m a <> None.
Proof.
  unfold sync; simpl; intros; eauto.
  destruct (m a); congruence.
Qed.


Lemma upd_set_upd_some:
  forall A AEQ V (m: @mem A AEQ (V * list V)) a v vs,
    m a = Some vs ->
    upd_set m a v = upd m a (v, fst vs :: snd vs).
Proof.
  intros.
  unfold upd_set; rewrite H; eauto.
Qed.

Lemma list_upd_batch_set_not_in:
  forall A AEQ V l_l_a l_l_v (m: @mem A AEQ (V * list V)) a,
    (forall l_a, In l_a l_l_a -> ~In a l_a) ->
    list_upd_batch_set m l_l_a l_l_v a = m a.
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; eauto.
  rewrite IHl_l_a; eauto.
  rewrite upd_batch_set_ne; eauto.
Qed.

Lemma upd_batch_set_none:
  forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)) a,
    upd_batch_set m l_a l_v a = None ->
    m a = None.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  eapply IHl_a in H.
  unfold upd_set in *.
  destruct (AEQ a0 a); subst; eauto.
  destruct (m a); congruence.
Qed.

Lemma sync_list_upd_batch_set:
  forall A AEQ V l_l_a l_l_v (m: @mem A AEQ (V * list V)),
    (forall l_a, In l_a l_l_a ->
            forall a, In a l_a -> m a <> None) ->
    sync (list_upd_batch_set m l_l_a l_l_v) =
    list_upd_batch (sync m) l_l_a (map (map (fun v => (v, nil))) l_l_v).
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; simpl; eauto.
  rewrite IHl_l_a; eauto.
  rewrite sync_upd_batch_set_comm; eauto.
  intros.
  intros Hx.
  eapply H; eauto.
  eapply upd_batch_set_none; eauto.
Qed.


Lemma list_upd_batch_not_in:
  forall A AEQ V l_l_a l_l_v (m: @mem A AEQ V) a,
    (forall l_a, In l_a l_l_a -> ~In a l_a) ->
    list_upd_batch m l_l_a l_l_v a = m a.
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; eauto.
  rewrite IHl_l_a; eauto.
  eapply upd_batch_ne; eauto.
Qed.

Lemma sync_selNopt:
  forall A AEQ V l a i (m: @mem A AEQ (V * list V)),
    m a = selNopt l i ->
    sync m a = selNopt (map (fun vs => (fst vs, nil)) l) i.
Proof.
  unfold sync; induction l; simpl; intros; eauto.
  rewrite H; eauto.
  destruct i. rewrite H; eauto.
  eapply IHl; eauto.
Qed.

 Lemma list_upd_batch_not_none:
   forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)) a,
     m a <> None ->
     list_upd_batch_set m l_a l_v a <> None.
 Proof.
   induction l_a; simpl; intros; eauto.
   destruct l_v; simpl; eauto.
   apply IHl_a.
   unfold not; intros.
   apply upd_batch_set_none in H0; congruence.
 Qed.

 



Lemma select_list_shifted_length:
  forall V (l: list (V * list V)) n selection,
    length(select_list_shifted n selection l) = length l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma select_list_shifted_selN:
  forall V (l: list (V * list V)) i n selection def1 def2,
    i < length l ->
    selN (select_list_shifted n selection l) i def1 =
    select_for_addr selection (n + i) (selN l i def2).
Proof.
  induction l; simpl; intros; eauto.
  lia.
  destruct i; simpl; eauto.
  rewrite Nat.add_0_r; eauto.
  unfold select_list_shifted in *; erewrite IHl.
  replace (S n + i) with (n + S i) by lia; eauto.
  lia.
Qed.

Lemma select_for_addr_synced:
  forall A AEQ V (selection: @mem A AEQ nat) (a: A) (vs: V * list V),
    snd vs = nil ->
    select_for_addr selection a vs = fst vs.
Proof.
  unfold select_for_addr; simpl; intros.   
  destruct (selection a); simpl; eauto.
  destruct n; eauto.
  rewrite H; simpl; eauto.
Qed.

Lemma select_list_shifted_synced:
  forall V (l: list (V * list V)) selection n,
    (forall vs, In vs l -> snd vs = nil) ->
    select_list_shifted n selection l = map fst l.
Proof.
  induction l; simpl; eauto; intros.
  unfold select_list_shifted in *; simpl.
  rewrite IHl; eauto.
  rewrite select_for_addr_synced; eauto.
Qed.


  Lemma mem_map_upd_comm:
    forall A AEQ V1 V2 (m: @mem A AEQ V1) a v (f: V1 -> V2),
      mem_map f (upd m a v) = upd (mem_map f m) a (f v).
  Proof.
    intros. unfold mem_map.
    extensionality x.
    destruct (AEQ a x); subst;
    [ repeat rewrite upd_eq; eauto
    | repeat rewrite upd_ne; eauto].
  Qed.

  Definition sumbool_agree {A B C D} (eq1: {A}+{B})(eq2: {C}+{D}):=
    if eq1 then
      if eq2 then
        True
      else
        False
    else
      if eq2 then
        False
      else
        True.

  Lemma upd_shift_comm:
    forall A AEQ V (m: @mem A AEQ V) (f: A -> A) a v,
      (forall x y, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
      upd (shift f m) a v = shift f (upd m (f a) v).
  Proof.
    unfold sumbool_agree; intros; simpl.
    extensionality x; simpl.
    specialize (H a x).
    unfold shift.
    destruct (AEQ a x);
    destruct (AEQ (f a) (f x)); subst; intuition;
    [ repeat rewrite upd_eq
    | repeat rewrite upd_ne]; eauto.
  Qed.

  Lemma upd_merge_set_cons_comm:
    forall A AEQ V (m1: @mem A AEQ V) m2 a v0 v1 vl,
      upd (merge_set m1 m2) a (v0, v1::vl) = merge_set (upd m1 a v0) (upd m2 a (v1, vl)).
  Proof.
    unfold merge_set; intros.
    extensionality x; simpl.
    destruct (AEQ a x); subst; intuition;
    [ repeat rewrite upd_eq
    | repeat rewrite upd_ne]; eauto.
  Qed.
  
  Lemma merge_set_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      m2 a <> None ->
      exists vs, merge_set m1 m2 a = Some vs /\
            fst vs = v.
  Proof.
    unfold merge_set; simpl; intros.
    rewrite H.
    destruct (m2 a); try congruence; eauto.    
  Qed.
  
  Lemma merge_set_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      merge_set m1 m2 a = m2 a.
  Proof.
    unfold merge_set; simpl; intros.
    rewrite H; eauto.
  Qed.
  
  Lemma mem_map_fst_some_elim:
      forall A AEQ V1 V2 (m: @mem A AEQ (V1 * V2)) a v vs,
        m a = Some (v, vs) ->
        mem_map fst m a = Some v.
  Proof.
    intros.
    unfold mem_map; simpl; rewrite H; eauto.
  Qed.

  Lemma mem_map_fst_some_exists:
      forall A AEQ V1 V2 (m: @mem A AEQ (V1 * V2)) a v,
        mem_map fst m a = Some v ->
        exists vs, m a = Some (v, vs).
  Proof.
    intros.
    unfold mem_map in *; simpl.
    destruct (m a).
    destruct p; simpl in *; eauto.
    inversion H; eauto.
    inversion H.
  Qed.


  Lemma upd_batch_not_in_none:
    forall A AEQ V l l' (m: @mem A AEQ V) a,
      m a = None ->
      ~ In a l ->
      length l = length l' ->
      upd_batch m l l' a = None.
  Proof.
    induction l; simpl; intros; eauto.
    destruct l'; simpl in *; try lia.
    destruct (AEQ a a0); subst.
    exfalso; apply H0; intuition.
    apply IHl.
    rewrite upd_ne; eauto.
    intros Hx; apply H0; eauto.
    lia.
  Qed.

  Definition synced_from {V} a (m: @mem nat Nat.eq_dec (V * list V)):=
    forall a', a' >= a -> (sync m) a' = m a'.

Hint Rewrite upd_eq using (solve [ auto ]) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.
