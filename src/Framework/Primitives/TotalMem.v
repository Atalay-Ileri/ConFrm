Require Import BaseTypes List ListUtils FunctionalExtensionality Lia PeanoNat.

Set Implicit Arguments.

Definition total_mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> V.

Section GenTotal_Mem.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  (** Operations **)

  Definition upd (m : @total_mem A AEQ V) (a : A) (v : V) : @total_mem A AEQ V :=
    fun a' => if AEQ a' a then v else m a'.

  Definition upd_set (m : @total_mem A AEQ (V * list V)) (a : A) (v : V) : @total_mem A AEQ (V * list V) :=
    fun a' =>
      if AEQ a' a then
         (v, fst (m a) :: snd (m a))
      else
        m a'.

  Definition total_mem_map {V'} (f: V -> V') (m : @total_mem A AEQ V) : @total_mem A AEQ V' :=
    fun a => f (m a).
  
  Definition merge_set (m1: @total_mem A AEQ V)
             (m2: @total_mem A AEQ (V * list V)) : @total_mem A AEQ (V * list V) :=
  fun a =>((m1 a), fst (m2 a)::snd (m2 a)).
  
  Definition sync (m: @total_mem A AEQ (V * list V)) :=
    fun a => (fst (m a), nil: list V).

  Definition shift (shift_a: A -> A) (m:@total_mem A AEQ V) :=
    fun a => m (shift_a a).

  Fixpoint upd_batch m al vl :=
    match al, vl with
    | a::al', v::vl' => upd_batch (upd m a v) al' vl'
    | _, _ => m
    end.

  Fixpoint upd_batch_set m al vl :=
    match al, vl with
    | a::al', v::vl' => upd_batch_set (upd_set m a v) al' vl'
    | _, _ => m
    end.

  Fixpoint list_upd_batch (m: @total_mem A AEQ V) l_l_a l_l_v :=
  match l_l_a, l_l_v with
  | l_a :: lla, l_v :: llv =>
    list_upd_batch (upd_batch m l_a l_v) lla llv
  | _, _ => m
  end.

  Fixpoint list_upd_batch_set (m: @total_mem A AEQ (V * list V)) l_l_a l_l_v :=
  match l_l_a, l_l_v with
  | l_a :: lla, l_v :: llv =>
    list_upd_batch_set (upd_batch_set m l_a l_v) lla llv
  | _, _ => m
  end.

  Definition get_all_existing (m: @total_mem A AEQ V) al :=
    map m al.

  Definition select_for_addr {A AEQ V} (selection: @total_mem A AEQ nat) (a: A) (vs: V * list V) : V :=
    seln (fst vs :: snd vs) (selection a) (fst vs).

  Definition select_total_mem {A AEQ V} (selection: @total_mem A AEQ nat) (m: @total_mem A AEQ (V * list V)) : @total_mem A AEQ (V * list V) :=
    fun a => (select_for_addr selection a (m a), nil).

   Definition select_list_shifted {V} n (selection: @total_mem addr addr_dec nat) (l: list (V * list V)) : list V :=
   indexed_map_shifted n (select_for_addr selection) l.
  
  (** Properties **)


  (** Facts **)  
  Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = v.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a a); tauto.
  Qed.

  Theorem upd_ne : forall m (a : A) (v : V) a',
    a' <> a -> upd m a v a' = m a'.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a' a); tauto.
  Qed.

  Theorem upd_repeat: forall m (a : A) (v v':V),
    upd (upd m a v') a v = upd m a v.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a a); try congruence.
    destruct (AEQ x a); auto.
  Qed.

  Theorem upd_nop: forall m (a : A) (v : V),
    m a = v ->
    upd m a v = m.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat erewrite upd_eq; eauto.
    repeat rewrite upd_ne; auto.
  Qed.

  Theorem upd_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; unfold upd; intros.
    destruct (AEQ a1 a0); destruct (AEQ a0 a1); try congruence.
    case_eq (AEQ x a1); case_eq (AEQ x a0); intros; subst; try congruence.
  Qed.
  
End GenTotal_Mem.
    
  Lemma sync_upd_set_comm:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)) a v, 
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
    forall A AEQ V l_a l_v (m: @total_mem A AEQ (V * list V)),
      sync (upd_batch_set m l_a l_v) = upd_batch (sync m) l_a (map (fun v => (v, nil)) l_v).
  Proof.
    induction l_a; simpl; intros; eauto.
    destruct l_v; simpl; eauto.
    rewrite IHl_a.
    rewrite sync_upd_set_comm; eauto.
  Qed.

  Lemma sync_idempotent:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)),
      sync (sync m) = sync m.
  Proof.
    intros; extensionality x.
    unfold sync; simpl.
    destruct (m x); simpl; eauto.
  Qed.

  Lemma upd_batch_upd:
    forall A AEQ V l_a l_v a v (m: @total_mem A AEQ V),
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
  forall A AEQ V (m: @total_mem A AEQ (V * list V)) a vs,
    sync (upd m a vs) = upd (sync m) a (fst vs, nil).
Proof.
  unfold sync; intros; extensionality x; simpl.
  destruct (AEQ a x); subst; eauto.
  repeat rewrite upd_eq; simpl; eauto.
  repeat rewrite upd_ne; eauto.
Qed.

Lemma upd_set_ne:
  forall A AEQ V (m: @total_mem A AEQ (V * list V)) a a' v,
    a <> a' ->
    upd_set m a v a' = m a'.
Proof.
  unfold upd_set; intros.
  destruct (AEQ a' a); intuition eauto.
  congruence.
Qed.

Lemma upd_batch_set_ne:
  forall A AEQ V l_a l_v (m: @total_mem A AEQ (V * list V)) a,
    ~In a l_a ->
    upd_batch_set m l_a l_v a = m a.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  rewrite IHl_a; eauto.
  rewrite upd_set_ne; eauto.
Qed.


Lemma upd_batch_app:
  forall A AEQ V l1 l2 l3 l4 (m: @total_mem A AEQ V),
    length l1 = length l3 ->
    upd_batch m (l1++l2) (l3++l4) = upd_batch (upd_batch m l1 l3) l2 l4.
Proof.
  induction l1; simpl; intros; eauto;
  destruct l3; simpl in *; try lia; eauto.
Qed.

Lemma upd_batch_ne:
  forall A AEQ V l_a l_v (m: @total_mem A AEQ V) a,
    ~In a l_a ->
    upd_batch m l_a l_v a = m a.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; eauto.
  rewrite IHl_a; eauto.
  apply upd_ne; eauto.
Qed.



Lemma upd_set_upd_some:
  forall A AEQ V (m: @total_mem A AEQ (V * list V)) a v vs,
    m a = vs ->
    upd_set m a v = upd m a (v, fst vs :: snd vs).
Proof.
  intros.
  unfold upd_set; rewrite H; eauto.
Qed.

Lemma list_upd_batch_set_not_in:
  forall A AEQ V l_l_a l_l_v (m: @total_mem A AEQ (V * list V)) a,
    (forall l_a, In l_a l_l_a -> ~In a l_a) ->
    list_upd_batch_set m l_l_a l_l_v a = m a.
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; eauto.
  rewrite IHl_l_a; eauto.
  rewrite upd_batch_set_ne; eauto.
Qed.


Lemma sync_list_upd_batch_set:
  forall A AEQ V l_l_a l_l_v (m: @total_mem A AEQ (V * list V)),
    sync (list_upd_batch_set m l_l_a l_l_v) =
    list_upd_batch (sync m) l_l_a (map (map (fun v => (v, nil))) l_l_v).
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; simpl; eauto.
  rewrite IHl_l_a; eauto.
  rewrite sync_upd_batch_set_comm; eauto.
Qed.


Lemma list_upd_batch_not_in:
  forall A AEQ V l_l_a l_l_v (m: @total_mem A AEQ V) a,
    (forall l_a, In l_a l_l_a -> ~In a l_a) ->
    list_upd_batch m l_l_a l_l_v a = m a.
Proof.
  induction l_l_a; simpl; intros; eauto.
  destruct l_l_v; eauto.
  rewrite IHl_l_a; eauto.
  eapply upd_batch_ne; eauto.
Qed.

Lemma select_list_shifted_length:
  forall V (l: list (V * list V)) n selection,
    length(select_list_shifted n selection l) = length l.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma select_list_shifted_seln:
  forall V (l: list (V * list V)) i n selection def1 def2,
    i < length l ->
    seln (select_list_shifted n selection l) i def1 =
    select_for_addr selection (n + i) (seln l i def2).
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
  forall A AEQ V (selection: @total_mem A AEQ nat) (a: A) (vs: V * list V),
    snd vs = nil ->
    select_for_addr selection a vs = fst vs.
Proof.
  unfold select_for_addr; simpl; intros.   
  destruct (selection a); simpl; eauto.
  destruct n; eauto.
  rewrite H; simpl; eauto.
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


  Lemma total_mem_map_upd_comm:
    forall A AEQ V1 V2 (m: @total_mem A AEQ V1) a v (f: V1 -> V2),
      total_mem_map f (upd m a v) = upd (total_mem_map f m) a (f v).
  Proof.
    intros. unfold total_mem_map.
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
    forall A AEQ V (m: @total_mem A AEQ V) (f: A -> A) a v,
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
    forall A AEQ V (m1: @total_mem A AEQ V) m2 a v0 v1 vl,
      upd (merge_set m1 m2) a (v0, v1::vl) = merge_set (upd m1 a v0) (upd m2 a (v1, vl)).
  Proof.
    unfold merge_set; intros.
    extensionality x; simpl.
    destruct (AEQ a x); subst; intuition;
    [ repeat rewrite upd_eq
    | repeat rewrite upd_ne]; eauto.
  Qed.
  
  Lemma total_mem_map_fst_some_elim:
      forall A AEQ V1 V2 (m: @total_mem A AEQ (V1 * V2)) a v vs,
        m a = (v, vs) ->
        total_mem_map fst m a = v.
  Proof.
    intros.
    unfold total_mem_map; simpl; rewrite H; eauto.
  Qed.

  Lemma total_mem_map_fst_some_exists:
      forall A AEQ V1 V2 (m: @total_mem A AEQ (V1 * V2)) a v,
        total_mem_map fst m a = v ->
        exists vs, m a = (v, vs).
  Proof.
    intros.
    unfold total_mem_map in *; simpl.
    destruct (m a).
    simpl in *; subst; eauto.
  Qed.

  Definition synced_from {V} a (m: @total_mem nat Nat.eq_dec (V * list V)):=
    forall a', a' >= a -> (sync m) a' = m a'.

  (*
  Lemma upd_batch_eq:
  forall A AEQ V l1 l2 (m: @total_mem A AEQ V) a i,
    nth_error l1 i = Some a ->
    ~In a (skipn (S i) l1) ->
    length l1 = length l2 ->
    upd_batch m l1 l2 a = nth_error l2 i.
Proof.
  induction l1; simpl in *; intros; eauto.
  congruence.
  
  destruct l2; simpl in *; try lia.
  destruct i; subst; simpl in *.
  -
    rewrite upd_batch_ne; eauto.
    apply upd_eq; eauto.
    congruence.

  - erewrite IHl1; eauto.
Qed.
*)

Lemma upd_batch_set_app:
  forall A AEQ V l1 l2 l3 l4 (m: @total_mem A AEQ (V * list V)),
    length l1 = length l3 ->
    upd_batch_set m (l1++l2) (l3++l4) = upd_batch_set (upd_batch_set m l1 l3) l2 l4.
Proof.
  induction l1; simpl; intros; eauto.
  destruct l3; simpl in *; eauto; lia.
  destruct l3; simpl in *; try lia.
  rewrite IHl1; eauto.
Qed.

Lemma upd_batch_set_seq_in:
  forall V n start l i j (m: @total_mem addr addr_dec (V * list V)) vs def,
    m j = vs ->
    j = start + i ->
    i < n ->
    length l = n ->
    upd_batch_set m (seq start n) l j = (seln l i def, fst vs :: snd vs).
Proof.
  induction n; simpl; intros; eauto; try lia.
  destruct l; simpl in *; subst; try lia.
  destruct i; simpl in *; eauto.
  rewrite Nat.add_0_r in *.
  rewrite upd_batch_set_ne; eauto.
  unfold upd_set; subst; eauto.
  destruct (addr_dec start start); subst;
  intuition eauto; try lia.
  intros Hx; apply in_seq in Hx; lia.
  specialize IHn with (i:= i) (start:= S start); simpl in *.
  erewrite <- IHn.
  replace (S (start + i)) with (start + S i) by lia; eauto.
  rewrite upd_set_ne; eauto.
  all: lia.
Qed.

Lemma select_list_shifted_select_0:
  forall V (l: list (V * list V)) n selector,
    (forall i, i < length l -> selector (n + i) = 0) ->
    select_list_shifted n selector l = map fst l.
Proof.
  unfold select_list_shifted; induction l;
  simpl; intros; eauto.
  erewrite IHl; eauto.
  unfold select_for_addr.
  setoid_rewrite <- Nat.add_0_r at 2.
  rewrite H; eauto.
  lia.
  intros.
  rewrite Nat.add_succ_comm.
  eapply H; lia.
Qed.

Lemma select_list_shifted_app:
  forall V (l' l: list (V * list V)) n selector,
    select_list_shifted n selector (l++l') =
    select_list_shifted n selector l ++
                        select_list_shifted (n + length l) selector l'.
Proof.
  induction l; simpl; intros; eauto.
  unfold select_list_shifted; simpl.
  rewrite Nat.add_0_r; eauto.
  unfold select_list_shifted in *; simpl.
  rewrite IHl.
  replace (n + S (length l)) with (S n + length l) by lia; eauto.
Qed.


Lemma select_for_addr_not_1_latest :
  forall A AEQ V (selector: @total_mem A AEQ nat) (n: A) (v1 v2: V),
    selector n <> 1 ->
    select_for_addr selector n (v1, v2::nil) = v1.
Proof.
  unfold select_for_addr; intros; simpl.
  destruct (selector n); simpl; eauto.
  destruct n0; simpl; eauto.
  congruence.
Qed.

Lemma map_noop:
  forall A l (f: A -> A),
    (forall a, In a l -> f a = a) ->
    map f l = l.
Proof.
  induction l; simpl; intuition eauto.
  rewrite IHl; eauto.
  rewrite H; eauto.
Qed.

Lemma shift_select_total_mem_comm:
  forall A AEQ V (m: @total_mem A AEQ (V * list V)) f selector,
    select_total_mem (shift f selector) (shift f m) = shift f (select_total_mem selector m).
Proof.
  intros; unfold select_total_mem, select_for_addr, shift; eauto.
Qed.

Lemma sync_shift_comm:
  forall A AEQ V (m: @total_mem A AEQ (V * list V)) f,
    sync (shift f m) = shift f (sync m).
Proof.
  unfold shift, sync; intros; simpl; eauto.
Qed.

Lemma select_total_mem_upd_comm:
  forall A AEQ V (a: A) (vs: V * list V) selector (m: @total_mem A AEQ _),
    snd vs = nil ->
    select_total_mem selector (upd m a vs) =
    upd (select_total_mem selector m) a vs.
Proof.
  intros; unfold select_total_mem, select_for_addr, upd; simpl; intros.
  destruct vs; simpl in *; subst.
  extensionality x.
  
  destruct (AEQ x a); subst; eauto.
  destruct (selector a); simpl; eauto.
Qed.

Lemma select_total_mem_upd_batch_comm:
  forall A AEQ V (l_a: list A) (l_vs: list (V * list V)) selector (m: @total_mem A AEQ _),
    Forall (fun vs => snd vs = nil) l_vs ->
    
    select_total_mem selector (upd_batch m l_a l_vs) =
    upd_batch (select_total_mem selector m) l_a l_vs.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_vs; simpl in *; eauto.
  rewrite IHl_a; eauto.
  rewrite select_total_mem_upd_comm; eauto.
  all: inversion H; intuition eauto.
Qed.

Lemma select_total_mem_list_upd_batch_comm:
  forall A AEQ V (l_l_a: list (list A)) (l_l_vs: list (list (V * list V))) selector (m: @total_mem A AEQ _),
    Forall (fun l_vs => Forall (fun vs => snd vs = nil) l_vs) l_l_vs ->
    select_total_mem selector (list_upd_batch m l_l_a l_l_vs) =
    list_upd_batch (select_total_mem selector m) l_l_a l_l_vs.
Proof.
  induction l_l_a; simpl in *; intros; eauto.
  destruct l_l_vs; eauto.
  erewrite IHl_l_a.
  rewrite select_total_mem_upd_batch_comm; eauto.
  all: inversion H; intuition eauto.
Qed.

Lemma sync_select_total_mem_noop:
  forall A AEQ V selector (m: @total_mem A AEQ (V * list V)),
    sync (select_total_mem selector m) = select_total_mem selector m.
Proof.
  unfold sync, select_total_mem; intros; simpl; eauto.
Qed.

Lemma list_upd_batch_app:
      forall A AEQ V l1 l2 l3 l4 (m: @total_mem A AEQ V),
        length l1 = length l3 ->
        list_upd_batch m (l1++l2) (l3++l4) = list_upd_batch (list_upd_batch m l1 l3) l2 l4.
Proof.
  induction l1; destruct l3; simpl; intros; eauto; lia.
Qed.

Lemma list_upd_batch_set_app:
  forall A AEQ V l1 l2 l3 l4 (m: @total_mem A AEQ (V * list V)),
    length l1 = length l3 ->
    list_upd_batch_set m (l1++l2) (l3++l4) = list_upd_batch_set (list_upd_batch_set m l1 l3) l2 l4.
Proof.
  induction l1; destruct l3; simpl; intros; eauto; lia.
Qed.

Lemma shift_upd_batch_comm:
  forall A AEQ V f l1 l2 (m: @total_mem A AEQ V),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    upd_batch (shift f m) l1 l2 = shift f (upd_batch m (map f l1) l2).
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite upd_shift_comm; eauto.
Qed.

Lemma shift_eq_after:
  forall V (m1 m2: @total_mem addr addr_dec V) f,
    (forall a, f a >= f 0)  ->
    (forall a, a >= f 0 -> m1 a = m2 a) ->
    shift f m1 = shift f m2.
Proof.
  unfold shift; intros; extensionality x; eauto.
Qed.


Lemma shift_upd_set_comm:
  forall A AEQ V f a v (m: @total_mem A AEQ (V * list V)),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (upd_set m (f a) v) =
    upd_set (shift f m) a v.
Proof.
  unfold sumbool_agree, upd_set, shift; simpl; intros; eauto.
  extensionality x; simpl.
  specialize (H x a).
  destruct (AEQ x a); subst.
  destruct (AEQ (f a) (f a)); subst; intuition eauto.        
  destruct (AEQ (f x) (f a)); intuition eauto.
Qed.

Lemma shift_upd_batch_set_comm:
  forall A AEQ V f l1 l2 (m: @total_mem A AEQ (V * list V)),
    
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (upd_batch_set m (map f l1) l2) =
    upd_batch_set (shift f m) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite IHl1; eauto.
  rewrite shift_upd_set_comm; eauto.
Qed.

Lemma shift_list_upd_batch_set_comm:
  forall A AEQ V f l1 l2 (m: @total_mem A AEQ (V * list V)),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (list_upd_batch_set m (map (map f) l1) l2) =
    list_upd_batch_set (shift f m) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite IHl1; eauto.
  rewrite shift_upd_batch_set_comm; eauto.
Qed.

Lemma shift_upd_noop:
  forall A AEQ V f (m: @total_mem A AEQ V) a v,
    (forall a', f a' <> a) ->
    shift f (upd m a v) = shift f m.
Proof.
  unfold shift, upd; intros.
  extensionality x.
  destruct (AEQ (f x) a); eauto; congruence.
Qed.

Lemma shift_upd_set_noop:
  forall A AEQ V f (m: @total_mem A AEQ (V * list V)) a v,
    (forall a', f a' <> a) ->
    shift f (upd_set m a v) = shift f m.
Proof.
  unfold shift, upd_set; intros.
  extensionality x.
  destruct (AEQ (f x) a); eauto; congruence.
Qed.

Lemma total_mem_map_shift_comm:
  forall A AEQ V1 V2 (f: V1 -> V2) s (m: @total_mem A AEQ V1),
    total_mem_map f (shift s m) = shift s (total_mem_map f m).
Proof.
  unfold total_mem_map, shift; intros; extensionality a.
  eauto.
Qed.

Lemma total_mem_map_fst_upd_set:
  forall A AEQ V a v (m: @total_mem A AEQ (V * list V)),
    total_mem_map fst (upd_set m a v) = upd (total_mem_map fst m) a v.
Proof.
  unfold upd_set, upd, total_mem_map; intros; simpl.
  extensionality x.
  destruct (AEQ x a); subst; eauto.
Qed.

Lemma total_mem_map_fst_upd_batch_set:
  forall A AEQ V l_a l_v (m: @total_mem A AEQ (V * list V)),
    total_mem_map fst (upd_batch_set m l_a l_v) = upd_batch (total_mem_map fst m) l_a l_v.
Proof.
  induction l_a; intros; simpl; eauto.
  destruct l_v; eauto.
  rewrite IHl_a.
  rewrite total_mem_map_fst_upd_set; eauto.
Qed.

Lemma total_mem_map_fst_list_upd_batch_set:
  forall A AEQ V l_a l_v (m: @total_mem A AEQ (V * list V)),
    total_mem_map fst (list_upd_batch_set m l_a l_v) = list_upd_batch (total_mem_map fst m) l_a l_v.
Proof.
  induction l_a; intros; simpl; eauto.
  destruct l_v; eauto.
  rewrite IHl_a.
  rewrite total_mem_map_fst_upd_batch_set; eauto.
Qed.

Lemma total_mem_map_fst_sync_noop:
  forall A AEQ V (m: @total_mem A AEQ (V * list V)),
    total_mem_map fst (sync m) = total_mem_map fst m.
Proof.
  unfold total_mem_map, sync; simpl; intros; eauto.
Qed.


Lemma upd_batch_list_upd_batch_app_rev:
  forall A AEQ V (m: @total_mem A AEQ V) l_l_a l_l_v l_a l_v,
    length l_l_a = length l_l_v ->
    upd_batch (list_upd_batch m l_l_a l_l_v) l_a l_v =
    list_upd_batch m (l_l_a ++ (l_a::nil)) (l_l_v ++ (l_v::nil)).
Proof.
  intros; rewrite list_upd_batch_app ; simpl; eauto.
Qed.

Lemma rev_cons_app:
  forall A (l l': list A) a,
    rev l = a::l' ->
    l = rev l' ++ (a::nil).
Proof.
  induction l; simpl;
  intros; try congruence.

  destruct (rev l') eqn:D.
  {
    rewrite <- rev_involutive with (l:= l') in H.
    rewrite D in H.
    simpl in *.
    destruct l; simpl in *; eauto.
    assert (AX: length ((rev l ++ (a1::nil)) ++ (a::nil)) = length (a0::nil)). {
      rewrite H; eauto.
    }
    repeat rewrite app_length in *; simpl in *; lia.
  }
  {                         
    rewrite <- rev_involutive with (l:= l') in H.
    rewrite D in H.
    simpl in *.
    rewrite app_comm_cons in H.
    apply app_inj_tail in H; intuition subst.
    erewrite IHl.
    rewrite rev_involutive; eauto.
    eauto.
  }
Qed.


Lemma upd_batch_upd_in_noop:
  forall A AEQ V l_a l_v (m: @total_mem A AEQ V) a v,
    In a l_a ->
    length l_a = length l_v ->
    upd_batch (upd m a v) l_a l_v =
    upd_batch m l_a l_v.
Proof.
  intros.
  apply in_split_first in H; eauto; subst.
  do 2 destruct H.
  intuition; subst.
  rewrite app_length in *; simpl in *.
  rewrite <- firstn_skipn with (l:= l_v) (n:= length x).
  repeat rewrite upd_batch_app.
  destruct (skipn (length x) l_v) eqn:D.
  { (** Impossible **)
    apply length_zero_iff_nil in D.
    rewrite skipn_length in D; lia.
  }
  {
    simpl.
    setoid_rewrite upd_batch_upd at 2; eauto.
    rewrite upd_repeat; eauto.
  }
  all: rewrite firstn_length_l; lia.
Qed.

Lemma upd_batch_in_cons_noop:
  forall A AEQ V l_a l_v a v (m: @total_mem A AEQ V),
    In a l_a ->
    length l_a = length l_v ->
    upd_batch m (a::l_a) (v::l_v) =
    upd_batch m l_a l_v.
Proof.
  induction l_a; simpl; intuition eauto.
  {
    subst; destruct l_v; simpl in *; try lia.
    rewrite upd_repeat; eauto.
  }
  {                           
    subst; destruct l_v; simpl in *; try lia.
    destruct (AEQ a a0); subst.
    rewrite upd_repeat; eauto.
    rewrite upd_comm; eauto.
  }
Qed.

Lemma upd_batch_upd_batch_noop:
  forall A AEQ V l_a l_v1 l_v2 (m: @total_mem A AEQ V),
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (upd_batch m l_a l_v1) l_a l_v2 =
    upd_batch m l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2; try lia; eauto.
  simpl in *; lia.
  
  destruct (in_dec AEQ a l_a).
  repeat rewrite upd_batch_in_cons_noop; eauto.
  simpl.
  rewrite <- upd_batch_upd; eauto.
  rewrite IHl_a; eauto.
  rewrite upd_repeat; eauto.
Qed.

Lemma upd_upd_batch_app_rev:
  forall A AEQ V (m: @total_mem A AEQ V) a v l_a l_v,
    length l_a = length l_v ->
    upd (upd_batch m l_a l_v) a v =
    upd_batch m (l_a ++ (a::nil)) (l_v ++ (v::nil)).
Proof.
  intros; rewrite upd_batch_app ; simpl; eauto.
Qed.

Lemma upd_batch_firstn_noop:
  forall A AEQ V l_a l_v (s: @total_mem A AEQ V) n,
    length l_a = length l_v ->
    upd_batch (upd_batch s (firstn n l_a) (firstn n l_v)) l_a l_v =
    upd_batch s l_a l_v.
Proof.
  intros A AEQ V l_a.
  eapply rev_ind with
      (P:= fun l_a =>
             forall (l_v : list V) (s : total_mem) (n : nat),
               length l_a = length l_v ->
               upd_batch (upd_batch s (firstn n l_a) (firstn n l_v))
                         l_a l_v = upd_batch s l_a l_v).

  simpl; intros.
  repeat rewrite firstn_nil; simpl; eauto.

  simpl; intros.
  destruct (rev l_v) eqn:D; simpl; eauto.
  {
    destruct l_v; simpl in *; try congruence.
    repeat rewrite firstn_nil; simpl; eauto.
    destruct (l ++ (x::nil)); simpl.
    destruct (firstn n nil); simpl; eauto.
    destruct (firstn n (a :: l0)); simpl; eauto.
    apply app_eq_nil in D; intuition; congruence.
  }
  {                     
    apply rev_cons_app in D.
    subst.
    repeat rewrite app_length in *; simpl in *.
    repeat rewrite upd_batch_app by lia; simpl.
    destruct (Compare_dec.le_dec n (length l)).
    repeat rewrite firstn_app_l by lia.
    rewrite H by lia; eauto.
    repeat rewrite firstn_oob by (rewrite app_length; simpl; lia).
    repeat rewrite upd_upd_batch_app_rev by lia.
    rewrite upd_batch_upd_batch_noop; eauto.
    repeat rewrite app_length; simpl; eauto.
    repeat rewrite app_length; simpl; eauto.
  }
Qed.

Lemma upd_to_upd_batch_singleton:
  forall A AEQ V (m: @total_mem A AEQ V) a v,
    upd m a v = upd_batch m (a::nil) (v::nil).
Proof.
  eauto.
Qed.

Lemma upd_batch_to_list_upd_batch_singleton:
  forall A AEQ V (m: @total_mem A AEQ V) l_a l_v,
    upd_batch m l_a l_v = list_upd_batch m (l_a::nil) (l_v::nil).
Proof.
  eauto.
Qed.

Lemma upd_list_upd_batch_upd_noop:
  forall A AEQ V  l_l_a l_l_v a v1 v2 (s: @total_mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    upd (list_upd_batch (upd s a v1) l_l_a l_l_v) a v2 =
    upd (list_upd_batch s l_l_a l_l_v) a v2.
Proof.
  induction l_l_a; intros; eauto.
  apply upd_repeat; eauto.
  eapply forall2_length in H as Hx.
  destruct l_l_v;
  try solve [simpl in *; lia].
  simpl.
  destruct (in_dec AEQ a0 a).
  rewrite upd_batch_upd_in_noop; eauto.
  inversion H; lia.
  rewrite upd_batch_upd; eauto.
  rewrite IHl_l_a; eauto.
  inversion H; eauto.
Qed.

Lemma upd_batch_list_upd_batch_upd_batch_noop:
  forall A AEQ V l_a l_v1 l_v2 l_l_a l_l_v (s: @total_mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (list_upd_batch (upd_batch s l_a l_v1) l_l_a l_l_v) l_a l_v2 =
    upd_batch (list_upd_batch s l_l_a l_l_v) l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  destruct (in_dec AEQ a l_a).
  repeat rewrite upd_batch_in_cons_noop; eauto.

  simpl.
  repeat rewrite upd_batch_upd; eauto.
  setoid_rewrite upd_to_upd_batch_singleton at 2.
  setoid_rewrite upd_batch_to_list_upd_batch_singleton at 2.
  rewrite <- list_upd_batch_app.
  rewrite IHl_a; eauto.
  simpl.
  rewrite <- upd_batch_upd; eauto.
  rewrite upd_list_upd_batch_upd_noop; eauto.
  rewrite upd_batch_upd; eauto.
  apply Forall2_app; simpl; eauto.
  simpl; eauto.
Qed.

Lemma upd_batch_list_upd_batch_upd_batch_firstn_noop:
  forall A AEQ V l_a l_v1 l_v2 l_l_a l_l_v (s: @total_mem A AEQ V) n,
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (list_upd_batch (upd_batch s (firstn n l_a) (firstn n l_v1)) l_l_a l_l_v) l_a l_v2 =
    upd_batch (list_upd_batch s l_l_a l_l_v) l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  repeat rewrite firstn_nil; simpl; eauto.
  
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  destruct n.
  simpl; eauto.
  destruct (in_dec AEQ a (firstn n l_a)).

  {
    simpl firstn.
    repeat rewrite upd_batch_in_cons_noop; eauto.
    eapply in_firstn_in; eauto.
    repeat rewrite firstn_length; simpl in *; lia.
    eapply in_firstn_in; eauto.
  }
  {
    simpl firstn.
    simpl upd_batch at 2.
    rewrite upd_batch_upd; eauto.
    simpl.
    rewrite upd_list_upd_batch_upd_noop; eauto.
    
    destruct (in_dec AEQ a l_a).
    repeat rewrite upd_batch_upd_in_noop; eauto.
    repeat rewrite upd_batch_upd; eauto.
    rewrite IHl_a; eauto.
  }
Qed.



Lemma list_upd_batch_noop:
  forall A AEQ V l_l_a l_l_v1 l_l_v2 (s: @total_mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v1 ->
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v2 ->
    list_upd_batch (list_upd_batch s l_l_a l_l_v1) l_l_a l_l_v2 =
    list_upd_batch s l_l_a l_l_v2.
Proof.
  intros A AEQ V l_l_a.
  eapply rev_ind with
      (P:= fun l_l_a =>
             forall (l_l_v1 l_l_v2 : list (list V)) (s : total_mem),
               Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v1 ->
               Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v2 ->
               list_upd_batch (list_upd_batch s l_l_a l_l_v1) l_l_a l_l_v2 =
               list_upd_batch s l_l_a l_l_v2).
  {
    simpl; intros; eauto.
  }
  {
    intros. 
    eapply forall2_length in H0 as Hx;
    eapply forall2_length in H1 as Hx0.
    repeat rewrite app_length in *.
    destruct (nil_or_app l_l_v1);
    subst; try solve [simpl in *; lia].
    destruct (nil_or_app l_l_v2);
    subst; try solve [simpl in *; lia].
    do 2 destruct H2.
    do 2 destruct H3.
    subst.

    repeat rewrite app_length in *.
    repeat rewrite list_upd_batch_app.
    simpl.                    
    rewrite upd_batch_list_upd_batch_upd_batch_noop; eauto.
    rewrite H; eauto.

    

    apply Forall2_app_split in H0; intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1;
    intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1; intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H0; intuition eauto.
    inversion H3; eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1; intuition eauto.
    inversion H3; eauto.
    all: simpl in *; lia.
  }
Qed.

Lemma list_upd_batch_firstn_noop:
  forall A AEQ V l_l_a l_l_v (s: @total_mem A AEQ V) n m,
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    list_upd_batch (list_upd_batch s (firstn n l_l_a ++ (firstn m (seln l_l_a n nil)::nil)) (firstn n l_l_v ++ (firstn m (seln l_l_v n nil)::nil))) l_l_a l_l_v =
    list_upd_batch s l_l_a l_l_v.
Proof.
  
  intros A AEQ V l_l_a.
  eapply rev_ind with
      (P:= fun l_l_a =>
             forall (l_l_v : list (list V)) (s : total_mem) (n m : nat),
               Forall2 (fun (l_a : list A) (l_v : list V) => length l_a = length l_v) l_l_a l_l_v ->
               list_upd_batch (list_upd_batch s (firstn n l_l_a ++ (firstn m (seln l_l_a n nil)::nil)) (firstn n l_l_v ++ (firstn m (seln l_l_v n nil)::nil))) l_l_a l_l_v =
    list_upd_batch s l_l_a l_l_v).
  {
    simpl; intros; eauto.
    repeat rewrite firstn_nil; simpl; eauto.
    destruct (firstn n l_l_v ++ (firstn m (seln l_l_v n nil)::nil));
    eauto.
  }
  {
    intros.
    eapply forall2_length in H0 as Hx.
    rewrite app_length in *.
    destruct (nil_or_app l_l_v); subst;
    try solve [simpl in *; lia].
    do 2 destruct H1; subst.
    rewrite app_length in *.
    {
      repeat rewrite list_upd_batch_app by (simpl in *; lia); simpl.
      destruct (Compare_dec.le_dec n (length l)).
      {
        repeat rewrite firstn_app_l by (simpl in *; lia).
        simpl in *.
        apply Forall2_app_split in H0; intuition subst.
        inversion H2; subst.
        inversion l0; subst.
        {
          rewrite firstn_oob.
          repeat rewrite seln_last by (simpl in *; lia).
          setoid_rewrite firstn_oob at 2.
          repeat rewrite list_upd_batch_app by lia; eauto; simpl.
          rewrite upd_batch_list_upd_batch_upd_batch_firstn_noop; eauto.
          rewrite list_upd_batch_noop; eauto.
          lia.
          eauto.
        }
        {
          repeat rewrite seln_app by lia.
          rewrite H; eauto.
          rewrite list_upd_batch_app; eauto.
          lia.
        }
        lia.
      }
      {
        repeat rewrite seln_oob.
        repeat rewrite firstn_nil.
        repeat rewrite firstn_oob.
        rewrite list_upd_batch_app; simpl; eauto.
        rewrite upd_batch_to_list_upd_batch_singleton.
        rewrite <- list_upd_batch_app; eauto.
        rewrite list_upd_batch_noop; eauto.
        all: try repeat rewrite app_length; simpl in *; try lia.
      }
    }
  }
Qed.

Lemma shift_some :
  forall A AEQ V f (m: @total_mem A AEQ V) a,
    shift f m a = m (f a).
Proof.
  unfold shift; eauto.
Qed.

Lemma list_upd_batch_some:
  forall A AEQ V l_l_a l_l_v (m1 m2: @total_mem A AEQ V) a v,
    list_upd_batch m1 l_l_a l_l_v a = v ->
    length l_l_a = length l_l_v ->
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    m1 a = v \/ list_upd_batch m2 l_l_a l_l_v a = v.
Proof.
  intros.
  destruct (list_list_in_EXM AEQ l_l_a a).
  {
    destruct H2; intuition eauto.
    rewrite <- firstn_skipn with (n:= S x)(l:= l_l_a) in H.
    rewrite <- firstn_skipn with (n:= S x)(l:= l_l_v) in H.
    rewrite list_upd_batch_app in H.
    rewrite list_upd_batch_not_in in H; eauto.
    setoid_rewrite firstn_S_seln in H; eauto.
    rewrite list_upd_batch_app in H.
    simpl in *.

    rewrite <- firstn_skipn with (n:= S x)(l:= l_l_a).
    rewrite <- firstn_skipn with (n:= S x)(l:= l_l_v).
    rewrite list_upd_batch_app.
    rewrite list_upd_batch_not_in; eauto.
    setoid_rewrite firstn_S_seln; eauto.
    rewrite list_upd_batch_app.
    simpl in *.
    
    apply in_split_last in H2.
    do 2 destruct H2; intuition; subst.
    rewrite H4 in *.
    instantiate (1:= nil) in H.
    instantiate (1:= nil).
    rewrite <- firstn_skipn with (n:= length x0)(l:= (seln l_l_v x nil)) in *.
    rewrite upd_batch_app in *; eauto.
    simpl in *.
    destruct (skipn (length x0) (seln l_l_v x nil)) eqn:D.
    eapply (f_equal (@length A)) in H4.
    eapply (f_equal (@length V)) in D.
    rewrite skipn_length in D; simpl in *.
    rewrite app_length in *; simpl in *.
    eapply forall2_seln in H1.
    rewrite <- H1, H4 in D; lia.
    lia.
    
    rewrite upd_batch_ne in *; eauto.
    rewrite upd_eq in *; eauto.

    all: try solve [ 
               try repeat rewrite firstn_length_l; eauto; try lia].
    all: try solve [eapply forall2_seln in H1;
                    [>  try repeat rewrite firstn_length_l; eauto;
                     try rewrite <- H1, H4, app_length; simpl; lia | lia] ].
  }
  {
    rewrite list_upd_batch_not_in in *; eauto.
  }
Qed.


Lemma upd_batch_eq:
  forall A AEQ V l1 l2 (m: @total_mem A AEQ V) a i def1 def2,
    seln l1 i def1 = a ->
    ~In a (skipn (S i) l1) ->
    length l1 = length l2 ->
    i < length l1 ->
    upd_batch m l1 l2 a = seln l2 i def2.
Proof.
  induction l1; simpl in *; intros; eauto.
  lia.
  
  destruct l2; simpl in *; try lia.
  destruct i; subst; simpl in *.
  -
    rewrite upd_batch_ne; eauto.
    apply upd_eq; eauto.

  - erewrite IHl1; eauto.
    lia.
Qed.

Lemma shift_select_total_mem_synced:
  forall A AEQ V (tm: @total_mem A AEQ (V * list V)) selector f,
    (forall a, snd (tm (f a)) = nil) ->
    shift f (select_total_mem selector tm) = shift f tm.
Proof.
  intros.
  extensionality a; simpl.
  unfold shift, select_total_mem; simpl.
  rewrite select_for_addr_synced; eauto.
  erewrite <- (H a).
  destruct (tm (f a)) eqn:D; eauto.
Qed.

Lemma select_total_mem_synced:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)) selector (a: A) vs,
      select_total_mem selector m a = vs ->
      snd vs = nil.
  Proof.
    unfold select_total_mem; intros.
    destruct (m a); try congruence.
    inversion H; simpl; eauto.
  Qed.

  Lemma select_total_mem_synced_noop:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)) selector,
      (forall a vs, m a = vs -> snd vs = nil) ->
      select_total_mem selector m = m.
  Proof.
    intros; extensionality a.
    unfold select_total_mem; simpl.
    destruct (m a) eqn:D; eauto.
    apply H in D; subst; eauto.
    simpl in *; subst; eauto.
    rewrite select_for_addr_synced; simpl; eauto.
  Qed.
  
Hint Rewrite upd_eq using (solve [ auto ]) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.
