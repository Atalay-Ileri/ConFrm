Require Import BaseTypes List Omega SetoidList Permutation.
Import ListNotations.
Import Permutation.


Set Implicit Arguments.

Fixpoint selN (V : Type) (vs : list V) (n : nat) (default : V) : V :=
  match vs with
    | nil => default
    | v :: vs' =>
      match n with
        | O => v
        | S n' => selN vs' n' default
      end
  end.

Fixpoint selNopt (V : Type) (vs : list V) (n : nat) : option V :=
  match vs with
    | nil => None
    | v :: vs' =>
      match n with
        | O => Some v
        | S n' => selNopt vs' n'
      end
  end.

Fixpoint updN T (vs : list T) (n : nat) (v : T) : list T :=
  match vs with
    | nil => nil
    | v' :: vs' =>
      match n with
        | O => v :: vs'
        | S n' => v' :: updN vs' n' v
      end
  end.


(** prevent eauto from unifying length ?a = length ?b *)
Definition eqlen A B (a : list A) (b : list B) := length a = length b.

Definition removeN {V} (l : list V) i :=
   (firstn i l) ++ (skipn (S i) l).

(** Deduplicates by leaving last occurences **)
Fixpoint dedup_last {A} AEQ(la: list A) :=
  match la with
  | nil => nil
  | a :: la' =>
    if In_dec AEQ a la' then
      dedup_last AEQ la'
    else
      a :: dedup_last AEQ la'
  end.


Fixpoint dedup_by_list {A B} AEQ (la: list A) (lb: list B) :=
  match la, lb with
  | a :: la' , b :: lb' =>
    if In_dec AEQ a la' then
      dedup_by_list AEQ la' lb'
    else
      b :: dedup_by_list AEQ la' lb'
  | _, _ => nil
  end.

Fixpoint dedup_by_fst {A B} AEQ (l: list (A * B)) :=
  match l with
  | ab :: l' =>
    if In_dec AEQ (fst ab) (map fst l') then
      dedup_by_fst AEQ l'
    else
      ab :: dedup_by_fst AEQ l'
  | nil => nil
  end.

Definition in_dec_b {T} (TEQ: EqDec T) : T -> list T -> bool.
  intros.
  induction X0.
  exact false.
  destruct (TEQ X a).
  exact true.
  destruct (in_dec TEQ X X0).
  exact true.
  exact false.
Defined.

(* rewrite hints for various List facts *)
Hint Rewrite repeat_length map_length app_length Nat.min_idempotent : lists.

Lemma in_iff_in_dec_b :
  forall A AEQ (l: list A) a,
    In a l <-> in_dec_b AEQ a l = true.
Proof.
  induction l; simpl; intuition eauto; try congruence.
  destruct (AEQ a0 a); try congruence.
  destruct (AEQ a0 a); try congruence.
  destruct (in_dec AEQ a0 l); try congruence.
  
  destruct (AEQ a0 a); try congruence; eauto.
  destruct (in_dec AEQ a0 l); try congruence; eauto.
Qed.



Lemma fst_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> fst c = a.
Proof.
 intros; subst; firstorder.
Qed.

Lemma snd_pair : forall T1 T2 (a : T1) (b : T2) c, 
  c = (a, b) -> snd c = b.
Proof.
 intros; subst; firstorder.
Qed.

Lemma repeat_selN : forall T i n (v def : T),
  i < n -> selN (repeat v n) i def = v.
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.

Lemma repeat_selN' : forall T i n (v : T),
  selN (repeat v n) i v = v.
Proof.
  induction i; destruct n; firstorder; inversion H.
Qed.

Lemma selNopt_selN : forall T i l (v def : T),
  selNopt l i = Some v -> selN l i def = v.
Proof.
  induction i; destruct l; intros; inversion H; firstorder.
Qed.

Lemma selN_selNopt : forall T i l (v def : T),
  i < length l -> selNopt l i = Some (selN l i def).
Proof.
  induction i; destruct l; simpl; intros; try omega; auto.
  apply IHi; auto; omega.
Qed.

Lemma selNopt_length : forall T i l (v : T),
  selNopt l i = Some v -> i < length l.
Proof.
  induction i; destruct l; simpl; intros; inversion H; try omega.
  specialize (IHi _ _ H); omega.
Qed.

Lemma repeat_app : forall T i j (x : T),
  repeat x i ++ repeat x j = repeat x (i + j).
Proof.
  induction i; simpl; intros; auto.
  f_equal; eauto.
Qed.

Lemma repeat_map : forall A B (f:A -> B) x n,
  map f (repeat x n) = repeat (f x) n.
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.

Lemma concat_hom_repeat : forall A l k (item : A),
  Forall (fun x => x = repeat item k) l ->
  concat l = repeat item (length l * k).
Proof.
  induction l; auto; intros.
  simpl.
  inversion H; subst.
  rewrite <- repeat_app.
  f_equal; auto.
Qed.

Lemma length_nil : forall A (l : list A),
  length l = 0 -> l = nil.
Proof.
  induction l; firstorder.
  inversion H.
Qed.

Lemma length_nil' : forall A (l : list A),
  length l = 0 -> nil = l.
Proof.
  intros; apply eq_sym.
  apply length_nil; auto.
Qed.

Lemma eqlen_nil : forall A B (a : list A),
  eqlen a (@nil B) -> a = nil.
Proof.
  unfold eqlen; simpl; intros.
  apply length_nil; auto.
Qed.

Lemma cons_app : forall A (a : A) l,
  a :: l = [a] ++ l.
Proof.
  intros; auto.
Qed.



(** TODO: use [nth] everywhere *)
Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
Proof.
  induction n; intros; destruct l; simpl; auto.
Qed.

Lemma length_updN : forall T vs n (v : T), length (updN vs n v) = length vs.
Proof.
  induction vs; destruct n; simpl; intuition.
Qed.

Hint Rewrite length_updN : lists.

Lemma selN_updN_eq : forall V vs n v (default : V),
  n < length vs
  -> selN (updN vs n v) n default = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_selN_def_eq : forall V vs n (def1 def2 : V),
  n < length vs
  -> selN vs n def1 = selN vs n def2.
Proof.
  induction vs; simpl; intros; try omega.
  destruct n; auto.
  eapply IHvs.
  omega.
Qed.

Lemma selN_updN_eq_default : forall V vs n (v : V),
  selN (updN vs n v) n v = v.
Proof.
  induction vs; destruct n; simpl; intuition; omega.
Qed.

Lemma selN_updN_ne : forall V vs n n' v (default : V),
  n <> n'
  -> selN (updN vs n v) n' default = selN vs n' default.
Proof.
  induction vs; destruct n; destruct n'; simpl; intuition.
Qed.

Lemma selN_eq_updN_eq : forall A (l : list A) i a def,
  a = selN l i def
  -> updN l i a = l.
Proof.
  induction l; destruct i; simpl; firstorder.
  f_equal; auto.
  erewrite IHl; eauto.
Qed.

Lemma repeat_eq_updN : forall T i n (v x : T) l,
  i < n ->
  repeat v n = updN l i x -> x = v.
Proof.
  induction i; intros.
  - destruct n. omega.
    destruct l; simpl in *; inversion H0. auto.
  - destruct n. omega.
    destruct l; simpl in *; inversion H0.
    eapply IHi; [> | eauto]. omega.
Qed.

Hint Rewrite selN_updN_eq using (simpl; omega) : lists.

Lemma in_skipn_S : forall A l n (a : A) def,
  selN l n def <> a
  -> In a (skipn n l)
  -> In a (skipn (S n) l).
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_firstn_in : forall A l n (a : A),
  In a (firstn n l) -> In a l.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_skipn_in : forall A l n (a : A),
  In a (skipn n l) -> In a l.
Proof.
  induction l; destruct n; simpl; firstorder.
Qed.

Lemma in_cons_head : forall A l (a:A),
  In a (a :: l).
Proof.
  intros.
  constructor.
  reflexivity.
Qed.

Lemma in_app_middle : forall A l1 l2 (a:A),
  In a (l1 ++ a :: l2).
Proof.
  intros.
  induction l1; simpl; auto.
Qed.

Lemma firstn_updN : forall T (v : T) vs i j,
  i <= j
  -> firstn i (updN vs j v) = firstn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs; auto; omega.
Qed.

Theorem updN_firstn_comm : forall T (v : T) vs i j,
  firstn i (updN vs j v) = updN (firstn i vs) j v.
Proof.
  induction vs; destruct i, j; simpl; intuition.
  rewrite IHvs by omega.
  reflexivity.
Qed.

Hint Rewrite firstn_updN using omega : lists.

Lemma skipn_skipn': forall A n m (l: list A),
  skipn n (skipn m l) = skipn (m + n) l.
Proof.
  intros until m.
  induction m; intros; simpl; auto.
  destruct l.
  destruct n; auto.
  apply IHm.
Qed.

Lemma skipn_skipn: forall A n m (l: list A),
  skipn n (skipn m l) = skipn (n + m) l.
Proof.
  intros.
  rewrite Nat.add_comm.
  apply skipn_skipn'.
Qed.

Lemma skipn_selN : forall T i j vs (def: T),
  selN (skipn i vs) j def = selN vs (i + j) def.
Proof.
  induction i; intros; auto.
  destruct vs; simpl; auto.
Qed.

Hint Rewrite skipn_selN using omega : lists.

Lemma skipn_seq : forall n a b, skipn n (seq a b) = seq (a + n) (b - n).
Proof.
  induction n; intros.
  rewrite plus_0_r, Nat.sub_0_r; auto.
  destruct b; auto.
  simpl.
  rewrite IHn.
  f_equal; omega.
Qed.

Hint Rewrite skipn_seq : lists.

Lemma skipN_updN' : forall T (v : T) vs i j,
  i > j
  -> skipn i (updN vs j v) = skipn i vs.
Proof.
  induction vs; destruct i, j; simpl; intuition; omega.
Qed.

Lemma skipn_updN : forall T (v : T) vs i j,
  i >= j
  -> match updN vs j v with
       | nil => nil
       | _ :: vs' => skipn i vs'
     end
     = match vs with
         | nil => nil
         | _ :: vs' => skipn i vs'
       end.
Proof.
  destruct vs, j; simpl; eauto using skipN_updN'.
Qed.


Lemma skipn_selN_skipn : forall off A (l : list A) def,
  off < length l ->
  skipn off l = selN l off def :: skipn (S off) l.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega; auto.
  destruct l; simpl in *; try omega.
  apply IHoff.
  omega.
Qed.

Lemma skipn_sub_S_selN_cons : forall A (l : list A) n def,
  n < length l ->
  skipn (length l - S n) l = selN l (length l - n - 1) def :: (skipn (length l - n) l).
Proof.
  intros.
  replace (length l - n) with (S (length l - n - 1)) at 2 by omega.
  rewrite <- skipn_selN_skipn by omega.
  f_equal; omega.
Qed.

Hint Rewrite skipn_updN using omega : lists.

Lemma updN_twice : forall T (l : list T) a v v',
  updN (updN l a v') a v = updN l a v.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; auto; simpl.
  rewrite IHl; auto.
Qed.


Hint Rewrite updN_twice : lists.

Lemma updN_comm : forall T (l : list T) a0 v0 a1 v1,
  a0 <> a1 ->
  updN (updN l a0 v0) a1 v1 = updN (updN l a1 v1) a0 v0.
Proof.
  induction l; simpl; intros; auto.
  destruct a0; destruct a1; simpl in *; try congruence.
  rewrite IHl by omega. auto.
Qed.

Lemma updN_firstn_skipn : forall T (l:list T) n v,
  n < length l ->
  updN l n v = firstn n l ++ v::nil ++ skipn (n+1) l.
Proof.
  intros.
  generalize dependent n.
  induction l; intros; simpl.
  inversion H.
  induction n; simpl.
  reflexivity.
  f_equal.
  apply IHl.
  simpl in H.
  omega.
Qed.

Theorem list_selN_ext' : forall len T (a b : list T) default,
  length a = len
  -> length b = len
  -> (forall pos, pos < len -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
  induction len; intros; destruct a; destruct b; simpl in *; try congruence.
  f_equal.
  apply (H1 0).
  omega.
  eapply IHlen; [ omega | omega | ].
  intros.
  apply (H1 (S pos)).
  omega.
Qed.

Theorem list_selN_ext : forall T (a b : list T) default,
  length a = length b
  -> (forall pos, pos < length a -> selN a pos default = selN b pos default)
  -> a = b.
Proof.
  intros. apply list_selN_ext' with (len:=length a) (default:=default); auto.
Qed.


Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.

Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
Proof.
  nth_selN nth_In.
Qed.

Lemma in_selN_exists : forall A l (a : A) def,
  In a l -> exists i, i < length l /\ selN l i def = a.
Proof.
  induction l; try easy; intros.
  inversion H; subst.
  exists 0; simpl; split; auto; omega.
  destruct (IHl a0 def H0).
  destruct H1.
  exists (S x); simpl; split; auto; omega.
Qed.

Lemma selN_split_r: forall A B (l : list (A * B)) i d,
  selN (snd (split l)) i (snd d) = snd (selN l i d).
Proof.
  induction l; cbn; intros.
  auto.
  destruct a, split.
  destruct i; cbn; auto.
Qed.

Lemma selN_split_l: forall A B (l : list (A * B)) i d,
  selN (fst (split l)) i (fst d) = fst (selN l i d).
Proof.
  induction l; cbn; intros.
  auto.
  destruct a, split.
  destruct i; cbn; auto.
Qed.

Lemma map_fst_split: forall A B (l : list (A * B)), map fst l = fst (split l).
Proof.
  induction l; cbn; auto.
  destruct a; cbn.
  destruct split eqn:?; cbn in *.
  congruence.
Qed.

Lemma map_snd_split: forall A B (l : list (A * B)), map snd l = snd (split l).
Proof.
  induction l; cbn; auto.
  destruct a; cbn.
  destruct split eqn:?; cbn in *.
  congruence.
Qed.

Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
  In x l \/ x = xn.
Proof.
  induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
  destruct (IHn l x xn H); auto.
Qed.

Lemma Forall_app: forall A f l (a : A),
  Forall f l -> f a -> Forall f (l ++ a :: nil).
Proof.
  intros.
  rewrite Forall_forall.
  rewrite Forall_forall in H.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; auto.
  simpl in H1.
  destruct H1.
  subst; auto.
  exfalso; auto.
Qed.

Lemma Forall_combine_r: forall A B F G (a : list A) (b : list B),
  length a = length b ->
  (forall x, F x <-> G (snd x)) ->
  Forall F (combine a b) <-> Forall G b.
Proof.
  induction a; destruct b; cbn in *; try congruence; intros.
  split; constructor.
  split; intros H'; inversion H'; constructor; subst.
  eapply H0 in H3; auto.
  eapply IHa; auto.
  eapply H0; auto.
  apply IHa; auto.
Qed.


Lemma Forall_append: forall A f (l1 l2:list A),
  Forall f l1 -> Forall f l2 -> Forall f (l1 ++ l2).
Proof.
  intros.
  rewrite Forall_forall in *.
  intros.
  apply in_app_or in H1.
  destruct H1.
  apply H; assumption.
  apply H0; assumption.
Qed.

Lemma forall_app_r : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P a.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
Qed.

Lemma forall_app_l : forall A P (a b : list A),
  Forall P (a ++ b) -> Forall P b.
Proof.
  intros; rewrite Forall_forall in *; firstorder.
Qed.

Lemma Forall_repeat: forall A (f:A -> Prop) a n,
  f a -> Forall f (repeat a n).
Proof.
  intros.
  rewrite Forall_forall.
  intros.
  apply repeat_spec in H0.
  congruence.
Qed.

Lemma Forall_updN : forall A (l : list A) a i P,
  Forall P l -> P a ->
  Forall P (updN l i a).
Proof.
  induction l; intros; auto.
  inversion H; subst; auto.
  simpl; destruct i; apply Forall_cons; auto.
Qed.


Lemma Forall_cons2 : forall A (l : list A) a f,
  Forall f (a :: l) -> Forall f l.
Proof.
  intros.
  rewrite Forall_forall in *; intros.
  apply H.
  apply in_cons; auto.
Qed.

Lemma Forall_combine_same : forall T T1 T2 (l : list T) P (f1 : T -> T1) (f2 : T -> T2),
  Forall (fun x => P (f1 x, f2 x)) l ->
  Forall P (combine (map f1 l) (map f2 l)).
Proof.
  induction l; simpl; intros.
  - constructor.
  - inversion H; subst.
    constructor; auto.
Qed.

Lemma concat_repeat: forall T n k (x : T),
  concat (repeat (repeat x k) n) = repeat x (n * k).
Proof.
  intros.
  erewrite concat_hom_repeat.
  autorewrite with lists.
  eauto.
  apply Forall_repeat; auto.
Qed.


(** crush any small goals.  Do NOT use for big proofs! *)
Ltac small_t' := intros; autorewrite with core; autorewrite with core in *;
           eauto; simpl in *; intuition; eauto.
Ltac small_t := repeat small_t'; subst; simpl; eauto.

Lemma forall_skipn: forall A n (l : list A) p,
  Forall p l -> Forall p (skipn n l).
Proof.
  induction n; small_t.
  destruct l; small_t.
  intros; apply IHn.
  eapply Forall_cons2; eauto.
Qed.


Lemma forall_firstn: forall A n (l : list A) p,
  Forall p l -> Forall p (firstn n l).
Proof.
  induction n; simpl; auto; intros.
  destruct l; auto.
  inversion H; subst.
  apply Forall_cons; auto.
Qed.

Lemma updN_selN_eq : forall T (l : list T) ix default,
  updN l ix (selN l ix default) = l.
Proof.
  induction l; auto.
  intros. destruct ix. auto. simpl. rewrite IHl. trivial.
Qed.

Lemma updN_app1 : forall t l l' (v:t) n,
  n < length l -> updN (l ++ l') n v = updN l n v ++ l'.
Proof.
  (* copied from proof of app_nth1 *)
  induction l.
  intros.
  inversion H.
  intros l' d n.
  case n; simpl; auto.
  intros; rewrite IHl; auto with arith.
Qed.

Lemma updN_app2 : forall t l l' (v:t) n,
  n >= length l -> updN (l ++ l') n v = l ++ updN l' (n - length l) v.
Proof.
  (* copied from proof of app_nth2 *)
  induction l.
  intros.
  simpl.
  rewrite <- minus_n_O; auto.
  intros l' d n.
  case n; simpl; auto.
  intros.
  inversion H.
  intros.
  rewrite IHl; auto with arith.
Qed.

Lemma updN_app_tail : forall T (l : list T) a v,
  updN (l ++ (a :: nil)) (length l) v = l ++ (v :: nil).
Proof.
  induction l; simpl; firstorder.
  rewrite IHl; auto.
Qed.

Lemma updN_concat : forall t a b m l (v:t), b < m ->
  Forall (fun sl => length sl = m) l ->
  updN (concat l) (b + a * m) v =
    concat (updN l a (updN (selN l a nil) b v)).
Proof.
  (* XXX this is almost exactly the same as selN_concat *)
  induction a; intros; destruct l; simpl; inversion H0.
  trivial.
  replace (b + 0) with b by omega. subst.
  rewrite updN_app1; auto.
  trivial.
  subst. remember (a * length l) as al. rewrite updN_app2 by omega.
  replace (b + (length l + al) - length l) with (b + al) by omega. subst.
  rewrite IHa; auto.
Qed.

Lemma selN_app1 : forall t l l' (d:t) n,
  n < length l -> selN (l ++ l') n d = selN l n d.
Proof.
  nth_selN app_nth1.
Qed.

Lemma selN_app2 : forall t l l' (d:t) n,
  n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
Proof.
  nth_selN app_nth2.
Qed.

Lemma selN_cons : forall A (a : A) l i def,
  i > 0 -> selN (a :: l) i def = selN l (i - 1) def.
Proof.
  intros.
  replace (a :: l) with ([a] ++ l) by (simpl; auto).
  rewrite selN_app2; simpl; auto.
Qed.

Theorem seq_right : forall b a, seq a (S b) = seq a b ++ (a + b :: nil).
Proof.
  induction b; simpl; intros.
  replace (a + 0) with (a) by omega; reflexivity.
  f_equal.
  replace (a + S b) with (S a + b) by omega.
  rewrite <- IHb.
  auto.
Qed.

Theorem seq_right_0 : forall b, seq 0 (S b) = seq 0 b ++ (b :: nil).
Proof.
  intros; rewrite seq_right; f_equal.
Qed.

Lemma selN_map_some_range : forall A (l : list A) idx a,
  selN (map (@Some _) l) idx None = Some a ->
  idx < length l.
Proof.
  induction l; simpl; intros.
  - congruence.
  - destruct idx; try omega.
    apply IHl in H; omega.
Qed.

Lemma map_updN : forall T U (v : T) (f : T -> U) vs i,
  map f (updN vs i v) = updN (map f vs) i (f v).
Proof.
  induction vs; auto; destruct i; simpl; f_equal; auto.
Qed.

Hint Rewrite map_updN : lists.

Theorem selN_map_seq' : forall T i n f base (default : T), i < n
  -> selN (map f (seq base n)) i default = f (i + base).
Proof.
  induction i; destruct n; simpl; intros; try omega; auto.
  replace (S (i + base)) with (i + (S base)) by omega.
  apply IHi; omega.
Qed.

Theorem selN_map_seq : forall T i n f (default : T), i < n
  -> selN (map f (seq 0 n)) i default = f i.
Proof.
  intros.
  replace i with (i + 0) at 2 by omega.
  apply selN_map_seq'; auto.
Qed.

Hint Rewrite selN_map_seq using ( solve [ auto ] ) : lists.

Lemma map_selN_seq: forall T (l : list T) n d,
  n = length l ->
  map (fun i => selN l i d) (seq 0 n) = l.
Proof.
  induction l; intros; subst; cbn in *.
  auto.
  f_equal.
  rewrite <- seq_shift.
  rewrite map_map. auto.
Qed.

Theorem selN_map : forall T T' l i f (default : T) (default' : T'), i < length l
  -> selN (map f l) i default = f (selN l i default').
Proof.
  induction l; simpl; intros; try omega.
  destruct i; auto.
  apply IHl; omega.
Qed.

Lemma in_selN_map : forall A B (l : list (A*B)) i def1 def2,
  i < length l
  -> In (selN (map fst l) i def1, selN (map snd l) i def2) l.
Proof.
  induction l; destruct i; simpl; firstorder.
  left; destruct a; auto.
Qed.

Theorem updN_map_seq_app_eq : forall T (f : nat -> T) len start (v : T) x,
  updN (map f (seq start len) ++ (x :: nil)) len v =
  map f (seq start len) ++ (v :: nil).
Proof.
  induction len; auto; simpl; intros.
  f_equal; auto.
Qed.

Theorem updN_map_seq_app_ne : forall T (f : nat -> T) len start (v : T) x pos, pos < len
  -> updN (map f (seq start len) ++ (x :: nil)) pos v =
     updN (map f (seq start len)) pos v ++ (x :: nil).
Proof.
  induction len; intros; try omega.
  simpl; destruct pos; auto.
  rewrite IHlen by omega.
  auto.
Qed.

Theorem updN_map_seq : forall T f len start pos (v : T), pos < len
  -> updN (map f (seq start len)) pos v =
     map (fun i => if eq_nat_dec i (start + pos) then v else f i) (seq start len).
Proof.
  induction len; intros; try omega.
  simpl seq; simpl map.
  destruct pos.
  - replace (start + 0) with (start) by omega; simpl.
    f_equal.
    + destruct (eq_nat_dec start start); congruence.
    + apply map_ext_in; intros.
      destruct (eq_nat_dec a start); auto.
      apply in_seq in H0; omega.
  - simpl; f_equal.
    destruct (eq_nat_dec start (start + S pos)); auto; omega.
    rewrite IHlen by omega.
    replace (S start + pos) with (start + S pos) by omega.
    auto.
Qed.

Lemma combine_l_nil : forall T R (a : list T), List.combine a (@nil R) = nil.
Proof.
  induction a; auto.
Qed.

Hint Rewrite combine_l_nil : lists.

Theorem firstn_combine_comm : forall n T R (a : list T) (b : list R),
  firstn n (List.combine a b) = List.combine (firstn n a) (firstn n b).
Proof.
  induction n; simpl; intros; auto.
  destruct a; simpl; auto.
  destruct b; simpl; auto.
  f_equal.
  auto.
Qed.

Theorem skipn_combine_comm : forall n T R (a : list T) (b : list R),
  match (List.combine a b) with
  | nil => nil
  | _ :: c => skipn n c
  end = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
  induction n.
  - simpl; intros.
    destruct a; simpl; auto.
    destruct b; simpl; auto.
    autorewrite with lists; auto.
  - intros.
    destruct a; [simpl; auto|].
    destruct b; [simpl; auto|].
    autorewrite with lists; auto.
    replace (skipn (S (S n)) (t :: a)) with (skipn (S n) a) by auto.
    replace (skipn (S (S n)) (r :: b)) with (skipn (S n) b) by auto.
    rewrite <- IHn.
    simpl; auto.
Qed.

Lemma skipn_combine_comm' : forall n T R (a : list T) (b : list R),
  skipn (S n) (List.combine a b) = List.combine (skipn (S n) a) (skipn (S n) b).
Proof.
  intros. apply skipn_combine_comm.
Qed.

Lemma skipn_combine : forall A B n (a : list A) (b : list B),
  length a = length b ->
  skipn n (combine a b) = combine (skipn n a) (skipn n b).
Proof.
  induction n; intros.
  simpl; auto.
  rewrite skipn_combine_comm'; auto.
Qed.

Lemma selN_last: forall A l n def (a : A),
  n = length l -> selN (l ++ a :: nil) n def = a.
Proof.
  unfold selN; induction l; destruct n; intros;
  firstorder; inversion H.
Qed.


Lemma selN_firstn: forall {A} (l:list A) i n d,
  i < n -> selN (firstn n l) i d = selN l i d.
Proof.
  induction l; destruct i, n; intros; try omega; auto.
  apply IHl; omega.
Qed.


Lemma selN_oob: forall A n l (def : A),
  length l <= n
  -> selN l n def = def.
Proof.
  induction n; destruct l; simpl; firstorder.
Qed.

Lemma selN_inb : forall A (l : list A) n d1 d2,
  n < length l ->
  selN l n d1 = selN l n d2.
Proof.
  induction l; destruct n; intros; simpl; firstorder; inversion H.
Qed.

Lemma selN_app: forall A n l l' (def : A),
  n < length l
  -> selN (l ++ l') n def = selN l n def.
Proof.
  induction n; destruct l; simpl; firstorder; inversion H.
Qed.


Lemma firstn_app2: forall A n (l1 l2 : list A),
  n = length l1 -> firstn n (l1 ++ l2) = l1.
Proof.
  induction n; destruct l1; intros; inversion H; auto; subst.
  unfold firstn; simpl.
  rewrite IHn; auto.
Qed.


Lemma skipn_oob: forall T n (l : list T),
  n >= length l -> skipn n l = nil.
Proof.
  unfold skipn; induction n; destruct l; intros; auto.
  inversion H.
  apply IHn; firstorder.
Qed.

Lemma updN_oob: forall T l i (v : T),
  i >= length l -> updN l i v = l.
Proof.
  unfold updN; induction l; destruct i; intros; auto.
  inversion H.
  rewrite IHl; firstorder.
Qed.


Lemma firstn_oob: forall A (l : list A) n,
  n >= length l -> firstn n l = l.
Proof.
  unfold firstn; induction l; destruct n; intros; firstorder.
  rewrite IHl; firstorder.
Qed.

Lemma firstn_exact: forall A (l : list A),
  firstn (length l) l = l.
Proof.
  intros; rewrite firstn_oob; auto.
Qed.


Lemma firstn_firstn : forall A (l : list A) n1 n2 ,
  firstn n1 (firstn n2 l) = firstn (Init.Nat.min n1 n2) l.
Proof.
  induction l; destruct n1, n2; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma firstn_all : forall A (l : list A), firstn (length l) l = l.
Proof. induction l as [| ? ? H]; simpl; [reflexivity | now rewrite H]. Qed.

Lemma firstn_plusone_selN : forall A n (l : list A) def,
  n < length l
  -> firstn (n + 1) l = firstn n l ++ (selN l n def :: nil).
Proof.
  induction n; destruct l; intros; simpl in *; firstorder.
  rewrite IHn with (def:=def) by omega; auto.
Qed.

Definition firstn_plusone_selN' : forall A n l (x: A) def,
  x = selN l n def ->
  n < length l ->
  firstn (n + 1) l = firstn n l ++ x::nil.
Proof.
  intros.
  rewrite H.
  apply firstn_plusone_selN; auto.
Qed.

Lemma firstn_S_selN : forall A n l (def : A),
  n < length l ->
  firstn (S n) l = firstn n l ++ [ (selN l n def) ].
Proof.
  intros.
  replace (S n) with (n + 1) by omega.
  apply firstn_plusone_selN; auto.
Qed.

Lemma firstn_S_selN_expand : forall A n l (def : A),
  n < length l ->
  match l with
  | nil => nil
  | a :: l => a :: firstn n l
  end = firstn n l ++ [ (selN l n def) ].
Proof.
  intros.
  rewrite <- firstn_S_selN by auto.
  simpl; auto.
Qed.

Lemma firstn_updN_oob: forall A (l : list A) n i def,
  n <= i -> firstn n (updN l i def) = firstn n l.
Proof.
  induction l; destruct n; destruct i; intros; simpl; auto.
  inversion H.
  rewrite IHl by omega; auto.
Qed.

Lemma firstn_app_updN_eq : forall A l n (x : A),
  n < length l
  -> (firstn n l) ++ x :: nil = firstn (n + 1) (updN l n x).
Proof.
  intros.
  rewrite firstn_plusone_selN with (def := x).
  rewrite selN_updN_eq by omega.
  rewrite firstn_updN_oob; auto.
  rewrite length_updN; auto.
Qed.


Lemma length_not_nil : forall A (l : list A),
  l <> nil <-> length l > 0.
Proof.
  split; induction l; simpl; firstorder.
Qed.

Lemma length_not_nil' : forall A (l : list A),
  l <> nil <-> length l <> 0.
Proof.
  split; intros.
  apply length_not_nil in H; omega.
  apply length_not_nil; omega.
Qed.

Lemma firstn_is_nil : forall A n (l : list A),
  n > 0 -> firstn n l = nil -> l = nil.
Proof.
  induction n; destruct l; firstorder.
  simpl in H0; inversion H0.
Qed.

Lemma removelast_firstn_sub : forall A n (l : list A),
  n > 0 -> n <= length l
  -> removelast (firstn n l) = firstn (n - 1) l.
Proof.
  intros.
  replace n with (S (n - 1)) by omega.
  replace (S (n - 1) - 1) with (n - 1) by omega.
  apply removelast_firstn; omega.
Qed.

Lemma firstn_nil : forall A n,
  firstn n nil = @nil A.
Proof.
  induction n; firstorder.
Qed.

Lemma firstn_cons : forall A n (a : A) l,
  firstn (S n) (a :: l) = a :: firstn n l.
Proof.
  induction n; intros.
  simpl; auto.
  simpl; f_equal.
Qed.

Lemma firstn_length_l : forall A (l : list A) n,
  n <= length l -> length (firstn n l) = n.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_l; auto.
Qed.

Lemma firstn_length_l_iff : forall A (l : list A) n,
  n <= length l <-> length (firstn n l) = n.
Proof.
  intros.
  split.
  - intros.
    apply firstn_length_l; auto.
  - intros.
    rewrite firstn_length in H.
    apply Nat.min_l_iff; auto.
Qed.

Lemma firstn_length_r : forall A (l : list A) n,
  n >= length l -> length (firstn n l) = length l.
Proof.
  intros.
  rewrite firstn_length.
  rewrite Nat.min_r; auto.
Qed.

Lemma skipn_length: forall A n (l : list A),
  length (skipn n l) = length l - n.
Proof.
  induction n; destruct l; intros; firstorder.
Qed.

Lemma skipn_nil : forall A n,
  skipn n nil = @nil A.
Proof.
  induction n; firstorder.
Qed.

Lemma removeN_nil : forall A n,
  removeN nil n = (@nil A).
Proof.
  induction n; firstorder.
Qed.

Lemma cons_nil_app : forall A l r (a : A),
  (l ++ (a :: nil)) ++ r = l ++ a :: r.
Proof.
  intros.
  rewrite app_assoc_reverse.
  simpl; auto.
Qed.

Local Hint Resolve cons_nil_app.

Lemma firstn_app_r : forall T i (b a : list T),
  firstn (length a + i) (a ++ b) = a ++ (firstn i b).
Proof.
  induction i; firstorder.
  rewrite firstn_app2 by omega.
  simpl; rewrite app_nil_r; auto.

  destruct b.
  simpl; rewrite app_nil_r.
  rewrite firstn_oob; auto; omega.
  rewrite firstn_cons.
  replace (length a + S i) with (length (a ++ (t :: nil)) + i).
  replace (a ++ t :: b) with ((a ++ (t :: nil)) ++ b) by auto.
  rewrite IHi; auto.
  rewrite app_length; simpl; omega.
Qed.

Lemma firstn_app_l: forall A (a b: list A) n,
  n <= length a ->
  firstn n (a ++ b) = firstn n a.
Proof.
  induction a; intros; simpl in *.
  inversion H. auto.
  destruct n; simpl in *; auto.
  rewrite IHa by omega; auto.
Qed.

Lemma skipn_app : forall T (a b : list T),
  skipn (length a) (a ++ b) = b.
Proof.
  induction a; firstorder.
Qed.

Lemma skipn_app_eq : forall T (a b : list T) n,
  length a = n -> skipn n (a ++ b) = b.
Proof.
  intros.
  rewrite <- H.
  apply skipn_app.
Qed.

Lemma skipn_app_r : forall T i (b a : list T),
  skipn (length a + i) (a ++ b) = skipn i b.
Proof.
  induction i; firstorder.
  replace (length a + 0) with (length a) by omega.
  rewrite skipn_app; simpl; auto.

  destruct a; destruct b; simpl; firstorder.
  rewrite app_nil_r.
  rewrite skipn_oob; auto; omega.
  rewrite <- IHi with (a := a ++ (t0 :: nil)).
  rewrite cons_nil_app.
  f_equal.
  rewrite app_length; simpl; omega.
Qed.

Lemma skipn_app_l : forall T i (a b : list T),
  i <= length a ->
  skipn i (a ++ b) = (skipn i a) ++ b.
Proof.
  intros.
  generalize dependent a.
  induction i; intros; firstorder.
  induction a; simpl; firstorder.
  inversion H.
Qed.

Lemma skipn_app_split: forall T (a b : list T) n,
  skipn n (a ++ b) = skipn n a ++ skipn (n - length a) b.
Proof.
  intros.
  destruct (lt_dec n (length a)).
  rewrite skipn_app_l by omega.
  rewrite not_le_minus_0 by omega.
  auto.
  replace n with (length a + (n - length a)) at 1 by omega.
  rewrite skipn_app_r.
  rewrite skipn_oob with (l := a) by omega.
  auto.
Qed.

Lemma removeN_app_r : forall T (b a : list T) i,
  removeN (a ++ b) (length a + i) = a ++ (removeN b i).
Proof.
  unfold removeN; intros.
  rewrite firstn_app_r.
  replace (S (length a + i)) with (length a + (S i)) by omega.
  rewrite skipn_app_r.
  apply app_assoc_reverse.
Qed.

Lemma firstn_repeat : forall T m n (v : T),
  n <= m -> firstn n (repeat v m) = repeat v n.
Proof.
  induction m; simpl; intros.
  replace n with 0 by omega.
  firstorder.

  unfold repeat at 1; fold repeat.
  destruct n.
  unfold repeat; simpl; auto.

  rewrite firstn_cons.
  rewrite IHm by omega; auto.
Qed.

Lemma skipn_repeat' : forall A (v : A) m n,
  n <= m -> skipn n (repeat v m) = repeat v (m - n).
Proof.
  induction m; simpl; intros.
  inversion H; subst; simpl; auto.
  destruct n; auto.
  rewrite <- IHm; auto.
  omega.
Qed.

Lemma skipn_repeat : forall A (v : A) m n,
  skipn n (repeat v m) = repeat v (m - n).
Proof.
  intros; destruct (le_dec n m).
  apply skipn_repeat'; auto.
  rewrite skipn_oob.
  replace (m - n) with 0 by omega; simpl; auto.
  rewrite repeat_length; omega.
Qed.

Lemma app_repeat : forall T m n (v : T),
  repeat v m ++ repeat v n = repeat v (m + n).
Proof.
  induction m; unfold repeat; firstorder; fold repeat.
  rewrite <- app_comm_cons.
  rewrite IHm.
  replace (S m + n) with (S (m + n)) by omega.
  auto.
Qed.

Lemma repeat_app_tail : forall T n (a : T),
  repeat a (S n) = repeat a n ++ (a :: nil).
Proof.
  induction n; intros; simpl; auto.
  unfold repeat; fold repeat; f_equal.
  rewrite <- IHn.
  auto.
Qed.

Lemma removeN_repeat : forall T n i (e : T),
   n > 0 -> i < n
   -> removeN (repeat e n) i = repeat e (n - 1).
Proof.
  intros.
  unfold removeN.
  rewrite firstn_repeat by omega.
  rewrite skipn_repeat by omega.
  rewrite app_repeat.
  f_equal; omega.
Qed.

(* Local Opaque pow2. *)

Lemma firstn_nonnil : forall T (l : list T) n, 0 < n -> l <> nil ->
  exists e l', firstn n l = e :: l'.
Proof.
  destruct l; simpl; intros; try congruence.
  destruct n; simpl; try omega.
  eauto.
Qed.

Lemma skipn_nonnil : forall T (l : list T) n, n < length l ->
  exists e l', skipn n l = e :: l'.
Proof.
  induction l; simpl; intros; try omega.
  destruct n.
  exists a; exists l; eauto.
  destruct (IHl n); try omega.
  destruct H0.
  eauto.
Qed.

Lemma firstn_sum_split : forall A n off (l: list A),
  firstn (n+off) l = firstn n l ++ firstn off (skipn n l).
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - reflexivity.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + f_equal.
      apply IHn.
Qed.

Lemma skipn_sum_split : forall A n k (l: list A),
  skipn n l = firstn k (skipn n l) ++ skipn (n+k) l.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; simpl.
  - symmetry; apply firstn_skipn.
  - induction l; simpl.
    + rewrite firstn_nil.
      reflexivity.
    + rewrite <- skipn_skipn'.
      symmetry; apply firstn_skipn.
Qed.

Lemma skipn_sum_split' : forall A n off1 off2 (l: list A),
  off1 <= off2 ->
  skipn (n+off1) l =
    firstn (off2 - off1) (skipn (n+off1) l) ++ skipn (n+off2) l.
Proof.
  intros.
  replace (n+off2) with (n+off1 + (off2 - off1)) by omega.
  apply skipn_sum_split.
Qed.

Lemma firstn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  firstn (n1 + n2) (l1 ++ l2) = l1 ++ firstn n2 l2.
Proof.
  intros.
  rewrite firstn_sum_split.
  rewrite H.
  rewrite firstn_app2 by reflexivity.
  rewrite skipn_app.
  reflexivity.
Qed.

Lemma skipn_sum_app : forall A (l1 l2: list A) n1 n2,
  n1 = length l1 ->
  skipn (n1 + n2) (l1 ++ l2) = skipn n2 l2.
Proof.
  intros.
  rewrite H.
  rewrite <- skipn_skipn'.
  rewrite skipn_app.
  reflexivity.
Qed.

Lemma firstn_double_skipn : forall A n len1 len2 (l:list A),
  len1 + n <= len2 ->
  firstn len1 (skipn n (firstn len2 l)) = firstn len1 (skipn n l).
Proof.
  intros.

  case_eq (lt_dec (length l) len2); intros.
  - rewrite firstn_oob with (n := len2) by omega.
    auto.
  - rewrite <- firstn_skipn with (n := len2) (l := l) at 2.
    rewrite skipn_app_l.
    rewrite firstn_app_l.
    auto.
    rewrite skipn_length.
    all: rewrite firstn_length_l; omega.
Qed.

Lemma firstn_skipn_subslice : forall A n1 len1 n2 len2 (l:list A),
  len1 + n1 <= len2 ->
  firstn len1 (skipn n1 (firstn len2 (skipn n2 l))) =
    firstn len1 (skipn (n1+n2) l).
Proof.
  intros.
  rewrite firstn_double_skipn; auto.
  rewrite skipn_skipn; auto.
Qed.

(* several facts about concat on lists of equally-sized
   (homogeneous) lists *)
Lemma concat_hom_length : forall A (lists: list (list A)) k,
  Forall (fun sublist => length sublist = k) lists ->
  length (concat lists) = (length lists) * k.
Proof.
  intros.
  induction lists.
  rewrite concat_nil.
  simpl; reflexivity.
  rewrite concat_cons.
  rewrite app_length.
  simpl.
  rewrite IHlists.
  rewrite Forall_forall in H.
  replace k with (length a).
  reflexivity.
  apply H; apply in_cons_head.
  eapply Forall_cons2.
  eassumption.
Qed.

Lemma concat_hom_firstn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  firstn (n * k) (concat lists) = concat (firstn n lists).
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite firstn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + rewrite firstn_cons.
     rewrite concat_cons.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'; apply in_cons_head.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite firstn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.

(* copied concat_hom_firstn proof, s/firstn/skipn/
   (except for firstn_cons, that becomes simpl) *)
Lemma concat_hom_skipn : forall A (lists: list (list A)) n k,
  Forall (fun sublist => length sublist = k) lists ->
  skipn (n * k) (concat lists) = concat (skipn n lists).
Proof.
  intros.
  generalize dependent n.
  induction lists; intros; simpl.
  repeat (rewrite skipn_nil).
  reflexivity.
  case_eq n; intros.
   + reflexivity.
   + simpl.
     assert (H' := H).
     rewrite Forall_forall in H'.
     assert (length a = k) as Hk.
     apply H'. left; reflexivity.
     replace (S n0 * k) with (k + n0 * k) by auto.
     rewrite <- Hk.
     rewrite skipn_app_r.
     f_equal.
     rewrite Hk.
     apply IHlists.
     eapply Forall_cons2.
     eassumption.
Qed.

Lemma concat_hom_updN_first_skip : forall A n k (lists: list (list A)) (l: list A),
  Forall (fun sublist => length sublist = k) lists ->
  n < length lists ->
  firstn (n * k) (concat lists) ++ l ++
  skipn (n * k + k) (concat lists) = concat (updN lists n l).
Proof.
  intros.
  rewrite updN_firstn_skipn by assumption.
  rewrite concat_app.
  rewrite concat_cons.
  rewrite concat_app.
  rewrite concat_nil.
  rewrite app_nil_l.
  f_equal.
  apply concat_hom_firstn; assumption.
  f_equal.
  replace (n * k + k) with ((n + 1) * k).
  apply concat_hom_skipn; assumption.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.

Lemma concat_hom_subselect_firstn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  firstn off (selN l n def) = firstn off (concat (skipn n l)).
Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  symmetry; apply firstn_app_l.
  rewrite H2.
  assumption.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption.
Qed.

Lemma concat_hom_subselect_skipn : forall A n off k (l: list (list A)) (def: list A),
  Forall (fun sublist => length sublist = k) l ->
  off <= k ->
  n < length l ->
  skipn off (selN l n def) =
    firstn (k - off) (skipn off (concat (skipn n l))).
 Proof.
  intros.
  generalize dependent off.
  generalize dependent l.
  induction n; intros; simpl.
  induction l; simpl.
  inversion H1. (* impossible *)
  rewrite Forall_forall in H.
  assert (length a = k).
  apply H; apply in_cons_head.
  rewrite skipn_app_l by omega.
  rewrite firstn_app2.
  reflexivity.
  rewrite skipn_length; omega.
  destruct l; simpl.
  inversion H1. (* impossible *)
  apply IHn; firstorder.
  eapply Forall_cons2; eassumption.
Qed.

Fact div_ge_subt : forall a b, b <> 0 -> (a - b) / b = a / b - 1.
Proof.
  intros.
  destruct (le_lt_dec b a).
  apply plus_minus.
  rewrite plus_comm.
  eapply Nat.div_add in H.
  rewrite Nat.mul_1_l in *.
  erewrite Nat.sub_add in * by eassumption.
  eassumption.
  repeat rewrite Nat.div_small by omega. auto.
Qed.

Fact mod_subt : forall a b, b >= a -> (b - a) mod a = b mod a.
Proof.
  intros.
  destruct (le_lt_dec a 0). intuition.
  rewrite <- Nat.mod_add with (b := 1) by omega.
  rewrite Nat.mul_1_l.
  rewrite Nat.sub_add by omega.
  auto.
Qed.

Lemma selN_selN_firstn_hom : forall T (l : list (list T)) k nvalid off d1 d2 d3,
  Forall (fun sublist : list T => length sublist = k) (firstn nvalid l) ->
  off < nvalid * k ->
  off < k * length l -> selN (selN l (off / k) d1) (off mod k) d2 = selN (concat l) off d3.
Proof.
  induction l; intros;
    assert (k > 0) by (destruct (Nat.eq_dec k 0); intuition; subst; intuition).
  rewrite mult_0_r in *; omega.
  destruct nvalid; [> omega | ].
  match goal with [H : Forall _ _ |- _] => inversion H end; subst.
  destruct (lt_dec off (length a)).
  - simpl; rewrite selN_app, Nat.div_small, Nat.mod_small; auto.
    apply selN_inb; auto.
  - rewrite Nat.nlt_ge in *.
    rewrite selN_cons.
    simpl in *; rewrite mult_comm in *; simpl in *; rewrite mult_comm in *.
    simpl; rewrite selN_app2 by auto.
    erewrite <- IHl by (eauto; omega).
    rewrite mod_subt; auto.
    rewrite <- div_ge_subt by omega.
    reflexivity.
    simpl in *; rewrite mult_comm in *; simpl in *; rewrite mult_comm in *.
    apply Nat.div_str_pos; omega.
Qed.

Lemma skipn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  skipn n (concat l) = skipn (n mod k) (selN l (n / k) nil) ++ concat (skipn (S (n / k)) l).
Proof.
  induction l; cbn; intros.
  repeat rewrite skipn_nil; auto.
  inversion H; subst.
  destruct (lt_dec n (length a)).
  rewrite skipn_app_l by omega.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  replace n with (length a + (n - (length a))) at 1 by omega.
  rewrite skipn_app_r.
  rewrite IHl by auto.
  rewrite mod_subt by omega.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Lemma firstn_hom_concat: forall T k (l : list (list T)) n,
  Forall (fun x => length x = k) l ->
  k <> 0 ->
  firstn n (concat l) = concat (firstn (n / k) l) ++ firstn (n mod k) (selN l (n / k) nil).
Proof.
  induction l; cbn; intros.
  repeat rewrite firstn_nil; auto.
  inversion H; subst.
  destruct (lt_dec n (length a)).
  rewrite firstn_app_l by omega.
  rewrite Nat.mod_small by auto.
  rewrite Nat.div_small by auto.
  auto.
  rewrite firstn_app by omega.
  rewrite firstn_oob by omega.
  rewrite IHl by auto.
  rewrite mod_subt by omega.
  rewrite div_ge_subt by auto.
  rewrite <- Nat.div_small_iff in * by auto.
  destruct (n / length a) eqn:?.
  congruence.
  cbn.
  rewrite Nat.sub_0_r.
  auto using app_assoc.
Qed.

Lemma selN_selN_hom : forall T (l : list (list T)) k off def,
  Forall (fun sublist => length sublist = k) l ->
  off < k * length l ->
  selN (selN l (off / k) nil) (Nat.modulo off k) def = selN (concat l) off def.
Proof.
  intros.
  eapply selN_selN_firstn_hom; auto.
  apply forall_firstn; auto.
  rewrite mult_comm; eauto.
Qed.

Definition combine_updN : forall A B i a b (va:A) (vb:B),
  List.combine (updN a i va) (updN b i vb) = updN (List.combine a b) i (va, vb).
Proof.
  induction i; intros; destruct a, b; simpl; auto.
  rewrite IHi; auto.
Qed.

Lemma combine_updN_l: forall A B (a : list A) (b : list B) i x d,
  combine (updN a i x) b = updN (combine a b) i (x, selN b i d).
Proof.
  intros.
  erewrite <- updN_selN_eq with (l := b) at 1.
  eauto using combine_updN.
Qed.

Lemma combine_updN_r: forall A B (a : list A) (b : list B) i x d,
  combine a (updN b i x) = updN (combine a b) i (selN a i d, x).
Proof.
  intros.
  erewrite <- updN_selN_eq with (l := a) at 1.
  eauto using combine_updN.
Qed.

Lemma selN_combine : forall Ta Tb i a b (a0:Ta) (b0:Tb),
  length a = length b
  -> selN (List.combine a b) i (a0, b0) = pair (selN a i a0) (selN b i b0).
Proof.
  induction i; destruct a, b; intros; inversion H; auto.
  simpl; apply IHi; assumption.
Qed.

Lemma combine_length_eq: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length a.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.

Lemma combine_length_eq2: forall A B (a : list A) (b : list B),
  length a = length b
  -> length (List.combine a b) = length b.
Proof.
  intros.
  rewrite combine_length.
  rewrite H; intuition.
Qed.


Theorem combine_app: forall A B (al ar : list A) (bl br: list B),
  length al = length bl
  -> List.combine (al ++ ar) (bl ++ br) 
     = (List.combine al bl) ++ (List.combine ar br).
Proof.
  induction al; destruct bl; simpl; intros; try omega; auto.
  f_equal.
  apply IHal; omega.
Qed.

Theorem removeN_updN : forall V l i (v : V),
   removeN (updN l i v) i = removeN l i.
Proof.
   unfold removeN; intros.
   rewrite firstn_updN; auto.
   simpl; rewrite skipn_updN; auto.
Qed.

Theorem removeN_oob: forall A (l : list A) i,
  i >= length l -> removeN l i = l.
Proof.
  intros; unfold removeN.
  rewrite firstn_oob by auto.
  rewrite skipn_oob by auto.
  firstorder.
Qed.

Lemma removeN_head: forall A l i (a : A),
  removeN (a :: l) (S i) = a :: (removeN l i).
Proof.
  unfold removeN; firstorder.
Qed.

Theorem removeN_combine: forall A B i (a : list A) (b : list B),
  removeN (List.combine a b) i = List.combine (removeN a i) (removeN b i).
Proof.
  induction i; destruct a, b; intros; simpl; auto.
  - unfold removeN at 2; simpl.
    repeat rewrite removeN_oob by auto.
    induction a0; firstorder.
  - rewrite removeN_head.
    rewrite IHi.
    unfold removeN; firstorder.
Qed.

Lemma removeN_length: forall A (l : list A) i,
  i < length l -> length (removeN l i) = length l - 1.
Proof.
  unfold removeN; induction l; intros; simpl.
  unfold length in H; omega.
  rewrite app_length.
  rewrite firstn_length; rewrite Nat.min_l; simpl in *; try omega.
  rewrite skipn_length; omega.
Qed.


Lemma removeN_length_eq: forall A B (a : list A) (b : list B) i,
  i < length a -> i < length b
  -> length (removeN a i) = length (removeN b i)
  -> length a = length b.
Proof.
  intros; destruct (Nat.eq_dec (length a) 0); try omega.
  rewrite removeN_length in H1; auto.
  rewrite removeN_length in H1; auto.
  omega.
Qed.


Lemma removeN_tail: forall A (l : list A) a,
  removeN (l ++ a :: nil) (length l) = l.
Proof.
  intros; unfold removeN.
  rewrite skipn_oob.
  rewrite firstn_app2; firstorder.
  rewrite app_length; simpl; omega.
Qed.


Lemma selN_removelast : forall A n l (def : A),
  n < length l - 1
  -> selN (removelast l) n def = selN l n def.
Proof.
  induction l using rev_ind; destruct n;
  intros; simpl; intuition;
  rewrite removelast_app; try congruence;
  simpl; rewrite app_nil_r;
  rewrite selN_app; auto;
  rewrite app_length in H; simpl in H; omega.
Qed.


Lemma length_removelast : forall A (l : list A),
  l <> nil -> length (removelast l) = length l - 1.
Proof.
  induction l using rev_ind; intros; simpl; auto.
  rewrite app_length; simpl.
  rewrite removelast_app; firstorder.
  unfold removelast; rewrite app_length; simpl.
  omega.
Qed.

Lemma removeN_removelast : forall A (l : list A),
  length l > 0
  -> removeN l (length l - 1) = removelast l.
Proof.
  induction l using rev_ind; intros; simpl; firstorder.
  rewrite removelast_app; simpl.
  rewrite app_nil_r.
  rewrite app_length; simpl.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite removeN_tail; auto.
  congruence.
Qed.

Lemma in_removeN : forall T (l : list T) i x,
  In x (removeN l i) -> In x l.
Proof.
  unfold removeN.
  intros.
  rewrite <- firstn_skipn with (n := i).
  rewrite in_app_iff in *.
  intuition.
  right.
  eapply in_skipn_in with (n := 1).
  rewrite skipn_skipn.
  auto.
Qed.

Lemma in_removeN_neq: forall T (l : list T) x d i,
  In x l ->
  selN l i d <> x ->
  In x (removeN l i).
Proof.
  unfold removeN.
  intros.
  erewrite <- firstn_skipn with (n := i) in H.
  rewrite in_app_iff in *.
  intuition.
  right.
  eapply in_skipn_S; eauto.
Qed.

Lemma in_combine_ex_l: forall A B (a : list A) (b : list B),
  length a >= length b ->
  forall y, In y b -> exists x, In (x, y) (List.combine a b).
Proof.
  induction a; cbn; intros.
  destruct b; cbn in *; intuition omega.
  destruct b; cbn in *; intuition; subst.
  eauto.
  edestruct IHa; eauto.
  omega.
Qed.

Lemma in_combine_ex_r: forall A B (a : list A) (b : list B),
  length a <= length b ->
  forall x, In x a -> exists y, In (x, y) (List.combine a b).
Proof.
  induction a; cbn; intros.
  omega.
  destruct b; cbn in *; intuition; subst; try omega.
  eauto.
  edestruct IHa; eauto.
  omega.
Qed.

Theorem firstn_removelast_eq : forall V (l : list V),
  length l > 0
  -> firstn (length l - 1) l = removelast l.
Proof.
  destruct l using rev_ind; firstorder.
  rewrite app_length; simpl.
  rewrite removelast_app; simpl; try congruence.
  replace (length l + 1 - 1) with (length l) by omega.
  rewrite firstn_app2; auto.
  rewrite app_nil_r; auto.
Qed.

Lemma firstn_app_le : forall A (a b : list A) n,
  length a <= n ->
    firstn n (a ++ b) = a ++ firstn (n - length a) b.
Proof.
  induction a; simpl; intros.
  rewrite <- minus_n_O; auto.
  destruct n; try omega; simpl.
  f_equal.
  apply IHa.
  omega.
Qed.

Lemma firstn_repeat_le : forall n m A (x : A),
  n <= m ->
    firstn n (repeat x m) = repeat x n.
Proof.
  induction n; simpl; intros; auto.
  destruct m; try omega; simpl.
  f_equal.
  apply IHn.
  omega.
Qed.

Lemma firstn_app_split : forall T (l1 l2 : list T) n,
  firstn n (l1 ++ l2) = firstn n l1 ++ firstn (n - length l1) l2.
Proof.
  intros.
  destruct (le_lt_dec n (length l1)).
  - rewrite firstn_app_l by auto.
    replace (_ - _) with 0 by omega. rewrite app_nil_r. auto.
  - rewrite firstn_app_le by omega.
    f_equal. rewrite firstn_oob by omega. auto.
Qed.

Lemma selN_skip_first : forall T (l:list T) n m p def,
  n + m < p ->
    selN l (n + m) def = selN (skipn n (firstn p l)) m def.
Proof.
  intros.
  rewrite skipn_selN.
  rewrite selN_firstn.
  reflexivity.
  assumption.
Qed.

Definition setlen A l n (def : A) :=
  firstn n l ++ (repeat def (n - length l)).

Lemma repeat_is_nil : forall T (v : T) n,
  n = 0 -> repeat v n = nil.
Proof.
  intros; subst; unfold repeat; auto.
Qed.

Lemma setlen_length : forall A l n (def : A),
  length (setlen l n def) = n.
Proof.
  unfold setlen; intros.
  rewrite app_length.
  rewrite repeat_length.
  destruct (le_lt_dec n (length l)).
  apply Nat.sub_0_le in l0 as Heq; rewrite Heq.
  rewrite firstn_length_l; auto.
  rewrite firstn_length_r; omega.
Qed.

Lemma setlen_nil : forall A n (def : A),
  setlen nil n def = repeat def n.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_nil.
  rewrite app_nil_l.
  rewrite Nat.sub_0_r; auto.
Qed.

Lemma list_isloate_len : forall A tl hd (x : A),
  length (hd ++ x :: tl) = length hd + S (length tl).
Proof.
  induction tl; intros; simpl; autorewrite with lists; simpl; auto.
Qed.

Lemma updN_0_skip_1: forall A l (a: A),
  length l > 0 -> updN l 0 a = a :: skipn 1 l .
Proof.
  intros; destruct l.
  simpl in H. omega.
  reflexivity.
Qed.

Lemma skipn_map_comm : forall A B n (l : list A) (f : A -> B),
  skipn n (map f l) = map f (skipn n l).
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
Qed.

Lemma firstn_map_comm : forall A B n (l : list A) (f : A -> B),
  firstn n (map f l) = map f (firstn n l).
Proof.
  induction n; intros; auto.
  destruct l; simpl; auto.
  rewrite IHn; auto.
Qed.

Lemma removeN_map_comm: forall T T' (f : T -> T') i l,
  removeN (map f l) i = map f (removeN l i).
Proof.
  unfold removeN.
  intros.
  rewrite firstn_map_comm, skipn_map_comm, map_app.
  auto.
Qed.

Lemma skipn_firstn_comm : forall A n m (l : list A),
  skipn n (firstn (n + m) l) = firstn m (skipn n l).
Proof.
  induction n; destruct l; intros; simpl; auto.
  rewrite firstn_nil; auto.
Qed.

Lemma setlen_app_r : forall A n (a b : list A) e0,
  n >= length a ->
  setlen (a ++ b) n e0 = a ++ setlen b (n - length a) e0.
Proof.
  unfold setlen; intros; simpl.
  rewrite firstn_app_le by auto.
  rewrite app_assoc.
  autorewrite with lists.
  f_equal; f_equal; omega.
Qed.

Lemma setlen_repeat : forall A m n (a : A),
  setlen (repeat a n) m a = repeat a m.
Proof.
  unfold setlen; intros.
  destruct (le_gt_dec m n).
  rewrite firstn_repeat by auto.
  rewrite repeat_app, repeat_length.
  replace (m + (m - n)) with m by omega; auto.
  
  rewrite firstn_oob by (rewrite repeat_length; omega).
  rewrite repeat_app, repeat_length.
  replace (n + (m - n)) with m by omega; auto.
Qed.

Lemma skipn_app_r_ge : forall A n (a b : list A),
  n >= length a ->
  skipn n (a ++ b) = skipn (n - length a) b.
Proof.
  induction n; intros; auto.
  replace a with (@nil A); auto.
  rewrite length_nil; auto; omega.
  destruct a, b; simpl; auto.
  rewrite app_nil_r, skipn_nil, skipn_oob; auto.
  simpl in H; omega.
  apply IHn.
  simpl in H; omega.
Qed.

Lemma firstn_map_exact : forall A B (l : list A) (f : A -> B),
  firstn (length l) (map f l) = map f l.
Proof.
  intros.
  rewrite firstn_map_comm.
  rewrite firstn_exact; auto.
Qed.


Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
  List.combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; rewrite <- surjective_pairing; auto.
Qed.

Lemma combine_map: forall T A' B' (l : list T) (f : _ -> A') (g : _ -> B'),
  map (fun x => (f x, g x)) l = combine (map f l) (map g l).
Proof.
  induction l; cbn; intros.
  auto.
  f_equal; eauto.
Qed.

Lemma combine_map': forall T T' A' B' (a : list T) (b : list T') (f : _ -> A') (g : _ -> B'),
  map (fun x => (f (fst x), g (snd x))) (combine a b) = combine (map f a) (map g b).
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn; auto.
  f_equal; eauto.
Qed.

Lemma combine_map_l : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine (map f a) b = map (fun ab => (f (fst ab), snd ab)) (combine a b).
Proof.
  intros.
  setoid_rewrite combine_map' with (g := id).
  rewrite map_id.
  auto.
Qed.

Lemma combine_map_r : forall A B C (a : list A) (b : list B) (f : _ -> C),
  combine a (map f b) = map (fun ab => (fst ab, f (snd ab))) (combine a b).
Proof.
  intros.
  setoid_rewrite combine_map' with (f := id).
  rewrite map_id.
  auto.
Qed.

Lemma map_fst_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map fst (List.combine a b) = a.
Proof.
  unfold map, List.combine; induction a; intros; auto.
  destruct b; try discriminate; simpl in *.
  rewrite IHa; [ auto | congruence ].
Qed.

Lemma map_snd_combine: forall A B (a: list A) (b: list B),
  length a = length b -> map snd (List.combine a b) = b.
Proof.
  unfold map, List.combine.
  induction a; destruct b; simpl; auto; try discriminate.
  intros; rewrite IHa; eauto.
Qed.

Lemma map_snd_updN : forall A B (l : list (A*B)) a v,
  map snd (updN l a v) = updN (map snd l) a (snd v).
Proof.
  induction l; intros; simpl; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma map_fst_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
  map fst ents = map fst (map (fun e => (fst e, f (snd e))) ents).
Proof.
  induction ents; simpl; auto; intros.
  f_equal.
  apply IHents.
Qed.

Lemma map_snd_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
  map snd (map (fun e => (fst e, f (snd e))) ents) = map f (map snd ents).
Proof.
  induction ents; simpl; auto; intros.
  f_equal.
  apply IHents.
Qed.

Lemma NoDup_skipn : forall A (l : list A) n,
  NoDup l -> NoDup (skipn n l).
Proof.
  induction l; simpl; intros; auto.
  rewrite skipn_nil; auto.
  inversion H; subst.
  destruct n; simpl; auto.
Qed.

Lemma NoDup_app_l : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup a.
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; constructor; eauto.
  intro; apply H2.
  apply in_or_app; eauto.
Qed.

Lemma NoDup_app_r : forall A (a b : list A),
  NoDup (a ++ b) -> NoDup b.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; eauto.
Qed.

Lemma NoDup_remove_mid : forall A (a b c : list A),
  NoDup (a ++ b ++ c) -> NoDup (a ++ c).
Proof.
  induction b using rev_ind; simpl; intros; eauto.
  eapply NoDup_remove_1.
  eapply IHb. rewrite <- app_assoc in H. eauto.
Qed.

Hint Resolve in_app_or.
Hint Resolve in_or_app.

Lemma not_In_NoDup_app : forall T (a : T) l1 l2,
  In a l1 -> NoDup (l1 ++ l2) -> ~ In a l2.
Proof.
  induction l1; simpl; intros; eauto.
  intuition; subst.
  inversion H0; subst; eauto.
  inversion H0; subst; eauto.
Qed.

Lemma in_nodup_split : forall T (a : T) l1 l2,
  In a (l1 ++ l2) -> NoDup (l1 ++ l2) -> ~ In a l2 -> In a l1.
Proof.
  induction l1; simpl; intros; eauto.
  intuition; subst.
  inversion H0; subst; eauto.
Qed.

Lemma NoDup_app_comm : forall T (l1 l2 : list T),
  NoDup (l1 ++ l2) ->
  NoDup (l2 ++ l1).
Proof.
  induction l2; simpl; intros; try rewrite app_nil_r in *; eauto.
  constructor.
  intro H'. apply in_app_or in H'.
  eapply NoDup_remove_2; eauto.
  apply in_or_app; intuition.
  eapply IHl2; eapply NoDup_remove_1; eauto.
Qed.

Lemma NoDup_3app_rev : forall T (l1 l2 l3 : list T),
  NoDup (l3 ++ l2 ++ l1) ->
  NoDup (l1 ++ l2 ++ l3).
Proof.
  induction l1; simpl; intros.
  rewrite app_nil_r in *. eapply NoDup_app_comm; eauto.
  rewrite app_assoc in H. apply NoDup_app_comm in H. simpl in H.
  inversion H; subst.
  constructor.
  - intro H'. apply H2.
    apply in_or_app. apply in_app_or in H'. intuition. right.
    apply in_or_app. apply in_app_or in H0. intuition.
  - eapply IHl1.
    apply NoDup_app_comm in H3. rewrite <- app_assoc in H3. eauto.
Qed.

Lemma in_nodup_firstn_not_skipn: forall T (l : list T) n x,
  NoDup l ->
  In x (firstn n l) -> ~In x (skipn n l).
Proof.
  intros.
  erewrite <- firstn_skipn in H.
  eapply not_In_NoDup_app; eauto.
Qed.

Lemma in_nodup_not_skipn_firstn: forall T (l : list T) n x,
  NoDup l -> In x l ->
  ~In x (skipn n l) -> In x (firstn n l).
Proof.
  intros.
  eapply in_nodup_split; rewrite ?firstn_skipn; eauto.
Qed.

Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
  In a (map fst l) -> exists b, In (a, b) l.
Proof.
  induction l; simpl; firstorder.
  destruct a; simpl in *; subst; eauto.
Qed.

Lemma setlen_In : forall A n l (a def : A),
  In a (setlen l n def)
  -> a = def \/ In a l.
Proof.
  unfold setlen; intros.
  destruct (le_dec n (length l)).
  right.
  rewrite repeat_is_nil in H by omega; rewrite app_nil_r in H.
  eapply in_firstn_in; eauto.
  apply in_app_or in H; destruct H.
  right. eapply in_firstn_in; eauto.
  left. eapply repeat_spec; eauto.
Qed.

Lemma updN_skipn : forall A l i n (v : A),
  updN (skipn n l) i v = skipn n (updN l (i + n) v).
Proof.
  induction l using rev_ind; intros; simpl.
  rewrite updN_oob; auto.
  rewrite skipn_nil; simpl; omega.

  destruct (lt_dec i (length l - n)).
  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app1 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto.
  f_equal; eauto.
  rewrite updN_app1 by omega.
  repeat rewrite skipn_app_r_ge by omega.
  rewrite length_updN, skipn_oob; simpl; auto; omega.

  destruct (le_dec n (length l)).
  rewrite skipn_app_l by auto.
  repeat rewrite updN_app2 by (try rewrite skipn_length; omega).
  setoid_rewrite skipn_app_l; autorewrite with lists; auto; f_equal.
  rewrite skipn_length; f_equal; omega.
  repeat rewrite skipn_oob; autorewrite with lists; simpl; auto; omega.
Qed.

Lemma setlen_skipn_updN_absorb : forall A (l : list A) m n i v def,
  i < n \/ i >= m + n ->
  setlen (skipn n (updN l i v)) m def = setlen (skipn n l) m def.
Proof.
  intros; destruct H.
  rewrite skipN_updN'; auto.
  unfold setlen.
  repeat rewrite <- skipn_firstn_comm.
  rewrite firstn_updN_oob by omega.
  repeat rewrite skipn_length.
  rewrite length_updN; auto.
Qed.

Lemma setlen_inbound : forall A n (l : list A) def,
  n <= length l ->
  setlen l n def = firstn n l.
Proof.
  unfold setlen; intros.
  replace (n - length l) with 0 by omega.
  simpl; rewrite app_nil_r; auto.
Qed.

Lemma setlen_oob : forall A n (l : list A) def,
  n >= length l ->
  setlen l n def = l ++ repeat def (n - length l).
Proof.
  unfold setlen; intros.
  rewrite firstn_oob by omega; auto.
Qed.

Lemma setlen_exact : forall A n (l : list A) def,
  n = length l ->
  setlen l n def = l.
Proof.
  unfold setlen; intros; subst.
  rewrite firstn_oob by omega; auto.
  rewrite Nat.sub_diag; simpl.
  rewrite app_nil_r; auto.
Qed.

Lemma selN_map_eq: forall T T' (f : T -> T') (l l' : list T) d,
  (forall i, f (selN l i d) = f (selN l' i d)) ->
  length l = length l' ->
  map f l = map f l'.
Proof.
  induction l; cbn; intros.
  rewrite length_nil; auto.
  autorewrite with list. auto.
  destruct l'; cbn in *. omega.
  rewrite (H 0).
  f_equal; auto.
  eapply IHl.
  intros i. apply (H (S i)).
  omega.
Qed.

Lemma combine_repeat : forall A B n (a : A) (b : B),
  combine (repeat a n) (repeat b n) = repeat (a, b) n.
Proof.
  induction n; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma Forall_selN : forall A (l : list A) P i def,
  Forall P l -> i < length l -> P (selN l i def).
Proof.
  intros.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.

Lemma selN_Forall : forall A (l : list A) (P : A -> Prop) def,
  (forall i, i < length l -> P (selN l i def)) ->
  Forall P l.
Proof.
  induction l; intros; eauto.
  apply Forall_cons.
  apply (H 0); simpl; omega.
  eapply IHl; intros.
  apply (H (S i)); simpl; omega.
Qed.

Theorem remove_not_In :
  forall T dec (a : T) l, ~ In a l -> remove dec a l = l.
Proof.
  induction l.
  auto.
  intro Hni. simpl.
  destruct (dec a a0).
  subst. destruct Hni. simpl. tauto.
  rewrite IHl. trivial.
  simpl in Hni. tauto.
Qed.

Theorem remove_still_In : forall T dec (a b : T) l,
  In a (remove dec b l) -> In a l.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  right; apply IHl; assumption.
  intro H. destruct H. subst. auto.
  right; apply IHl; assumption.
Qed.

Theorem remove_still_In_ne : forall T dec (a b : T) l,
  In a (remove dec b l) -> b <> a.
Proof.
  induction l; simpl; [tauto|].
  destruct (dec b a0).
  assumption.
  intro H. destruct H. subst. auto.
  apply IHl; assumption.
Qed.

Theorem remove_other_In : forall T dec (a b : T) l,
  b <> a -> In a l -> In a (remove dec b l).
Proof.
  induction l.
  auto.
  simpl. destruct (dec b a0).
  subst. intros. destruct H0; [subst; tauto | apply IHl; auto].
  simpl. intros. destruct H0; [left; auto | right; apply IHl; auto].
Qed.

Lemma NoDup_remove : forall T (l : list T) v EQ,
  NoDup l ->
  NoDup (remove EQ v l).
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  destruct (EQ v a); eauto.
  constructor; eauto.
  contradict H2.
  eapply remove_still_In; eauto.
Qed.

Lemma remove_cons_eq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) a,
  NoDup (a :: l) ->
  remove E a (a :: l) = l.
Proof.
  induction l; intros; subst.
  - simpl. 
    destruct (E a a); try congruence.
  - unfold remove.
    destruct (E a0 a0); subst; try congruence.
    destruct (E a0 a); subst. try congruence.
    + exfalso. inversion H.
      apply H2. constructor; auto.
    + unfold remove in IHl; simpl in IHl.
      specialize (IHl a0). 
      destruct (E a0 a0); subst; try congruence.
      rewrite IHl; auto.
      rewrite cons_app in H.
      rewrite cons_app with (l := l) in H.
      eapply NoDup_remove_mid in H; auto.
Qed.

Lemma remove_cons_neq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) a b,
  a <> b ->
  remove E a (b :: l) = b :: remove E a l.
Proof.
  induction l; intros; subst.
  - simpl.
    destruct (E a b); subst; try congruence.
  - unfold remove.
    destruct (E a0 b); subst; try congruence.
Qed.

Lemma remove_comm: forall T E x x' (l : list T),
  remove E x' (remove E x l) = remove E x (remove E x' l).
Proof.
  induction l; cbn; intros; auto.
  repeat (destruct E; cbn); congruence.
Qed.

Lemma remove_same: forall T E x y (l : list T),
  x = y ->
  remove E x (remove E y l) = remove E x l.
Proof.
  induction l; cbn; intros; auto.
  repeat (destruct E; cbn); subst.
  eauto.
  congruence.
  congruence.
  f_equal; eauto.
Qed.

Lemma remove_cons: forall T E x (l : list T),
  remove E x (x :: l) = remove E x l.
Proof.
  cbn; intros; destruct E; congruence.
Qed.


Lemma selN_cons_fold : forall A (a : A) l i def,
  match i with | O => a | S n' => selN l n' def end = selN (a :: l) i def.
Proof.
  intros; simpl; auto.
Qed.

Lemma removeN_0_skipn : forall A n (l : list A),
  removeN (skipn n l) 0 = skipn (S n) l.
Proof.
  induction n; destruct l; simpl; eauto.
Qed.


Lemma skipn_firstn_length_eq : forall A B (a : list A) (b : list B) n,
  length (firstn n a) = length (firstn n b) ->
  length (skipn n a) = length (skipn n b) ->
  length a = length b.
Proof.
  intros.
  repeat rewrite firstn_length in H.
  repeat rewrite skipn_length in H0.
  destruct (le_dec n (length a)); destruct (le_dec n (length b)).
  omega.
  rewrite Nat.min_l in H by auto.
  rewrite Nat.min_r in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_l in H by omega; subst.
  omega.
  rewrite Nat.min_r in H by omega.
  rewrite Nat.min_r in H by omega; subst.
  omega.
Qed.

Lemma Forall_map : forall A B (l : list A) P (f : A -> B),
  Forall (fun x => P (f x)) l <->
  Forall P (map f l).
Proof.
  induction l; simpl; intros.
  rewrite Forall_forall in *; firstorder.
  split; intros;
  inversion H; simpl; subst;
  apply Forall_cons; firstorder.
Qed.

Lemma Forall_map_l : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P (f a) b) l <->
  Forall (fun a => P a b) (map f l).
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.

Lemma Forall_map_r : forall A B C P (l : list A) (b : B) (f : A -> C),
  Forall (fun a => P b (f a)) l <->
  Forall (fun a => P b a) (map f l).
Proof.
  induction l; simpl; split; intros;
  try apply Forall_nil; inversion H;
  subst; firstorder.
  apply Forall_cons; firstorder.
Qed.

Lemma Forall_remove : forall A (l : list A) a P EQ,
  Forall P l ->
  Forall P (remove EQ a l).
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  destruct (EQ a0 a); eauto.
Qed.

Lemma forall2_length : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> length a = length b.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma forall2_forall : forall A B (a : list A) (b : list B) P,
  Forall2 P a b -> Forall (fun x => P (fst x) (snd x)) (combine a b).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma forall_forall2 : forall A B (a : list A) (b : list B) P,
  Forall (fun x => P (fst x) (snd x)) (combine a b) ->
  length a = length b ->
  Forall2 P a b.
Proof.
  induction a; destruct b; firstorder.
  inversion H0.
  inversion H0.
  inversion H; subst; simpl in *.
  constructor; auto.
Qed.

Lemma forall2_forall_l' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun a => exists b, P a b) la.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma forall2_forall_l : forall A B (la : list A) (lb : list B) P,
  Forall2 (fun a b => P a) la lb -> Forall P la.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma forall2_forall_r' : forall A B (la : list A) (lb : list B) P,
  Forall2 P la lb -> Forall (fun b => exists a, P a b) lb.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma forall2_forall_r : forall A B (la : list A) (lb : list B) P,
  Forall2 (fun a b => P b) la lb -> Forall P lb.
Proof.
  induction la; simpl; intros.
  inversion H. constructor.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma forall_forall2_l : forall A B (la : list A) (lb : list B) P,
  length la = length lb -> Forall P la -> Forall2 (fun a b => P a) la lb.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H0.
  constructor; eauto.
Qed.

Lemma forall_forall2_r : forall A B (la : list A) (lb : list B) P,
  length la = length lb -> Forall P lb -> Forall2 (fun a b => P b) la lb.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H0.
  constructor; eauto.
Qed.

Lemma forall2_impl : forall A B (la : list A) (lb : list B) (P Q : A -> B -> Prop),
  Forall2 P la lb ->
  Forall2 (fun a b => P a b -> Q a b) la lb ->
  Forall2 Q la lb.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  inversion H.
  inversion H.
  inversion H; subst.
  inversion H0; subst.
  constructor; eauto.
Qed.

Lemma forall2_lift : forall A B (la : list A) (lb : list B) (P : A -> B -> Prop),
  (forall a b, P a b) ->
  length la = length lb ->
  Forall2 P la lb.
Proof.
  induction la; simpl; intros; destruct lb; simpl in *; try congruence.
  constructor.
  constructor; eauto.
Qed.

Lemma forall2_selN : forall A B (a : list A) (b : list B) P n ad bd,
  Forall2 P a b ->
  n < length a ->
  P (selN a n ad) (selN b n bd).
Proof.
  intros.
  pose proof (forall2_length H).
  apply forall2_forall in H.
  eapply Forall_selN with (i := n) in H.
  erewrite selN_combine in H; eauto.
  rewrite combine_length_eq; auto.
Qed.

Lemma forall2_updN : forall A B P (a : list A) (b : list B) xa xb i,
  Forall2 P a b ->
  P xa xb ->
  Forall2 P (updN a i xa) (updN b i xb).
Proof.
  intros.
  apply forall_forall2.
  rewrite combine_updN.
  apply Forall_updN; auto.
  apply forall2_forall; auto.
  repeat rewrite length_updN.
  eapply forall2_length; eauto.
Qed.

Lemma selN_Forall2 : forall A B (a : list A) (b : list B) (P : A -> B -> Prop) da db,
  length a = length b ->
  (forall i, i < length a -> P (selN a i da) (selN b i db)) ->
  Forall2 P a b.
Proof.
  induction a; destruct b; intros; eauto.
  inversion H.
  inversion H.
  constructor.
  specialize (H0 0); simpl in *.
  apply H0; omega.
  eapply IHa.
  inversion H; auto.
  intros.
  specialize (H0 (S i)); simpl in *.
  apply H0.
  omega.
Qed.

Lemma forall2_map2_in: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2),
    (forall a b, In a l1 -> In b l2 -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y).
    eapply H; eauto.
    constructor; auto.
    constructor; auto.
    eapply IHForall2; intros.
    eapply H; eauto.
    eapply in_cons; eauto.
    eapply in_cons; eauto.
Qed.

Lemma forall2_map2_selN: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2) def1 def2,
    (forall a b n, n < Datatypes.length l1 -> selN l1 n def1 = a -> selN l2 n def2 = b -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y 0).
    eapply H; eauto.
    simpl; omega.
    eapply IHForall2; intros.
    eapply H; eauto.
    instantiate (1 := (S n)).
    simpl; omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
    rewrite selN_cons; eauto.
    replace (S n - 1) with n by omega; eauto.
    omega.
Qed.

Lemma Forall2_eq : forall T (l l' : list T),
  Forall2 eq l l' -> l = l'.
Proof.
  induction l; simpl; intros.
  inversion H; eauto.
  inversion H; subst.
  erewrite IHl; eauto.
Qed.

Lemma Forall2_to_map_eq : forall T U l l' (R : T -> T -> Prop) (f : T -> U),
  (forall a b, R a b -> f a = f b) ->
  Forall2 R l l' ->
  map f l = map f l'.
Proof.
  intros.
  apply Forall2_eq.
  eapply forall2_map2_in; eauto.
Qed.


Definition cuttail A n (l : list A) := firstn (length l - n) l.

Lemma cuttail_length : forall A (l : list A) n,
  length (cuttail n l) = length l - n.
Proof.
  unfold cuttail; intros.
  rewrite firstn_length.
  rewrite Nat.min_l; omega.
Qed.

Lemma cuttail_0 : forall A (l : list A),
  cuttail 0 l = l.
Proof.
  unfold cuttail; intros.
  rewrite firstn_oob by omega; auto.
Qed.

Lemma cuttail_oob : forall A (l : list A) n,
  n >= length l -> cuttail n l = nil.
Proof.
  unfold cuttail; intros.
  replace (length l - n) with 0 by omega.
  simpl; auto.
Qed.

Lemma last_selN : forall A (l : list A) def,
  last l def = selN l (length l - 1) def.
Proof.
  induction l; intuition; simpl.
  rewrite Nat.sub_0_r, IHl.
  case_eq (length l); intros.
  erewrite length_nil with (l := l); auto.
  destruct l.
  inversion H.
  replace (S n - 1) with n by omega; auto.
Qed.

Lemma last_cuttail_selN : forall A n (l : list A) def,
  n < length l ->
  last (cuttail n l) def = selN l (length l - n - 1) def.
Proof.
  unfold cuttail; intros.
  rewrite last_selN.
  rewrite selN_firstn.
  rewrite firstn_length_l by omega; auto.
  rewrite firstn_length_l by omega; omega.
Qed.

Lemma cuttail_cuttail : forall A (l : list A) m n,
  cuttail m (cuttail n l) = cuttail (n + m) l.
Proof.
  unfold cuttail; intros.
  rewrite firstn_firstn, firstn_length.
  f_equal.
  apply Nat.min_case_strong; intros.
  apply Nat.min_case_strong; intros; omega.
  rewrite Nat.min_l in H; omega.
Qed.

Lemma cuttail_tail : forall A (l : list A) a n,
  cuttail (S n) (l ++ [a]) = cuttail n l.
Proof.
  unfold cuttail; intros.
  rewrite app_length; simpl.
  replace (length l + 1 - S n) with (length l - n) by omega.
  rewrite firstn_app_l; auto; omega.
Qed.

Lemma selN_cuttail : forall A n (l : list A) idx def,
  idx < length (cuttail n l) ->
  selN (cuttail n l) idx def = selN l idx def.
Proof.
  induction n; simpl; intros.
  rewrite cuttail_0. auto.
  destruct l using rev_ind; simpl; auto.
  rewrite cuttail_tail in *.
  rewrite IHn by auto.
  rewrite selN_app; auto.
  rewrite cuttail_length in *; omega.
Qed.

Lemma cuttail_cons : forall A (a : A) l n,
  n <= length l ->
  cuttail n (a :: l) = a :: (cuttail n l).
Proof.
  unfold cuttail; simpl; intros.
  destruct n; simpl.
  rewrite Nat.sub_0_r; auto.
  rewrite <- firstn_cons.
  f_equal.
  omega.
Qed.

Lemma cuttail_app_one: forall T (l : list T) n i d,
  n < length l ->
  i = length l - S n ->
  cuttail (S n) l ++ [selN l i d] = cuttail n l.
Proof.
  unfold cuttail.
  intros; subst.
  destruct (length l) eqn:?. omega.
  rewrite Nat.sub_succ, Nat.sub_succ_l by omega.
  erewrite firstn_S_selN; auto.
  omega.
Qed.

Lemma cuttail_concat_hom: forall T (l : list (list T)) n k,
  (Forall (fun x => length x = k) l) ->
  cuttail (n * k) (concat l) = concat (cuttail n l).
Proof.
  unfold cuttail; intros.
  erewrite concat_hom_length by eauto.
  rewrite <- Nat.mul_sub_distr_r.
  rewrite concat_hom_firstn by eauto.
  reflexivity.
Qed.

Lemma incl_cons2 : forall T (a b : list T) (v : T), 
  incl a b
  -> incl (v :: a) (v :: b).
Proof.
  firstorder.
Qed.

Lemma incl_nil : forall T (l : list T), 
  incl nil l.
Proof.
  firstorder.
Qed.

Lemma incl_in_nil : forall T (l : list T),
  incl l nil -> l = nil.
Proof.
  destruct l; auto; intros.
  assert (In t nil).
  apply H; constructor; auto.
  inversion H0.
Qed.

Lemma incl_remove : forall T dec (a : T) (l : list T),
  incl (remove dec a l) l.
Proof.
  induction l; unfold incl; simpl; auto; intros.
  destruct (dec a a0); subst; eauto.
  inversion H; subst; eauto.
Qed.

Fixpoint upd_range {T} l start len (v : T) :=
  match len with
  | 0 => l
  | S len' => updN (upd_range l (S start) len' v) start v
  end.

Fixpoint upd_range_fast {T} vs start len (v : T) :=
  match vs with
  | nil => nil
  | v' :: vs' =>
    match start with
    | S start' => v' :: upd_range_fast vs' start' len v
    | O =>
      match len with
      | O => v' :: vs'
      | S len' => v :: upd_range_fast vs' O len' v
      end
    end
  end.

Lemma upd_range_0 : forall T l start (v : T),
  upd_range l start 0 v = l.
Proof.
  auto.
Qed.

Lemma upd_range_length : forall T l start len (v : T),
  length (upd_range l start len v) = length l.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros; auto.
  unfold upd_range in *. simpl.
  rewrite length_updN. auto.
Qed.

Lemma upd_range_selN : forall T l start len (v : T) n d,
  start <= n < start + len ->
  n < length l ->
  selN (upd_range l start len v) n d = v.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros. omega.
  simpl.
  destruct (Nat.eq_dec start n). subst. rewrite selN_updN_eq. auto.
  rewrite upd_range_length. auto.
  rewrite selN_updN_ne by auto.
  rewrite IHlen. auto. omega. auto.
Qed.

Definition upd_range' T l start len (v : T) :=
  firstn start l ++ repeat v len ++ skipn (start + len) l.

Lemma upd_range_eq_upd_range' : forall T (l : list T) start len v,
  start + len <= length l ->
  upd_range l start len v = upd_range' l start len v.
Proof.
  intros T l start len.
  generalize dependent l.
  generalize dependent start.
  induction len; intros. simpl.
  - unfold upd_range'. rewrite plus_0_r. simpl.
    rewrite firstn_skipn. auto.
  - simpl. rewrite IHlen by omega.
    unfold upd_range'. simpl repeat.
    erewrite firstn_S_selN by omega.
    repeat rewrite <- app_assoc.
    rewrite updN_app2. rewrite updN_app1.
    all : rewrite firstn_length_l by omega.
    rewrite plus_Snm_nSm.
    rewrite Nat.sub_diag. simpl. auto.
    all : simpl; omega.
  Unshelve.
  eauto.
Qed.

Theorem upd_range_fast_eq_upd_range' : forall T (l: list T) start len v,
    start + len <= length l ->
    upd_range_fast l start len v = upd_range' l start len v.
Proof.
  unfold upd_range'.
  induction l; simpl; intros.
  - assert (start = 0) by omega.
    assert (len = 0) by omega.
    subst; auto.
  - destruct start, len; simpl.
    unfold upd_range'; simpl; auto.
    erewrite IHl; eauto; try omega.
    erewrite IHl; eauto; try omega.
    erewrite IHl; eauto; try omega.
Qed.

Lemma upd_range_concat_hom_small : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Forall (fun l' => length l' = k) l ->
  start mod k + len <= k ->
  0 < k -> 0 < len ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) (start mod k) len v)).
Proof.
  intros. assert (k <> 0) by omega.
  match goal with [H : context [length (concat _)]|- _ ] =>
    pose proof H; erewrite concat_hom_length in H by eauto end.
  repeat rewrite upd_range_eq_upd_range'.
  unfold upd_range'.
  erewrite <- concat_hom_updN_first_skip; eauto.
  erewrite concat_hom_subselect_firstn; eauto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm. rewrite mult_comm. rewrite <- Nat.div_mod by auto.
  erewrite <- Nat.min_l with (n := _ * _) at 1. rewrite <- firstn_firstn.
  repeat rewrite app_assoc. rewrite firstn_skipn.
  repeat rewrite <- app_assoc. repeat f_equal.
  erewrite concat_hom_subselect_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite le_plus_minus_r by auto.
  erewrite <- concat_hom_skipn; eauto.
  rewrite <- skipn_firstn_comm.
  rewrite skipn_skipn. rewrite Nat.add_shuffle0.
  rewrite plus_comm with (m := _ * _). rewrite mult_comm. rewrite <- Nat.div_mod by auto.
  remember (k - start mod k - len) as e.
  replace k with (start mod k + len + e) at 3 6 by omega.
  repeat rewrite plus_assoc. rewrite <- Nat.div_mod by auto.
  rewrite skipn_firstn_comm.
  rewrite plus_comm with (m := e).
  repeat rewrite <- skipn_skipn.
  rewrite firstn_skipn. auto.
  all : try (apply Nat.div_lt_upper_bound; auto; rewrite mult_comm; omega).
  all : try apply Nat.mul_div_le; auto.
  - omega.
  - eapply le_trans; eauto. apply Nat.eq_le_incl.
    symmetry. apply Forall_selN; auto.
    apply Nat.div_lt_upper_bound; auto. rewrite mult_comm; omega.
Qed.

Lemma upd_range_concat_hom_start_aligned : forall T l start len (v : T) k d,
  start + len <= length (concat l) ->
  Nat.divide k start ->
  Forall (fun l' => length l' = k) l ->
  0 < len <= k -> 0 < k ->
  upd_range (concat l) start len v =
  concat (updN l (start / k) (upd_range (selN l (start / k) d) 0 len v)).
Proof.
  intros.
  rewrite <- Nat.mod_divide in * by omega.
  erewrite upd_range_concat_hom_small; eauto. repeat (f_equal; auto).
  all : omega.
Qed.

Lemma upd_range_nil : forall T start len (v : T),
  upd_range nil start len v = nil.
Proof.
  intros T start len.
  generalize start.
  induction len; intros; simpl; auto.
  rewrite IHlen. auto.
Qed.

Lemma upd_range_same : forall T start len n (v : T),
  upd_range (repeat v n) start len v = repeat v n.
Proof.
  intros.
  generalize dependent start. generalize dependent len.
  induction len; intros. auto.
  simpl. rewrite IHlen.
  destruct (lt_dec start n).
  erewrite selN_eq_updN_eq. auto.
  rewrite repeat_selN; auto.
  rewrite updN_oob. auto.
  rewrite repeat_length. omega.
  Unshelve. eauto.
Qed.

Hint Rewrite upd_range_0 upd_range_length upd_range_selN upd_range_nil upd_range_same : lists.

Lemma forall_upd_range : forall T l start len (v : T) f,
  Forall f l -> f v -> Forall f (upd_range l start len v).
Proof.
  intros.
  generalize dependent start. generalize dependent l.
  induction len; intros.
  rewrite upd_range_0. auto.
  simpl. apply Forall_updN; auto.
Qed.

Lemma firstn_upd_range : forall T l n n' len (v : T),
  n <= n' -> firstn n (upd_range l n' len v) = firstn n l.
Proof.
  intros.
  generalize dependent n. generalize dependent l.
  generalize dependent n'. induction len; intros.
  rewrite upd_range_0. auto.
  simpl. rewrite firstn_updN_oob by omega. auto.
Qed.

Lemma upd_range_updN_oob : forall T l start len (v v2 : T) i,
  i < start \/ i >= start + len ->
  upd_range (updN l i v2) start len v = updN (upd_range l start len v) i v2.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl; auto.
  rewrite updN_comm by omega.
  rewrite IHlen by omega. auto.
Qed.

Lemma upd_range_upd_range : forall T l start len1 len2 (v : T),
  upd_range (upd_range l start len1 v) (start + len1) len2 v = upd_range l start (len1 + len2) v.
Proof.
  intros T l start len1.
  generalize dependent l. generalize dependent start.
  induction len1; intros; simpl.
  rewrite plus_0_r. auto.
  rewrite upd_range_updN_oob by omega.
  rewrite <- plus_Snm_nSm. rewrite IHlen1. auto.
Qed.

Lemma upd_range_hd : forall T l start len x (v : T),
  upd_range (x :: l) (S start) len v = x :: upd_range l start len v.
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; simpl; intros. auto.
  rewrite IHlen. auto.
Qed.

Lemma upd_range_fast_len_0 : forall T vs start (v : T),
  upd_range_fast vs start 0 v = vs.
Proof.
  induction vs; cbn; intros; auto.
  destruct start; f_equal; auto.
Qed.

Theorem upd_range_fast_eq : forall T vs start len (v : T),
    upd_range_fast vs start len v = upd_range vs start len v.
Proof.
  induction vs; cbn; intros.
  rewrite upd_range_nil. auto.
  destruct start, len; cbn; auto.
  rewrite upd_range_hd.
  cbn; f_equal; auto.
  rewrite upd_range_fast_len_0. auto.
  rewrite upd_range_hd. cbn.
  f_equal.
  rewrite IHvs. reflexivity.
Qed.

Hint Rewrite upd_range_upd_range upd_range_hd : lists.

Lemma upd_range_app_l : forall T l1 l2 start len (v : T),
  start + len <= length l1 ->
  upd_range (l1 ++ l2) start len v = upd_range l1 start len v ++ l2.
Proof.
  intros T l1 l2 start len. generalize dependent start.
  generalize dependent l1. generalize dependent l2.
  induction len; intros; simpl; auto.
  rewrite IHlen by omega.
  rewrite updN_app1. auto.
  rewrite upd_range_length. omega.
Qed.

Lemma upd_range_app_r : forall T l1 l2 start len (v : T),
  length l1 <= start ->
  upd_range (l1 ++ l2) start len v = l1 ++ upd_range l2 (start - length l1) len v.
Proof.
  intros T l1 l2 start len. generalize dependent start.
  generalize dependent l1. generalize dependent l2.
  induction len; intros; simpl; auto.
  rewrite IHlen by omega.
  rewrite updN_app2 by omega. repeat f_equal. omega.
Qed.

Lemma upd_range_selN_oob : forall T (l : list T) start len v i d,
  i < start \/ i >= start + len ->
  selN (upd_range l start len v) i d = selN l i d.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl; auto.
  rewrite selN_updN_ne by omega. apply IHlen.
  omega.
Qed.

Lemma removeN_upd_range_l : forall T (l : list T) start len v,
  removeN (upd_range l (S start) len v) start = removeN (upd_range l start (S len) v) start.
Proof.
  destruct len; intros; simpl;
    rewrite removeN_updN; auto.
Qed.

Lemma removeN_updN_lt : forall T (l : list T) i i' v,
  i < i' ->
  removeN (updN l i v) i' = updN (removeN l i') i v.
Proof.
  intros T l i.
  generalize dependent l.
  induction i; intros.
  - destruct l; simpl in *. rewrite removeN_nil. auto.
    destruct i'; try omega. repeat rewrite removeN_head. auto.
  - destruct l; simpl in *. rewrite removeN_nil. auto.
    destruct i'; try omega. repeat rewrite removeN_head.
    simpl. f_equal. apply IHi. omega.
Qed.

Lemma removeN_upd_range_r : forall T (l : list T) start len v,
  removeN (upd_range l start len v) (start + len) = removeN (upd_range l start (S len) v) (start + len).
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; intros; simpl.
  - rewrite plus_0_r. rewrite removeN_updN. auto.
  - repeat rewrite removeN_updN_lt by omega. f_equal.
    rewrite <- plus_Snm_nSm. apply IHlen.
Qed.

Lemma upd_range_eq_app_firstn_repeat : forall T (l : list T) start len v,
  length l <= start + len ->
  upd_range l start len v = firstn start l ++ repeat v (length l - start).
Proof.
  intros T l start len. generalize dependent start.
  generalize dependent l.
  induction len; intros; simpl.
  + rewrite firstn_oob by omega. replace (_ - _) with 0 by omega.
    rewrite app_nil_r. auto.
  + rewrite IHlen by omega.
    destruct (le_lt_dec (length l) start).
    - repeat rewrite firstn_oob by omega.
      repeat replace (_ - _) with 0 by omega.
      rewrite app_nil_r. rewrite updN_oob; auto.
    - replace (S start) with (start + 1) by omega.
      rewrite firstn_sum_split.
      rewrite updN_app1, updN_app2.
      all : try rewrite app_length.
      all : repeat rewrite firstn_length_l.
      rewrite Nat.sub_diag.
      destruct (skipn start l) eqn:H'.
      apply f_equal with (f := @length _) in H'. simpl in *.
      all : try rewrite skipn_length in *; try omega.
      rewrite <- app_assoc. simpl.
      replace (length l - start) with (S (length l - (start + 1))) by omega.
      auto.
Qed.

Lemma upd_range_oob : forall T (l : list T) start len v,
  length l <= start ->
  upd_range l start len v = l.
Proof.
  intros T l start len.
  generalize dependent start. generalize dependent l.
  induction len; intros; simpl. auto.
  rewrite updN_oob. rewrite IHlen; auto.
  rewrite upd_range_length. auto.
Qed.

Lemma removeN_upd_range_mid : forall T (l : list T) start len v i i',
  start <= i < start + len ->
  start <= i' < start + len ->
  i <= i' < length l ->
  removeN (upd_range l start len v) i = removeN (upd_range l start len v) i'.
Proof.
  intros.
  destruct (le_lt_dec (length l) (start + len)).
  + rewrite upd_range_eq_app_firstn_repeat by auto.
    unfold removeN.
    repeat rewrite firstn_app_le by (rewrite firstn_length_l; omega).
    rewrite firstn_length_l by omega.
    repeat rewrite skipn_app_r_ge by (rewrite firstn_length_l; omega).
    repeat rewrite skipn_repeat.
    repeat rewrite firstn_repeat by omega.
    repeat rewrite <- app_assoc. repeat rewrite repeat_app.
    f_equal. f_equal. rewrite firstn_length_l by omega.
    repeat rewrite <- Nat.sub_add_distr.
    omega.
  + repeat rewrite upd_range_eq_upd_range' by omega.
    unfold upd_range', removeN.
    repeat (
      rewrite firstn_app_le; rewrite firstn_length;
      (let H := fresh in let H' := fresh in
        edestruct Min.min_spec as [ [H H']|[H H'] ];
        rewrite H' in *; clear H'); try omega;
      rewrite firstn_app_l by (rewrite repeat_length; omega)).
    repeat rewrite <- app_assoc. f_equal.
    rewrite skipn_app_r_ge by (rewrite firstn_length_l; omega).
    rewrite skipn_app_r_ge with (n := S _) by (rewrite firstn_length_l; omega).
    repeat rewrite firstn_length_l by omega.
    repeat rewrite firstn_repeat by omega.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite le_plus_minus with (m := b) (n := a) at 1 by omega;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; omega)
    end. symmetry.
    match goal with [|- context [skipn ?a (repeat _ ?b ++ _)] ] =>
      rewrite le_plus_minus with (m := b) (n := a) at 1 by omega;
      rewrite <- repeat_app, <- app_assoc;
      rewrite skipn_app_l, skipn_oob by (rewrite repeat_length; omega)
    end.
    repeat rewrite app_nil_l. repeat rewrite app_assoc.
    repeat rewrite repeat_app. do 2 f_equal.
    omega.
Qed.

Lemma concat_hom_upd_range : forall T l start len (v : T) k,
  Forall (fun x => length x = k) l ->
  concat (upd_range l start len (repeat v k)) = upd_range (concat l) (start * k) (len * k) v.
Proof.
  induction l; intros; simpl.
  repeat rewrite upd_range_nil. auto.
  apply Forall_inv in H as H'.
  apply Forall_cons2 in H as H''. subst.
  destruct len. auto.
  simpl. rewrite upd_range_hd.
  destruct start; simpl.
  -rewrite IHl by auto. simpl.
    rewrite <- upd_range_upd_range. simpl.
    rewrite upd_range_app_l by omega.
    rewrite upd_range_app_r.
    rewrite upd_range_eq_app_firstn_repeat with (len := length _) by omega.
    simpl. rewrite repeat_length. rewrite Nat.sub_0_r, Nat.sub_diag. auto.
    rewrite upd_range_length. omega.
  - rewrite upd_range_app_r. f_equal.
    rewrite minus_plus.
    rewrite <- IHl with (len := S len) by auto.
    auto.
    apply le_plus_l.
Qed.

Lemma upd_range_start_0 : forall T l len (v : T),
  len <= length l ->
  upd_range l 0 len v = repeat v len ++ skipn len l.
Proof.
  induction l; intros.
  rewrite upd_range_nil. rewrite skipn_nil. rewrite app_nil_r.
  replace len with 0 by (simpl in *; omega). auto.
  destruct len. auto. simpl in *.
  rewrite upd_range_hd. rewrite IHl by omega. auto.
Qed.

Lemma upd_range_all : forall T l len (v : T),
  length l <= len ->
  upd_range l 0 len v = repeat v (length l).
Proof.
  induction l; intros.
  simpl. rewrite upd_range_nil. auto.
  simpl in *. destruct len; try omega.
  simpl. rewrite upd_range_hd. rewrite IHl by omega. auto.
Qed.

Lemma upd_range_app : forall T l1 l2 start len (v : T),
  start <= length l1 < start + len ->
  start + len <= length (l1 ++ l2) ->
  upd_range (l1 ++ l2) start len v =
    upd_range l1 start len v ++ upd_range l2 0 (len - (length l1 - start)) v.
Proof.
  intros T l1 l2 start len.
  generalize dependent l1. generalize dependent l2.
  generalize dependent start.
  induction len; intros; auto.
  rewrite upd_range_eq_upd_range' by auto.
  unfold upd_range'.
  rewrite firstn_app_l by omega.
  rewrite upd_range_eq_app_firstn_repeat by omega.
  rewrite <- app_assoc. f_equal.
  rewrite app_length in *.
  destruct (le_dec (length l2) (S len - (length l1 - start))).
  rewrite upd_range_all by omega.
  rewrite skipn_oob by (rewrite app_length; omega).
  rewrite repeat_app. rewrite app_nil_r. f_equal. omega.
  rewrite upd_range_start_0 by omega.
  rewrite app_assoc. rewrite repeat_app.
  rewrite skipn_app_r_ge by omega. repeat (omega || f_equal).
Qed.

Lemma In_incl : forall A (x : A) (l1 l2 : list A),
  In x l1 -> incl l1 l2 -> In x l2.
Proof.
  firstorder.
Qed.


Definition postfix A (a b : list A) :=
  exists n, a = skipn n b.

Lemma postfix_nil : forall A (l : list A),
  postfix nil l.
Proof.
  unfold postfix; intros.
  exists (length l).
  rewrite skipn_oob; auto.
Qed.

Lemma postfix_refl : forall A (a : list A),
  postfix a a.
Proof.
  unfold postfix; intros.
  exists 0; auto.
Qed.

Lemma postfix_app : forall A (l a b: list A),
  postfix l b ->
  postfix l (a ++ b).
Proof.
  unfold postfix; intros.
  destruct H. eexists; subst.
  rewrite skipn_app_r; eauto.
Qed.

Lemma postfix_tl : forall A x (l a: list A),
  postfix l a ->
  postfix l (x :: a).
Proof.
  intros.
  rewrite cons_app.
  apply postfix_app; auto.
Qed.

Lemma postfix_singular : forall A (a : A) l,
  postfix l [ a ] -> l <> nil -> l = [ a ].
Proof.
  unfold postfix; intros.
  destruct H.
  destruct l; try congruence.
  destruct x; simpl in *; try congruence.
  rewrite skipn_nil in H; congruence.
Qed.

Theorem rev_injective :
  forall A (l1 l2 : list A), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive.
  reflexivity.
Qed.

Lemma rev_eq_iff : forall T (l l' : list T),
  l = rev l' <-> rev l = l'.
Proof.
  split; intros; apply f_equal with (f := @rev T) in H;
    rewrite rev_involutive in *; auto.
Qed.

Lemma NoDup_app_not_In : forall A (l : list A) (a : A),
  NoDup (l ++ [a]) -> ~ In a l.
Proof.
  induction l; simpl; auto; intros.
  inversion H; subst; auto.
  intro; intuition; subst.
  rewrite in_app_iff in H2; intuition.
  eapply IHl; eauto.
Qed.


Lemma NoDup_rev_1 : forall A (l : list A),
  NoDup l -> NoDup (rev l).
Proof.
  induction l using rev_ind; simpl; intros; auto.
  rewrite rev_app_distr; simpl.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev; auto.
Qed.

Lemma NoDup_rev_2 : forall A (l : list A),
  NoDup (rev l) -> NoDup l.
Proof.
  induction l; simpl; intros; auto.
  apply NoDup_app_l in H as H1.
  apply NoDup_app_not_In in H as H2.
  constructor; eauto.
  contradict H2.
  apply in_rev in H2; auto.
Qed.

Lemma NoDup_rev : forall A (l : list A),
  NoDup l <-> NoDup (rev l).
Proof.
  split.
  apply NoDup_rev_1.
  apply NoDup_rev_2.
Qed.

Lemma selN_rev: forall T n (l : list T) d,
  n < length l ->
  selN (rev l) n d = selN l (length l - S n) d.
Proof.
  induction l; cbn; auto.
  intros.
  destruct (lt_dec n (length l)).
  rewrite selN_app1 by (rewrite rev_length; auto).
  rewrite IHl by auto.
  destruct (length l - n) eqn:?; try omega.
  f_equal; omega.
  rewrite selN_app2 by (rewrite rev_length; omega).
  rewrite rev_length.
  repeat match goal with |- context [?a - ?b] =>
    destruct (a - b) eqn:?; try omega
  end.
  auto.
Qed.

Lemma firstn_rev: forall T (l : list T) n, firstn n (rev l) = rev (skipn (length l - n) l).
Proof.
  induction l using rev_ind; cbn; intros.
  auto using firstn_nil.
  rewrite rev_app_distr; cbn.
  rewrite app_length; cbn.
  rewrite plus_comm.
  rewrite skipn_app_split.
  rewrite rev_app_distr.
  rewrite <- Nat.sub_add_distr.
  rewrite plus_comm with (n := n).
  rewrite Nat.sub_add_distr.
  rewrite Nat.add_sub.
  destruct n.
  repeat rewrite skipn_oob by (cbn; omega).
  auto.
  cbn.
  congruence.
Qed.

Lemma combine_rev: forall A B (a : list A) (b : list B),
  length a = length b ->
  rev (combine a b) = combine (rev a) (rev b).
Proof.
  induction a; destruct b; cbn; intros; auto.
  congruence.
  rewrite combine_app; cbn.
  f_equal; auto.
  repeat rewrite rev_length; auto.
Qed.

Lemma list_isolate: forall T (l : list T) m n d,
  length l = m + 1 + n ->
  l = firstn m l ++ [selN l m d] ++ rev (firstn n (rev l)).
Proof.
  intros.
  erewrite <- firstn_skipn at 1.
  f_equal.
  cbn.
  erewrite skipn_selN_skipn.
  f_equal.
  rewrite firstn_rev by auto.
  rewrite rev_involutive.
  f_equal; omega.
  omega.
Qed.

Lemma filter_length : forall A f (l : list A),
  length (filter f l) <= length l.
Proof.
  induction l; simpl; auto.
  destruct (f a); simpl; auto; omega.
Qed.

Definition disjoint A (a b : list A) :=
  forall x, (In x a -> ~ In x b) /\ (In x b -> ~ In x a).

Lemma disjoint_sym : forall A (a b : list A),
  disjoint a b -> disjoint b a.
Proof.
  unfold disjoint; firstorder.
Qed.

Lemma disjoint_nil_l : forall A (a : list A),
  disjoint nil a.
Proof.
  unfold disjoint; firstorder.
Qed.

Lemma disjoint_cons_l : forall A (a b : list A) x,
  disjoint a b ->
  ~ In x b ->
  disjoint (x :: a) b.
Proof.
  unfold disjoint; firstorder; subst.
  specialize (H x0); intuition.
  pose proof (H x); pose proof (H x0); intuition.
  firstorder; subst; intuition.
Qed.

Definition enumerate A (l : list A) := combine (seq 0 (length l)) l.

Theorem selN_enumerate : forall A (l : list A) d i,
  i < length l -> selN (enumerate l) i d = (i, selN l i (snd d)).
Proof.
  intros.
  unfold enumerate.
  destruct d.
  rewrite selN_combine.
  rewrite nth_selN_eq, seq_nth; auto.
  apply seq_length.
Qed.

Fact length_enumerate : forall T (l : list T), length (enumerate l) = length l.
Proof.
  unfold enumerate; intros.
  rewrite combine_length_eq; rewrite seq_length; auto.
Qed.

Lemma firstn_seq : forall n a b, firstn n (seq a b) = seq a (min n b).
Proof.
  induction n; intros; auto; simpl.
  destruct b; auto; simpl; f_equal; auto.
Qed.

Lemma firstn_enumerate : forall A (l : list A) n, firstn n (enumerate l) = enumerate (firstn n l).
Proof.
  unfold enumerate; intros.
  rewrite firstn_combine_comm; f_equal.
  rewrite firstn_seq; f_equal.
  rewrite firstn_length; auto.
Qed.

Lemma enumerate_inj : forall A (l1 l2 : list A), enumerate l1 = enumerate l2 <-> l1 = l2.
Proof.
  unfold enumerate.
  split; intros; subst; auto.
  generalize dependent H.
  generalize 0.
  generalize dependent l2.
  induction l1; simpl in *; intros;
  destruct l2; try inversion H; auto.
  f_equal; eauto.
Qed.

Hint Rewrite length_enumerate firstn_enumerate selN_enumerate enumerate_inj : lists.

Definition part {T} (l : list T) (k : nat) :=
  map (fun i => firstn k (skipn (i * k) l)) (seq 0 (length l / k)).

Definition part_nil : forall T k, part (@nil T) k = nil.
Proof.
  unfold part. intros.
  destruct (Nat.eq_dec 0 k); subst.
  auto.
  rewrite Nat.div_0_l by auto. auto.
Qed.

Lemma part_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  length (part l k) = length l / k.
Proof.
  intros.
  unfold Nat.divide in *. destruct H.
  unfold part.
  rewrite H, Nat.div_mul by auto.
  rewrite map_length, seq_length; auto.
Qed.

Lemma part_forall_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  Forall (fun x => length x = k) (part l k).
Proof.
  intros.
  destruct H. unfold part; rewrite H.
  rewrite Nat.div_mul by auto.
  apply Forall_map, Forall_forall.
  intros x0 HH.
  apply in_seq in HH.
  apply firstn_length_l.
  rewrite skipn_length, H.
  rewrite <- Nat.mul_sub_distr_r, mult_comm.
  rewrite <- mult_1_r at 1.
  apply mult_le_compat_l. omega.
Qed.

Lemma concat_hom_part : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
  concat (part l k) = l.
Proof.
  intros.
  unfold part.
  destruct H.
  remember (length l) as n.
  generalize dependent n.
  generalize dependent l.
  generalize dependent k.
  induction x; intros.
  simpl in *; rewrite H in *.
  rewrite Nat.div_0_l by auto.
  simpl.
  symmetry; apply length_nil. auto.
  rewrite H; simpl.
  rewrite Nat.div_add, Nat.div_same by auto.
  simpl in *.
  rewrite <- seq_shift, map_map.
  simpl in *.
  rewrite <- firstn_skipn with (l := l) at 2.
  f_equal.
  rewrite <- IHx with (k := k) (n := x * k); auto.
  rewrite Nat.div_mul by auto.
  f_equal. apply map_ext.
  intros.
  f_equal.
  rewrite skipn_skipn'; auto.
  rewrite skipn_length.
  assert (x * k >= 0) by intuition.
  omega.
Qed.

Lemma part_hom_concat : forall T (l : list (list T)) k, Forall (fun x => length x = k) l -> k <> 0 ->
  part (concat l) k = l.
Proof.
  unfold part.
  intros.
  erewrite concat_hom_length; eauto.
  rewrite Nat.div_mul by auto.
  induction l; simpl; intros. auto.
  inversion H; subst.
  f_equal. rewrite firstn_app2; auto.
  rewrite <- seq_shift, map_map.
  simpl in *.
  rewrite <- IHl at 2 by auto.
  apply map_ext.
  intros.
  f_equal.
  rewrite skipn_app_r. auto.
Qed.

Section ifind_list.
  Variable T : Type.
  (* finding an element inside a block *)
  Fixpoint ifind_list (cond : T -> nat -> bool) (vs : list T) start : option (nat * T ) :=
    match vs with
    | nil => None
    | x :: rest =>
        if (cond x start) then Some (start, x)
                          else ifind_list cond rest (S start)
    end.

  Lemma ifind_list_ok_mono : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    fst r >= start.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct cond.
    inversion H; simpl; auto.
    apply le_Sn_le.
    apply IHvs; auto.
  Qed.

  Lemma ifind_list_ok_bound : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    fst r < start + length vs.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; omega.
    replace (start + S (length vs)) with (S start + length vs) by omega.
    apply IHvs; auto.
  Qed.

  Lemma ifind_list_ok_cond : forall cond vs start r,
    ifind_list cond vs start = Some r ->
    cond (snd r) (fst r) = true.
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct (cond a) eqn: C.
    inversion H; simpl; auto.
    eapply IHvs; eauto.
  Qed.

  Lemma ifind_list_ok_item : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    selN vs ((fst r) - start) d = (snd r).
  Proof.
    induction vs; simpl; intros; try congruence.
    destruct cond.
    inversion H; simpl; auto.
    rewrite Nat.sub_diag; simpl; auto.
    replace (fst r - start) with (S (fst r - S start)).
    apply IHvs; auto.
    apply ifind_list_ok_mono in H; omega.
  Qed.

  Lemma ifind_list_ok_facts : forall cond vs start r d,
    ifind_list cond vs start = Some r ->
    (fst r) >= start /\
    (fst r) < start + length vs /\
    cond (snd r) (fst r) = true /\
    selN vs ((fst r) - start) d = (snd r).
  Proof.
    intros; intuition eauto using
      ifind_list_ok_mono,
      ifind_list_ok_bound,
      ifind_list_ok_cond,
      ifind_list_ok_item.
  Qed.

  Lemma ifind_list_none : forall cond l start d,
    ifind_list cond l start = None ->
    forall ix, ix < length l ->
    cond (selN l ix d) (start + ix) = false.
  Proof.
    induction l; simpl; intros; try omega.
    destruct ix.
    rewrite Nat.add_0_r.
    destruct cond; congruence.
    rewrite <- plus_Snm_nSm.
    apply IHl; try omega.
    destruct (cond a); congruence.
  Qed.
End ifind_list.

Inductive list_same {T : Type} (v : T) : list T -> Prop :=
| ListSameNil : list_same v nil
| ListSameCons : forall l, list_same v l -> list_same v (v :: l).

Lemma list_same_app_l : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v a.
Proof.
  induction a; simpl; intros.
  constructor.
  inversion H; subst.
  constructor.
  eauto.
Qed.

Lemma list_same_app_r : forall T v (a b : list T),
  list_same v (a ++ b) -> list_same v b.
Proof.
  induction a; simpl; intros; eauto.
  inversion H; subst; eauto.
Qed.

Lemma list_same_app_both : forall T v (a b : list T),
  list_same v a -> list_same v b -> list_same v (a ++ b).
Proof.
  induction a; simpl; intros; eauto.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma list_same_repeat : forall T (v : T) n,
  list_same v (repeat v n).
Proof.
  induction n; simpl; intros; constructor; eauto.
Qed.

Lemma list_same_firstn : forall T (v : T) n l,
  list_same v l -> list_same v (firstn n l).
Proof.
  induction n; simpl; intros; try constructor.
  destruct l; try constructor.
  inversion H; subst.
  constructor; eauto.
Qed.

Lemma list_same_skipn : forall T (v : T) n l,
  list_same v l -> list_same v (skipn n l).
Proof.
  induction n; simpl; intros; eauto.
  destruct l; try constructor.
  inversion H; subst; eauto.
Qed.

Lemma list_same_firstn_le : forall T (v : T) n2 n1 l,
  n2 <= n1 -> list_same v (firstn n1 l) -> list_same v (firstn n2 l).
Proof.
  induction n2; simpl; intros.
  constructor.
  destruct n1; try omega.
  destruct l; try constructor.
  simpl in *.
  inversion H0; subst.
  constructor.
  eapply IHn2.
  2: eauto.
  omega.
Qed.

Lemma list_same_skipn_ge : forall T (v : T) n1 n2 l,
  n2 >= n1 -> list_same v (skipn n1 l) -> list_same v (skipn n2 l).
Proof.
  induction n1; simpl; intros.
  eapply list_same_skipn; eauto.
  destruct n2; try omega; simpl.
  destruct l; simpl in *.
  constructor.
  eapply IHn1; eauto.
  omega.
Qed.

Lemma list_same_skipn_upd_range_tail : forall T (v : T) l off,
  list_same v (skipn off (upd_range l off (length l - off) v)).
Proof.
  intros.
  destruct (le_dec off (length l)).
  - rewrite upd_range_eq_upd_range' by omega; unfold upd_range'.
    rewrite skipn_app_r_ge by ( rewrite firstn_length, min_l; omega ).
    rewrite firstn_length, min_l by omega.
    replace (off - off) with 0 by omega.
    simpl.
    apply list_same_app_both.
    apply list_same_repeat.
    replace (off + (length l - off)) with (length l) by omega.
    rewrite skipn_oob by omega.
    constructor.
  - rewrite not_le_minus_0 by auto. rewrite upd_range_0.
    rewrite skipn_oob by omega. constructor.
Qed.

Lemma list_same_skipn_upd_range_mid : forall T (v : T) l off count,
  list_same v (skipn (off + count) l) ->
  off + count <= length l ->
  list_same v (skipn off (upd_range l off count v)).
Proof.
  intros.
  rewrite upd_range_eq_upd_range' by omega; unfold upd_range'.
  rewrite skipn_app_r_ge by ( rewrite firstn_length, min_l; omega ).
  rewrite firstn_length, min_l by omega.
  replace (off - off) with 0 by omega.
  simpl.
  apply list_same_app_both.
  apply list_same_repeat.
  auto.
Qed.

Lemma list_same_skipn_selN : forall T (v : T) off l def,
  off < length l -> list_same v (skipn off l) -> v = selN l off def.
Proof.
  induction off; simpl; intros.
  destruct l; simpl in *; try omega.
  inversion H0; auto.
  destruct l; simpl in *; try omega.
  eapply IHoff; eauto.
  omega.
Qed.

Lemma updN_concat' : forall T (l : list (list T)) l' off k x ld,
  k <> 0 ->
  off < k * length l ->
  Forall (fun y => length y = k) l ->
  l' = updN (selN l (off / k) ld) (off mod k) x ->
  updN (concat l) off x = concat (updN l (off / k) l').
Proof.
  intros.
  subst.
  erewrite Nat.div_mod with (x := off) at 1 by eauto.
  rewrite plus_comm, mult_comm.
  erewrite updN_concat; auto.
  erewrite selN_inb; eauto.
  apply Nat.div_lt_upper_bound; auto.
  apply Nat.mod_bound_pos; omega.
Qed.


Lemma not_in_app: forall (A : Type) (x: A) l1 l2,
  ~In x (l1++l2) -> (~In x l1) /\ (~In x l2).
Proof.
  split; auto using in_or_app.
Qed.


Hint Resolve incl_app incl_appl incl_appr incl_refl : incl_app.

Lemma incl_app2r : forall T (l1 l2 l2' : list T),
  incl l2 l2' ->
  incl (l1 ++ l2) (l1 ++ l2').
Proof.
  eauto with incl_app.
Qed.

Lemma incl_app2l : forall T (l1' l1 l2 : list T),
  incl l1 l1' ->
  incl (l1 ++ l2) (l1' ++ l2).
Proof.
  eauto with incl_app.
Qed.

Lemma incl_app_commr: forall (A: Type) (l: list A) l1 l2,
  incl l (l1++l2) -> incl l (l2++l1).
Proof.
  unfold incl; intros.
  eapply in_or_app.
  specialize (H _ H0).
  eapply in_app_or in H.
  intuition.
Qed.

Lemma incl_app_comml: forall (A: Type) (l: list A) l1 l2,
  incl (l1++l2) l -> incl (l2++l1) l.
Proof.
  unfold incl; intros.
  apply H.
  eapply in_or_app.
  eapply in_app_or in H0.
  intuition.
Qed.

Lemma incl_appl' : forall (A : Type) (l m n : list A),
  incl (l ++ m) n -> incl l n.
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.

Lemma incl_appr' : forall (A : Type) (l m n : list A),
  incl (l ++ m) n -> incl m n.
Proof.
  unfold incl; intros.
  eapply H.
  eapply in_or_app.
  eauto.
Qed.

Lemma NoDup_incl_l : forall T (l1 l2 l2' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l2' ->
  incl l2' l2 ->
  NoDup (l1 ++ l2').
Proof.
  induction l1; intros; eauto.
  simpl.
  inversion H; subst.
  constructor; eauto.
  contradict H4.
  eapply In_incl; eauto.
  eapply incl_app2r; eauto.
Qed.

Lemma NoDup_remove_inverse : forall T a (l' l : list T),
  NoDup (l ++ l') -> ~ In a (l ++ l') -> NoDup (l ++ a :: l').
Proof.
  induction l; simpl; intros; eauto.
  constructor; eauto.
  inversion H; subst.
  constructor.
  - apply not_in_app in H3; destruct H3.
    intro H'.
    apply in_app_or in H'; destruct H'.
    eauto.
    rewrite cons_app in H3. apply in_app_or in H3. destruct H3.
    simpl in *; intuition eauto.
    eauto.
  - eapply IHl; eauto.
Qed.

Lemma NoDup_incl_r : forall T (l2 l1 l1' : list T),
  NoDup (l1 ++ l2) ->
  NoDup l1' ->
  incl l1' l1 ->
  NoDup (l1' ++ l2).
Proof.
  induction l2; intros; eauto.
  rewrite app_nil_r; eauto.

  eapply List.NoDup_remove in H; intuition.
  specialize (IHl2 _ _ H2 H0 H1).

  eapply NoDup_remove_inverse; eauto.
  contradict H3.
  eapply In_incl.
  eauto.
  eapply incl_app2l; eauto.
Qed.

Lemma incl_cons2_inv : forall T (l1 l2 : list T) a,
  ~ In a l1 ->
  incl (a :: l1) (a :: l2) ->
  incl l1 l2.
Proof.
  induction l1; simpl; intros.
  apply incl_nil.
  apply incl_cons.
  edestruct (H0 a).
  intuition.
  intuition congruence.
  eauto.
  eapply IHl1 with (a := a0).
  intuition.
  intro; intro. apply H0.
  inversion H1; subst; simpl; eauto.
Qed.

Lemma incl_cons_inv : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> incl l1 l2.
Proof.
  unfold incl; intros.
  apply H; intuition.
Qed.

Lemma incl_cons_inv' : forall T (a : T) l1 l2,
  incl (a :: l1) l2 -> In a l2 /\ incl l1 l2.
Proof.
  unfold incl; intros.
  intuition.
Qed.

Lemma incl_tl_inv : forall T l1 l2 (a : T),
  incl l1 (a :: l2) ->
  ~ In a l1 ->
  incl l1 l2.
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - intuition.
    apply incl_cons.
    + specialize (H a).
      simpl in *. intuition.
    + eapply IHl1; eauto.
      eapply incl_cons_inv; eauto.
Qed.


Definition incl_count T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x <= count_occ E l2 x.

Definition permutation T (E : forall (a b : T), {a=b}+{a<>b}) (l1 l2 : list T) :=
  forall x, count_occ E l1 x = count_occ E l2 x.

Lemma count_occ_app : forall T E (l1 l2 : list T) x,
  count_occ E (l1 ++ l2) x = count_occ E l1 x + count_occ E l2 x.
Proof.
  induction l1; simpl; intros; eauto.
  repeat rewrite IHl1.
  destruct (E a x); omega.
Qed.

Lemma count_occ_remove_ne : forall T E (l : list T) a b,
  a <> b ->
  count_occ E (remove E a l) b = count_occ E l b.
Proof.
  induction l; simpl; intros; eauto.
  destruct (E a0 a); destruct (E a b); subst; try congruence; simpl.
  rewrite IHl by eauto; omega.
  destruct (E b b); try congruence.
  rewrite IHl by eauto; omega.
  destruct (E a b); try congruence.
  rewrite IHl by eauto; omega.
Qed.


Lemma incl_count_In: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1: list T) n l2,
  incl_count E (n ::l2) l1 ->
  In n l1.
Proof.
  intros.
  unfold incl_count in *.
  eapply count_occ_In with (eq_dec := E).
  specialize (H n).
  assert (count_occ E (n :: l2) n  >= 1).
  erewrite count_occ_cons_eq with (l := l2); eauto.
  omega.
  omega.
Qed.

Lemma incl_count_not_In: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
    count_occ E l x <= 0 ->
    ~In x l.
Proof.
  induction l; intros.
  - intro.
    apply H0.
  - apply not_in_cons.
    intuition.
    subst.
    rewrite count_occ_cons_eq in H. omega. auto.
    eapply IHl; eauto.
    destruct (E x a); subst.
    + rewrite count_occ_cons_eq in H. omega. auto.
    + exfalso.
      eapply IHl with (x := x); eauto.
      rewrite count_occ_cons_neq in H; eauto.
Qed.


Lemma count_occ_NoDup: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T),
  NoDup l <->
  forall x, count_occ E l x <= 1.
Proof.
  split.
  + induction l; intros.
    - unfold count_occ.
      omega.
    - destruct (E x a).
      ++ rewrite count_occ_cons_eq; auto.
        subst.
        inversion H; subst.
        assert (count_occ E l a = 0).
        erewrite <- count_occ_not_In; eauto.
        rewrite H0. omega.
      ++ rewrite count_occ_cons_neq; eauto.
        inversion H; subst.
        apply IHl; eauto.
  + induction l.
    - constructor.
    - constructor.
      specialize (H a).
      rewrite count_occ_cons_eq in H; auto.
      eapply incl_count_not_In with (E:=E); eauto.
      omega.
      apply IHl.
      intro.
      destruct (E x a); subst.
      ++
        specialize (H a). 
        rewrite count_occ_cons_eq in H; auto.
        omega.
      ++
        specialize (H x). 
        rewrite count_occ_cons_neq in H; auto.
 Qed.

Lemma count_occ_NoDup_dec: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l : list T) x,
  NoDup l -> count_occ E l x = 0 \/ count_occ E l x = 1.
Proof.
  intros.
  destruct (In_dec E x l).
  + right.
    eapply count_occ_NoDup with (E:= E) (x := x) in H.
    assert (count_occ E l x > 0).
    apply count_occ_In; eauto.
    omega.
  + left.
    apply count_occ_not_In; auto.
Qed.

Lemma occ_count_NoDup_impl_NoDup: forall (T: Type) (E : forall a b : T, {a = b} + {a <> b}) (l1 l2 : list T),
  incl_count E l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  intros.
  eapply count_occ_NoDup with (E:= E); eauto.
  intro.
  eapply count_occ_NoDup with (E:= E) (x := x) in H0 as H0'; eauto.
  unfold incl_count in H.
  specialize (H x).
  rewrite H0' in H; eauto.
Qed.


Lemma incl_count_incl : forall T E (l1 l2 : list T),
  incl_count E l1 l2 ->
  incl l1 l2.
Proof.
  unfold incl_count, incl; intros.
  specialize (H a).
  rewrite count_occ_In with (eq_dec := E) in *.
  omega.
Qed.

Lemma permutation_incl_count : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  incl_count E l1 l2.
Proof.
  unfold incl_count, permutation; intros.
  specialize (H x).
  omega.
Qed.

Lemma incl_count_tl : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E l1 (x :: l2).
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.

Lemma incl_count_cons : forall T E (l1 l2 : list T) x,
  incl_count E l1 l2 ->
  incl_count E (x :: l1) (x :: l2).
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.

Lemma incl_count_cons': forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) n,
  incl_count E (n::l1) (n::l2) ->
  incl_count E l1 l2.
Proof.
  unfold incl_count in *; intros.
  specialize (H x).
  rewrite cons_app in H.
  rewrite cons_app with (l := l2) in H.
  repeat rewrite count_occ_app in H.
  omega.
Qed.

Module Type HIDDEN_APP.
  Parameter app : forall {T : Type} (l1 l2 : list T), list T.
  Axiom app_is : @app = List.app.
End HIDDEN_APP.

Module Hidden_App : HIDDEN_APP.
  Definition app := List.app.
  Theorem app_is : @app = List.app.
    reflexivity.
  Qed.
End Hidden_App.

Lemma incl_count_rotate_start : forall T E (l1 l2 : list T),
  incl_count E l1 (Hidden_App.app l2 nil) ->
  incl_count E l1 l2.
Proof.
  intros.
  rewrite Hidden_App.app_is in *.
  rewrite app_nil_r in *.
  intros; eauto.
Qed.

Lemma incl_count_rotate_one : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (Hidden_App.app l2 (l2' ++ [x])) ->
  incl_count E l1 (Hidden_App.app (x :: l2) l2').
Proof.
  rewrite Hidden_App.app_is.
  unfold incl_count; intros.
  specialize (H x0).
  repeat rewrite count_occ_app in *; simpl in *.
  destruct (E x x0); omega.
Qed.

Lemma incl_count_rotate_cons : forall T E (l1 l2 l2' : list T) x,
  incl_count E l1 (l2 ++ l2') ->
  incl_count E (x :: l1) (Hidden_App.app (x :: l2) l2').
Proof.
  rewrite Hidden_App.app_is.
  unfold incl_count; intros.
  specialize (H x0).
  simpl.
  destruct (E x x0); omega.
Qed.

Lemma incl_count_nil : forall T E (l : list T),
  incl_count E [] l.
Proof.
  unfold incl_count; simpl; intros; omega.
Qed.

Lemma incl_count_trans : forall T E (l1 l2 l3 : list T),
  incl_count E l1 l2 ->
  incl_count E l2 l3 ->
  incl_count E l1 l3.
Proof.
  unfold incl_count; intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.

Lemma incl_count_refl : forall T E (l : list T),
  incl_count E l l.
Proof.
  unfold incl_count; intros.
  omega.
Qed.

Lemma count_occ_remove_eq: forall T E (l : list T) x,
  count_occ E (remove E x l) x = 0.
Proof.
  induction l; cbn; auto; intros.
  repeat (destruct E; subst; cbn; auto).
  congruence.
Qed.

Lemma count_occ_remove_NoDup_eq: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l: list T) n,
  NoDup l ->
  count_occ E (remove E n l) n <= 0.
Proof.
  induction l; intros; subst.
  + simpl in *. auto.
  + destruct (E n  a); subst.
    - rewrite remove_cons_eq; auto.
      eapply count_occ_NoDup with (E := E) (x := a) in H as H'.
      rewrite cons_app in H'.
      rewrite count_occ_app in H'; auto.
      simpl in H'.
      destruct (E a a); subst; try congruence.
      omega.
    - rewrite remove_cons_neq; auto.
      rewrite cons_app.
      rewrite count_occ_app.
      simpl.
      destruct (E a n); subst; try congruence.
      eapply IHl.
      inversion H; auto.
Qed.

Lemma incl_count_remove_NoDup: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1: list T) n l2,
  NoDup l1 -> 
  NoDup (n :: l2) ->
  incl_count E (n::l2) l1 ->
  incl_count E l2 (remove E n l1).
Proof. 
  unfold incl_count in *; intros.
  eapply count_occ_NoDup with (E := E) (x := x) in H as H'.    
  eapply count_occ_NoDup with (E := E) (x := x) in H0 as H0'.    
  rewrite cons_app in H0'.
  rewrite count_occ_app in H0'.
  destruct (E n x); subst.
  - simpl in *.
    destruct (E x x); subst; try congruence.
    assert ( count_occ E (remove E x l1) x <= 0).
    eapply count_occ_remove_NoDup_eq; auto.
    omega.
  - simpl in H0'.
    destruct (E n x); subst; try congruence.
    rewrite count_occ_remove_ne; auto.
    specialize (H1 x).
    rewrite cons_app in H1.
    rewrite count_occ_app in H1.
    simpl in H1.
    destruct (E n x); subst; try congruence.  
    omega.
Qed.


Lemma incl_count_add: forall (T: Type) 
    (E : forall a b : T, {a = b} + {a <> b}) (l1 l2: list T) x,
  incl_count E l1 l2 ->
  incl_count E (x::l1) (x::l2).
Proof.
  unfold incl_count; intros.
  specialize (H x0).
  rewrite cons_app.
  rewrite cons_app with (l := l2).
  repeat rewrite count_occ_app.
  omega.
Qed.


Lemma permutation_trans : forall T E (l1 l2 l3 : list T),
  permutation E l1 l2 ->
  permutation E l2 l3 ->
  permutation E l1 l3.
Proof.
  unfold permutation; intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.

Lemma permutation_refl : forall T E (l : list T),
  permutation E l l.
Proof.
  firstorder.
Qed.

Lemma permutation_comm : forall T E (l1 l2 : list T),
  permutation E l1 l2 ->
  permutation E l2 l1.
Proof.
  firstorder.
Qed.

Lemma permutation_cons: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (x :: l) (x :: l').
Proof.
  unfold permutation. cbn; intros.
  destruct E; congruence.
Qed.

Lemma incl_count_app_comm : forall T E (l1 l2 : list T),
  incl_count E (l1 ++ l2) (l2 ++ l1).
Proof.
  unfold incl_count; intros.
  repeat rewrite count_occ_app.
  omega.
Qed.

Lemma permutation_app_comm : forall T E (l1 l2 : list T),
  permutation E (l1 ++ l2) (l2 ++ l1).
Proof.
  unfold permutation; intros.
  repeat rewrite count_occ_app.
  omega.
Qed.

Lemma permutation_app_split : forall T E (l1 l1' l2 l2' : list T),
  permutation E l1 l1' ->
  permutation E l2 l2' ->
  permutation E (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold permutation; intros.
  repeat rewrite count_occ_app.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.

Lemma permutation_remove: forall T E (l l' : list T) x,
  permutation E l l' ->
  permutation E (remove E x l) (remove E x l').
Proof.
  unfold permutation.
  intros.
  destruct (E x x0); subst.
  repeat rewrite count_occ_remove_eq; auto.
  repeat rewrite count_occ_remove_ne by auto.
  eauto.
Qed.

Lemma permutation_in: forall T E (l l' : list T) x,
  permutation E l l' -> In x l -> In x l'.
Proof.
  unfold permutation.
  intros.
  rewrite count_occ_In in *.
  rewrite <- H. eauto.
Qed.

Lemma incl_count_app_split : forall T E (l1 l1' l2 l2' : list T),
  incl_count E l1 l1' ->
  incl_count E l2 l2' ->
  incl_count E (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold incl_count; intros.
  repeat rewrite count_occ_app.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.

Hint Resolve incl_count_trans incl_count_refl incl_count_app_comm incl_count_app_split : incl_count_app.
Hint Resolve permutation_trans permutation_refl permutation_app_comm permutation_app_split : permutation_app.

Definition NoDupApp (T : Type) (l : list (list T)) := NoDup (concat l).

Lemma NoDupApp_pick : forall T (l1 l2 l3 : list (list T)),
  NoDupApp (l1 ++ l2 ++ l3) -> NoDupApp (l2 ++ l1 ++ l3).
Proof.
  unfold NoDupApp; intros; repeat rewrite concat_app in *.
  rewrite app_assoc. apply NoDup_app_comm.
  apply NoDup_3app_rev.
  eauto.
Qed.

Lemma NoDupApp_cons_nil : forall T (l : list (list T)),
  NoDupApp ([] :: l) <-> NoDupApp l.
Proof.
  firstorder.
Qed.

Lemma NoDupApp_cons : forall T a (l : list (list T)),
  NoDupApp l ->
  NoDup a ->
  (forall x, In x a -> ~ In x (concat l)) ->
  NoDupApp (a :: l).
Proof.
  induction a; simpl; intros.
  apply NoDupApp_cons_nil; eauto.
  constructor.
  - intro H'.
    apply in_app_or in H'; intuition.
    + inversion H0; eauto.
    + eapply H1; eauto.
  - apply IHa; eauto.
    inversion H0; eauto.
Qed.

Lemma NoDupApp_In : forall T a (l : list (list T)),
  NoDupApp l ->
  In a l ->
  NoDup a.
Proof.
  induction l; simpl; intros.
  firstorder.
  intuition subst.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_l; eauto.
  eapply IHl; eauto.
  unfold NoDupApp in H; simpl in H.
  eapply NoDup_app_r; eauto.
Qed.

Lemma incl_pick_inv : forall T (l1 l2 l : list T) x,
  NoDup (x :: l1 ++ l2) ->
  incl (l1 ++ x :: l2) (x :: l) ->
  incl (l1 ++ l2) l.
Proof.
  intros.
  unfold incl; intros.
  specialize (H0 a).
  edestruct H0; subst; eauto.

  eapply in_app_or in H1.
  eapply in_or_app.
  intuition.

  exfalso. inversion H. eauto.
Qed.

Lemma incl_pick_inv' : forall T (E : forall a b, {a=b}+{a<>b}) (l1 l2 l : list T) x,
  incl_count E (x :: l) (l1 ++ x :: l2) ->
  incl_count E l (l1 ++ l2).
Proof.
  intros.
  unfold incl_count in *; intros.
  specialize (H x0).
  rewrite count_occ_app in *.
  simpl in *.
  destruct (E x x0); omega.
Qed.

Lemma incl_concat' : forall T (x : list T) l,
  In x l ->
  incl x (concat l).
Proof.
  destruct x; simpl; intros.
  apply incl_nil.

  induction l; simpl; intros.
  - exfalso; simpl in *; eauto.
  - inversion H; subst.
    apply incl_appl. apply incl_refl.
    apply incl_appr. eauto.
Qed.

Lemma incl_concat : forall T (l1 l2 : list (list T)),
  incl l1 l2 ->
  incl (concat l1) (concat l2).
Proof.
  induction l1; simpl; intros.
  - apply incl_nil.
  - apply incl_cons_inv' in H; intuition.
    eapply incl_app; eauto.
    eapply incl_concat'; eauto.
Qed.

Theorem NoDupApp_incl : forall T (E : forall (a b : T), {a=b}+{a<>b}) (l2 l1 : list (list T)),
  NoDupApp l1 ->
  incl_count (list_eq_dec E) l2 l1 ->
  NoDupApp l2.
Proof.
  induction l2; simpl; intros.
  - constructor.
  - apply incl_count_incl in H0 as Hi.
    specialize (Hi a) as H0'; simpl in *; intuition. clear H2.

    apply in_split in H3. destruct H3. destruct H1. subst.
    eapply incl_pick_inv' in H0 as H0'; eauto.
    rewrite cons_app in H. apply NoDupApp_pick in H. simpl in H.
    eapply NoDupApp_cons.

    eapply IHl2; eauto.
    eapply incl_count_tl; eauto.
    unfold NoDupApp in *; simpl in *. eapply NoDup_app_l; eauto.

    intros; intro.
    unfold NoDupApp in *; simpl in *.
    eapply not_In_NoDup_app in H; eauto.
    apply H.

    apply incl_count_incl in H0'.
    eapply incl_concat in H0'. apply H0'. eauto.
Qed.

Lemma NoDup_incl_count : forall T E (l1 l2 : list T),
  incl_count E l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  unfold incl_count.
  intros.
  rewrite (NoDup_count_occ E) in H0.
  rewrite (NoDup_count_occ E); intros.
  specialize (H x).
  specialize (H0 x).
  omega.
Qed.


(* Automation for solving goals about [NoDup]s of appended lists *)
Lemma NoDupApp_start : forall T (l : list T) ls,
  l = concat ls ->
  NoDup l = NoDupApp ls.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma concat_build_app : forall T (a b : list T) la lb,
  a = concat la ->
  b = concat lb ->
  a ++ b = concat (la ++ lb).
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.

Lemma concat_build_cons : forall T a (b : list T) lb,
  b = concat lb ->
  a :: b = concat ([[a]] ++ lb).
Proof.
  intros; subst.
  rewrite concat_app; auto.
Qed.

Lemma concat_build_nil : forall T,
  @nil T = concat nil.
Proof.
  reflexivity.
Qed.

Lemma concat_build_one : forall T (x : list T),
  x = concat [x].
Proof.
  intros. simpl. rewrite app_nil_r. auto.
Qed.

Ltac concat_build :=
  repeat ( eapply concat_build_app || eapply concat_build_cons || eapply concat_build_one ).

Ltac nodupapp_build :=
  repeat match goal with
  | [ |- context[NoDup (?a ++ ?b)] ] =>
    erewrite NoDupApp_start with (l := a ++ b) by concat_build
  | [ |- context[NoDup (?a :: ?b)] ] =>
    erewrite NoDupApp_start with (l := a :: b) by concat_build
  | [ H : context[NoDup (?a ++ ?b)] |- _ ] =>
    erewrite NoDupApp_start with (l := a ++ b) in H by concat_build
  | [ H : context[NoDup (?a :: ?b)] |- _ ] =>
    erewrite NoDupApp_start with (l := a :: b) in H by concat_build
  end.

Ltac solve_incl_count_one :=
  ( eapply incl_count_rotate_cons; simpl ) || ( eapply incl_count_rotate_one; solve_incl_count_one ).

Ltac solve_incl_count :=
  repeat ( eapply incl_count_rotate_start; solve_incl_count_one );
  eapply incl_count_nil.

Hint Resolve NoDupApp_incl : nodupapp.
Hint Extern 1 (incl_count _ _ _) => solve_incl_count : nodupapp.

Ltac nodupapp :=
  nodupapp_build;
  eauto with nodupapp.

Example nodupapp_5 : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: e ++ a ++ c).
Proof.
  intros.
  nodupapp.
  Grab Existential Variables.
  exact eq_nat_dec.
Qed.

Example nodupapp_3_5 : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: c).
Proof.
  intros.
  nodupapp.
  Grab Existential Variables.
  exact eq_nat_dec.
Qed.

Example nodupapp_fail : forall (a : list nat) b c d e,
  NoDup (a ++ b ++ c ++ d :: e) ->
  NoDup (b ++ d :: e ++ c ++ c).
Proof.
  intros.
  nodupapp.
Abort.

Definition selN_each {T} (l : list (list T)) n (def : T) : list T :=
  map (fun l => selN l n def) l.

Lemma selN_each_S: forall T (l : list (list T)) n def,
  selN_each l (S n) def = selN_each (map (skipn 1) l) n def.
Proof.
  unfold selN_each.
  induction l; cbn -[skipn]; intros; auto.
  rewrite skipn_selN.
  f_equal.
  eauto.
Qed.

Lemma NoDup_NoDupA_eq: forall T E,
  (forall x y, E x y <-> x = y) ->
  forall (l : list T),
  NoDupA E l <-> NoDup l.
Proof.
  induction l; cbn; intros.
  split; constructor.
  split; intro H'; inversion H'; subst.
  constructor; auto.
  rewrite IHl in *.
  rewrite InA_alt in *.
  intro Ha.
  match goal with H: context [not] |- _ => eapply H end.
  eexists; split; eauto.
  eapply H; auto.
  eapply IHl; eauto.
  constructor.
  rewrite InA_alt in *.
  intro Ha.
  destruct Ha; intuition.
  rewrite H in *.
  subst; auto.
  eapply IHl; auto.
Qed.

Lemma NoDup_filter: forall T f (l : list T),
  NoDup l -> NoDup (filter f l).
Proof.
  induction l; cbn; intros.
  constructor.
  inversion H; subst.
  destruct f; auto.
  constructor; eauto.
  rewrite filter_In.
  intuition.
Qed.

Lemma combine_no_dup: forall A B (a : list A) (b : list B),
  NoDup a \/ NoDup b -> NoDup (List.combine a b).
Proof.
  induction a; cbn; intros.
  constructor.
  destruct b.
  constructor.
  intuition try match goal with H : NoDup (_ :: _) |- _ => inversion H; subst end.
  constructor; eauto using in_combine_l.
  constructor; eauto using in_combine_r.
Qed.

Fact NoDup_In_inj: forall T V (f : T -> V) (l : list T),
  NoDup (map f l) ->
  forall a b,
  In a l -> In b l ->
  f a = f b ->
  a = b.
Proof.
  induction l; cbn; intros.
  intuition.
  inversion H; subst.
  match goal with H : f _ = f _ |- _ => rename H into Hf end.
  intuition subst; auto.
  rewrite Hf in *.
  exfalso.
  eauto using in_map.
  rewrite <- Hf in *.
  exfalso.
  eauto using in_map.
Qed.

Lemma filter_ext: forall T (f f' : T -> bool) l,
  (forall x, f x = f' x) ->
  filter f l = filter f' l.
Proof.
  induction l; cbn; intros.
  auto.
  rewrite IHl by auto.
  specialize (H a).
  rewrite H.
  destruct f'; auto.
Qed.

Definition index_of {T} (f : T -> bool) (l : list T) :=
  match (ifind_list (fun x _ => f x) l 0) with
  | Some (i, x) => i
  | None => length l
  end.

Fixpoint sort_by_index {S T} (f : T -> T -> bool) (ls : list (S * T)) (lt : list T) s0 t0 :=
  match lt with
  | nil => nil
  | t :: lt =>
    let i := index_of (fun a => f t (snd a)) ls in
    (selN ls i (s0, t0)) :: (sort_by_index f ls lt s0 t0)
  end.

Definition inb {T} {E} (l : list T) (x : T) :=
  if in_dec E x l then true else false.

Lemma index_of_spec: forall T (l : list T) f d,
  let i := index_of f l in
  i < length l -> f (selN l i d) = true.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'; eauto.
  rewrite Nat.sub_0_r in *.
  intuition.
  match goal with H: _ |- _ => rewrite H end.
  auto.
  omega.
Qed.

Lemma index_of_inb: forall T (l : list T) f,
  (exists x, In x l /\ f x = true) ->
  index_of f l < length l.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite (surjective_pairing p).
  omega.
  destruct H as [x [Ha Hb] ].
  eapply in_selN_exists in Ha.
  destruct Ha as [? [? Ha] ].
  eapply ifind_list_none in H'; eauto.
  rewrite Ha in *.
  congruence.
Unshelve.
  all: eauto.
  destruct p; eauto.
Qed.

Lemma inb_spec: forall T E l x,
  In x l <-> @inb T E l x = true.
Proof.
  unfold inb.
  intros.
  destruct in_dec; intuition congruence.
Qed.

Lemma sort_by_index_length: forall S T t f (l : list (S * T)) s0 t0,
  length (sort_by_index f l t s0 t0) = length t.
Proof.
  induction t; cbn; auto.
Qed.

Lemma sort_by_index_spec: forall S T (ls : list (S * T)) f lt s0 t0,
  (forall x, In x lt -> In x (snd (split ls))) ->
  (forall a b, f a b = true <-> a = b) ->
  snd (split (sort_by_index f ls lt s0 t0)) = lt.
Proof.
  induction lt; cbn.
  auto.
  intros.
  destruct selN eqn: Hp.
  remember (split (sort_by_index _ _ _ _ _)) as r.
  rewrite (surjective_pairing r); cbn.
  subst r.
  rewrite IHlt; auto.
  f_equal.
  unfold index_of in *.
  destruct ifind_list eqn:Ha.
  eapply ifind_list_ok_facts in Ha.
  rewrite Nat.sub_0_r in *.
  intuition subst.
  eapply f_equal with (f := snd) in Hp.
  match goal with H: selN _ _ _ = _ |- _ => rewrite H in * end.
  rewrite Hp in *.
  rewrite H0 in *. subst.
  auto.
  specialize (H a) as ?.
  intuition.
  match goal with H: _ |- _ => eapply in_selN_exists in H;
    destruct H as [i ?]; intuition end.
  rewrite split_length_r in *.
  eapply ifind_list_none with (ix := i) in Ha; eauto.
  rewrite <- selN_split_r in *.
  match goal with
    Hf : context [iff],
    Hb : _ = a |- _ => symmetry in Hb; eapply Hf in Hb end.
  rewrite Ha in *.
  congruence.
Unshelve.
  all: eauto.
Qed.

Lemma index_of_in_sort_by_index: forall T V (fn : T -> V) f (l : list T) d x,
  In x l ->
  NoDup (map fn l) ->
  (forall x y, f x y = true <-> x = y) ->
  selN l (index_of (fun a => f (fn x) (fn a)) l) d = x.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite Nat.sub_0_r in *.
  intuition auto.
  repeat match goal with H: _ |- _ => rewrite H in * end.
  eapply NoDup_In_inj; eauto.
  match goal with H: _ |- _ => rewrite <- H end.
  eapply in_selN; eauto.
  eapply in_selN_exists in H.
  destruct H as [i [? Hs] ].
  eapply ifind_list_none in H'; eauto.
  eapply f_equal with (f := fn) in Hs.
  match goal with H: forall x y, _, H' : f ?a ?b = false |- _ =>
    specialize (H a b) end.
  rewrite Hs in *.
  intuition.
  congruence.
Unshelve.
  all: eauto.
Qed.

Lemma NoDup_selN_index_of_multiple: forall T V f (fn : T -> V) (l : list T) a d,
  NoDup l ->
  In a l ->
  (forall x y, f x y = true <-> x = y) ->
  fn (selN l (index_of (fun x => f (fn a) (fn x)) l) d) <> fn a -> False.
Proof.
  unfold index_of.
  intros.
  destruct ifind_list eqn:H'.
  eapply ifind_list_ok_facts in H'.
  rewrite Nat.sub_0_r in *.
  intuition auto.
  repeat match goal with H: _ |- _ => rewrite H in * end.
  congruence.
  match goal with H: _ |- _ => eapply in_selN_exists in H; destruct H end.
  intuition.
  eapply ifind_list_none in H'; eauto.
  match goal with H: forall x y, _, H' : f ?a ?b = false |- _ =>
    specialize (H a b) end.
  match goal with H: _ |- _ => rewrite H in * end.
  intuition congruence.
Unshelve.
  all: eauto.
Qed.

Lemma in_sort_by_index': forall S T f t (l : list (S * T)) x s0 t0,
  NoDup (map snd l) ->
  In x l ->
  In (snd x) t ->
  (forall x y, f x y = true <-> x = y) ->
  In x (sort_by_index f l t s0 t0).
Proof.
  induction t; cbn; intros.
  auto.
  intuition subst.
  left.
  eapply index_of_in_sort_by_index; auto.
  right.
  eapply IHt; auto.
Qed.

Lemma in_sort_by_index: forall S T f t (l : list (S * T)) (x : S * T) s0 t0,
  NoDup t -> NoDup l ->
  (forall x, In x t -> exists y, In (y, x) l) ->
  (forall x y, f x y = true <-> x = y) ->
  In x (sort_by_index f l t s0 t0) -> In x l /\ In (snd x) t.
Proof.
  induction t; cbn in *.
  intuition auto.
  intros.
  match goal with H: context [iff] |- _ => rename H into Hf end.
  inversion H; subst.
  edestruct (H1 a).
  left; eauto.
  intuition subst.
  eapply in_selN.
  eapply index_of_inb.
  eexists.
  split; try eassumption.
  rewrite Hf; auto.
  match goal with |- ?a = ?b \/ _ => destruct (f a b) eqn:? end.
  left.
  rewrite <- Hf; eauto.
  exfalso; eapply NoDup_selN_index_of_multiple with (fn := snd) (l := l); eauto.
  intro Hs.
  symmetry in Hs.
  rewrite <- Hf in Hs.
  rewrite Hs in *.
  congruence.
  eapply IHt; eauto.
  right.
  eapply IHt; eauto.
Qed.

Lemma filter_elements_permutation: forall T (l : list (T * _)) a t0,
  NoDup (map snd l) ->
  NoDup a ->
  (forall x, In x a -> exists y, In (y, x) l) ->
  let e := (sort_by_index Nat.eqb l a t0 0) in
  let p := filter (fun x => inb (E:=Nat.eq_dec) a (snd x)) l in
  Permutation e p.
Proof.
  cbn; intros.
  eapply Permutation.NoDup_Permutation.
  eapply NoDup_map_inv with (f := snd).
  rewrite map_snd_split.
  rewrite sort_by_index_spec; auto.
  intros.
  match goal with H: _, H': _ |- _ => apply H in H'; destruct H' as [? Ha] end.
  eapply in_split_r in Ha.
  auto.
  eauto using Nat.eqb_eq.
  eapply NoDup_filter.
  eauto using NoDup_map_inv.
  intros.
  intuition.
  match goal with H: _ |- _ => eapply in_sort_by_index in H end.
  rewrite filter_In.
  rewrite <- inb_spec. auto.
  eauto.
  eauto using NoDup_map_inv.
  intuition.
  eauto using Nat.eqb_eq.
  rewrite filter_In in *. intuition cbn in *.
  eapply in_sort_by_index'; cbn; auto.
  rewrite inb_spec; eauto.
  eauto using Nat.eqb_eq.
Unshelve.
  all: eauto.
Qed.

Lemma partition_permutation_app: forall T f (l : list T),
  let p := partition f l in
  Permutation l (fst p ++ snd p).
Proof.
  cbn; induction l; cbn.
  constructor.
  destruct partition eqn:?.
  destruct f; cbn in *.
  constructor.
  auto.
  eapply Permutation_cons_app.
  eauto.
Qed.

Lemma sort_by_index_combine: forall A B f (la : list A) (lb : list B) t a0 b0,
  length la = length lb ->
  incl t lb ->
  (forall x y, f x y = true <-> x = y) ->
  let s := sort_by_index f (List.combine la lb) t a0 b0 in
  s = List.combine (fst (split s)) t.
Proof.
  intros.
  pose proof (split_combine s).
  destruct (split s) eqn:Hs; cbn.
  subst s.
  match goal with H: _ |- _ => rewrite <- H end.
  f_equal.
  eapply f_equal with (f := snd) in Hs; cbn in Hs.
  subst.
  eapply sort_by_index_spec; auto.
  intros.
  rewrite List.combine_split; auto.
Qed.

Lemma partition_eq_filter: forall T (l : list T) f,
  partition f l = (filter f l, filter (fun x => negb (f x)) l).
Proof.
  induction l; cbn; intros.
  auto.
  destruct partition eqn:He; cbn.
  rewrite IHl in He.
  destruct f; cbn; congruence.
Qed.

Lemma filter_map_ext: forall T T' f f' (g : T -> T') l,
  (forall x, In x l -> f x = f' (g x)) ->
  filter f' (map g l) = map g (filter f l).
Proof.
  induction l; cbn; intros.
  auto.
  rewrite H by auto.
  destruct f'; cbn.
  f_equal; auto.
  auto.
Qed.

Lemma filter_r: forall A B (f : B -> bool) (a : list A) b da db,
  length a = length b ->
  filter (fun x => f (snd x)) (List.combine a b) = List.combine (map (fun i => selN a i da) (filter (fun i => f (selN b i db)) (seq 0 (length a)))) (filter f b).
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn in *; try congruence.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn; rewrite map_map.
  f_equal.
  all: eauto.
Qed.

Lemma filter_l: forall A B (f : A -> bool) a b da (db : B),
  length a = length b ->
  filter (fun x => f (fst x)) (List.combine a b) = List.combine (filter f a) (map (fun i => selN b i db) (filter (fun i => f (selN a i da)) (seq 0 (length a)))).
Proof.
  induction a; cbn; intros.
  auto.
  destruct b; cbn in *; try congruence.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn; rewrite map_map.
  f_equal.
  all: eauto.
Qed.

Lemma filter_selN_length: forall T f (l : list T) d,
  length (filter f l) = length (filter (fun i => f (selN l i d)) (seq 0 (length l))).
Proof.
  induction l; cbn; intros.
  auto.
  rewrite <- seq_shift.
  erewrite filter_map_ext.
  destruct f; cbn.
  f_equal.
  all: autorewrite with lists; eauto.
Qed.

Lemma permutation_filter: forall T E (l l' : list T),
  NoDup l -> NoDup l' ->
  incl l' l ->
  Permutation.Permutation (filter (@inb _ E l') l) l'.
Proof.
  intros.
  apply Permutation.NoDup_Permutation; auto using NoDup_filter.
  intros.
  rewrite filter_In.
  unfold inb.
  destruct in_dec; intuition.
Qed.


Lemma app_split_length_eq_l :
  forall T (l1 l2 l1' l2': list T),
    l1++l2 = l1'++l2' ->
    length l1 = length l1' ->
    l1 = l1' /\ l2 = l2'.
Proof.
  induction l1; simpl; intros.
  symmetry in H0.
  apply length_zero_iff_nil in H0.
  subst.
  simpl; eauto.

  destruct l1'; simpl in *.
  inversion H0.
  inversion H; subst.
  edestruct IHl1; eauto; subst; eauto.
Qed.

Lemma app_split_length_eq_r :
  forall T (l2 l1 l1' l2': list T),
    l1++l2 = l1'++l2' ->
    length l2 = length l2' ->
    l1 = l1' /\ l2 = l2'.
Proof.
  induction l2; simpl; intros.
  symmetry in H0.
  apply length_zero_iff_nil in H0; subst.
  repeat rewrite app_nil_r in *; eauto.

  destruct l2'; simpl in *.
  inversion H0.
  rewrite <- cons_nil_app in H.
  setoid_rewrite <- cons_nil_app in H at 2.
  edestruct IHl2; eauto; subst; eauto.
  apply app_inj_tail in H1; destruct H1; subst; eauto.
Qed.

 Lemma length_lt_prefix:
    forall T (l1 l2 l3 l4: list T),
      l1++l2=l3++l4 ->
      length l1 < length l3 ->
      exists l1', l3 = l1++l1' /\ l1' <> [].
  Proof.
    induction l1; simpl in *; intros; eauto.
    destruct l3; simpl in *.
    inversion H0.
    eexists; split; eauto.
    congruence.
    destruct l3; simpl in *.
    inversion H0.
    inversion H; subst.
    edestruct IHl1; eauto.
    omega.
    destruct H1; subst.
    eexists; eauto.
  Qed.

  
Lemma dedup_last_app:
  forall A AEQ (l1 l2: list A),
    dedup_last AEQ (l1 ++ l2) =
    filter (fun a => negb (in_dec_b AEQ a l2)) (dedup_last AEQ l1) ++
           dedup_last AEQ l2.

Proof.
  induction l1; simpl; intros; eauto.
  
  destruct (in_dec AEQ a l1);
  destruct (in_dec AEQ a (l1 ++ l2)); eauto.
  exfalso; apply n; eauto.
  apply in_app_or in i; intuition eauto.
  simpl.
  eapply in_iff_in_dec_b in H; eauto.
  rewrite H; simpl; eauto.
  simpl.
  destruct (in_dec_b AEQ a l2) eqn:D; simpl; eauto.
  eapply in_iff_in_dec_b in D.
  exfalso; apply n0; eauto.
  rewrite IHl1; eauto.
Qed.
  
  Lemma dedup_last_length:
    forall A AEQ (l: list A),
      length (dedup_last AEQ l) <= length l.
  Proof.
    induction l; simpl; eauto.
    destruct (in_dec AEQ a l); simpl; eauto; omega.
  Qed.
  
  Lemma dedup_by_list_length:
    forall A AEQ B (l1: list A) (l2: list B),
      length (dedup_by_list AEQ l1 l2) <= length l1 /\
      length (dedup_by_list AEQ l1 l2) <= length l2.
  Proof.
    induction l1; destruct l2;
    simpl; intros; try solve [split; try omega].
    
    specialize (IHl1 l2); destruct IHl1.
    destruct (in_dec AEQ a l1); simpl; split; try omega.
  Qed.
  
  
  Lemma dedup_last_dedup_by_list_length_le:
    forall A AEQ B (l1: list A) (l2: list B),
      length l1 <= length l2 ->
      length (dedup_last AEQ l1) =
      length (dedup_by_list AEQ l1 l2).
  Proof.
    induction l1; destruct l2;
    simpl; intros; try omega.
    
    destruct (in_dec AEQ a l1);
    simpl; try solve [ exfalso; eauto];
    try omega.
    apply IHl1; omega.
    specialize (IHl1 l2); omega.
  Qed.
  
  Lemma dedup_last_length_not_in_tail_S:
    forall A AEQ (l: list A) a,
      ~In a l ->
      length (dedup_last AEQ (l ++ [a])) = S (length (dedup_last AEQ l)).
  Proof.
    induction l; simpl; intros; intuition.
    destruct (in_dec AEQ a l);
    destruct (in_dec AEQ a (l ++ [a0]));
    eauto; try solve [exfalso; eauto].
    apply in_app_or in i; simpl in *; intuition eauto.
    congruence.
    simpl; eauto.
  Qed.
  
  Lemma dedup_last_length_in_tail:
    forall A AEQ (l: list A) a,
      In a l ->
      length (dedup_last AEQ (l ++ [a])) = length (dedup_last AEQ l).
  Proof.
    induction l; simpl; intros; intuition.
    - subst.
      destruct (in_dec AEQ a0 l);
      destruct (in_dec AEQ a0 (l ++ [a0]));
      eauto; try solve [exfalso; eauto].
      simpl.
      apply dedup_last_length_not_in_tail_S; eauto.
      exfalso; apply n0;
      apply in_or_app; simpl; eauto.
      
    - destruct (in_dec AEQ a l);
      destruct (in_dec AEQ a (l ++ [a0]));
      eauto; try solve [exfalso; eauto].
      apply in_app_or in i; simpl in *; intuition eauto.
      subst; exfalso; eauto.
      simpl; eauto.
  Qed.
  
  Lemma dedup_last_app_length_comm:
    forall A AEQ (l1 l2: list A),
      length (dedup_last AEQ (l2++l1)) =
      length (dedup_last AEQ (l1++l2)).
  Proof.
    induction l1;
    simpl; intros;
    try rewrite app_nil_r; try omega.
    rewrite cons_app.
    rewrite app_assoc.
    erewrite IHl1.
    rewrite app_assoc.
    
    destruct (in_dec AEQ a (l1 ++ l2));
    simpl; try solve [ exfalso; eauto];
    try omega; eauto.
    apply dedup_last_length_in_tail; eauto.
    apply dedup_last_length_not_in_tail_S; eauto.
  Qed.
  
  Lemma dedup_last_app_length:
    forall A AEQ  (l2 l1: list A),
      length (dedup_last AEQ l1) <=
      length (dedup_last AEQ (l2++l1)).
  Proof.
    induction l2;
    simpl; intros; try omega.
    
    destruct (in_dec AEQ a (l2 ++ l1));
    simpl; try solve [ exfalso; eauto];
    try omega; eauto.
  Qed.
  
