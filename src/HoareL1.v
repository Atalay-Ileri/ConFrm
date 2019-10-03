Require Import PeanoNat List BaseTypes Layer1 ProgAuto CommonAutomation.
Require Import Streams Disk Memx Predx SepAuto Simulation.
Import ListNotations.

Set Implicit Arguments.

Fixpoint Str_firstn {T} n (s: Stream T) : list T :=
  match n with
  |0 => nil
  |S n' => hd s :: Str_firstn n' (tl s)
  end.

(** ** Hoare logic *)
Definition precond := oracle -> @pred addr addr_dec (set value).
Definition postcond {T: Type} := oracle -> T -> @pred addr addr_dec (set value).
Definition crashcond := oracle -> @pred addr addr_dec (set value).


Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond):=
  forall o d,
    pre o d ->
    (exists o' ret,
        exec o d p o' ret /\
        ((exists d' r,
             ret = Finished d' r
             /\ post o' r d') \/
         (exists d',
             ret = Crashed d' /\ crash o' d')))%type.
  
Notation
  "<< o >> pre p << o' , r >> post crash" :=
  (forall F, hoare_triple
          (fun o => F * pre)%pred
          p
          (fun (o': oracle) r => F * post)%pred
          (fun o' => F * crash)%pred)
    (at level 10,
     o at next level,
     pre at next level,
     p at next level,
     o' at next level,
     r at next level,
     post at next level,
     crash at next level,
     format "'[v' '[  ' '<<' o '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' o' ',' r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

(*
Notation
  "{{ e1 }} << o >> pre p << r >> post crash" :=
   (exists e1, (forall F, hoare_triple
          (fun o => F * pre)%pred
          p
          (fun o r => F * post)%pred
          (F * crash)%pred))
    (at level 10, o at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '{{' e1 '}}' '//' '[  ' '<<' o '>>' '//' pre '//' p ']' '//' '[  ' '<<' r '>>' '//' post '//' crash ']' ']'").
*)

Theorem hoare_triple_strengthen_pre:
  forall T (p: prog T) (pre pre': precond) post crash,
  hoare_triple pre p post crash ->
  (forall o, pre' o =p=>  pre o) ->
  hoare_triple pre' p post crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_post_weak:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall o o' d r,
      pre o d ->
      post o' r =p=>
      post' o' r) ->
  hoare_triple pre p post' crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup; split_ors; cleanup.
  do 2 eexists; split; eauto.  
  left; repeat eexists; eauto.
  eapply H0; eauto.
  do 2 eexists; split; eauto.
Qed.


Theorem hoare_triple_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall o (r: T),
      post o r =p=>
      post' o r) ->
  hoare_triple pre p post' crash.
Proof.
  intros; eapply hoare_triple_weaken_post_weak; eauto.
Qed.

Theorem hoare_triple_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall o o' d,
      pre o d ->
      crash o' =p=>
      crash' o') ->
  hoare_triple pre p post crash'.
Proof.
  unfold  hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup; split_ors; cleanup.
  do 2 eexists; split; eauto.
  do 2 eexists; split; eauto.  
  right; repeat eexists; eauto.
  eapply H0; eauto. 
Qed.


Theorem hoare_triple_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall o, crash o =p=> crash' o) ->
  hoare_triple pre p post crash'.
Proof.
  intros; eapply hoare_triple_weaken_crash_weak; eauto.
Qed.

(*
Theorem hoare_triple_pimpl_strong :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 pre2 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall r, hoare_triple pre2 (p2 r) post2 crash2) ->
    (forall o d o' d' r,
      pre1 o d ->
      exec o d p1 (Finished d' r) ->
      post1 o o' r d' ->
      pre2 o' d') ->
    (forall o d o' d',
      pre1 o d ->
      exec (o, d) p1 (Crashed (o', d')) ->
      crash1 o o' d' ->
      crash2 o o' d') ->
    (forall o o' d' o'' d'' r r2,
      post1 o o' r d' ->
      pre2 o' d' ->
      exec (o', d') (p2 r) (Finished (o'', d'') r2) ->
      post2 o o'' r2 d'') ->
    (forall o o' d' o'' d'' r,
      post1 o o' r d' ->
      pre2 o' d' ->
      exec (o', d') (p2 r) (Crashed (o'', d'')) ->
      crash2 o o'' d'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  invert_exec.
  {
    edestruct H; eauto; cleanup.
    edestruct H0; eauto; cleanup.
    left; repeat eexists; eauto.
  }
  {
    destruct H6; cleanup;
    edestruct H; eauto; cleanup.
    - right; repeat eexists; eauto.
    - edestruct H0; eauto; cleanup.
      right; repeat eexists; eauto.
  }
  {
    destruct H6; cleanup;
    edestruct H; eauto; cleanup;
    edestruct H0; eauto; cleanup.
  }
Qed.

Theorem hoare_triple_pimpl' :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall r, hoare_triple (fun u o' s' => exists o s d, [[pre1 u o s d]] * post1 u o s o' s' r)%pred (p2 r) post2 crash2) ->
    (forall u o d s o' d' s' tr,
      pre1 u o s d ->
      exec (u, o, d, s) p1 (Crashed (u, o', d', s')) tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
    (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      exec (u, o', d', s') (p2 r) (Finished (u, o'', d'', s'') r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      exec (u, o', d', s') (p2 r) (Crashed (u, o'', d'', s'')) tr ->
      crash2 u o s o'' s'' d'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  invert_exec.
  {
      edestruct H; eauto.
      destruct H7; cleanup.
      edestruct H0; eauto.
      pred_apply; cancel; eauto.
      destruct H7; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app_merge; eauto.
    }
    {
      destruct H5.
      - edestruct H; eauto; destruct H6; cleanup.
        split; eauto; right; repeat eexists; eauto.
      - cleanup.
        edestruct H; eauto; destruct H7; cleanup.
        edestruct H0; eauto.
        pred_apply; cancel; eauto.
        destruct H7; eauto; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        apply trace_ok_app_merge; eauto.
    }
Qed.

Theorem hoare_triple_pimpl'' :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall u o s d r,
          pre1 u o s d ->
          hoare_triple (fun u' o' s' => [[u = u']] * post1 u' o s o' s' r)%pred (p2 r) post2 crash2) ->
    (forall u o d s o' d' s' tr,
      pre1 u o s d ->
      exec (u, o, d, s) p1 (Crashed (u, o', d', s')) tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
    (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      exec (u, o', d', s') (p2 r) (Finished (u, o'', d'', s'') r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      exec (u, o', d', s') (p2 r) (Crashed (u, o'', d'', s'')) tr ->
      crash2 u o s o'' s'' d'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  invert_exec.
  {
      edestruct H; eauto.
      destruct H7; cleanup.
      edestruct H0; eauto.
      pred_apply; cancel; eauto.
      destruct H7; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app_merge; eauto.
    }
    {
      destruct H5.
      - edestruct H; eauto; destruct H6; cleanup.
        split; eauto; right; repeat eexists; eauto.
      - cleanup.
        edestruct H; eauto; destruct H7; cleanup.
        edestruct H0; eauto.
        pred_apply; cancel; eauto.
        destruct H7; eauto; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        apply trace_ok_app_merge; eauto.
    }
Qed.
 *)

Lemma exec_oracle_prefix:
  forall T (p: prog T) o o' d ret,
    exec o d p o' ret ->
    exists n, o' = Str_nth_tl n o.
Proof.
  induction p; simpl in *; intros;
    invert_exec; cleanup;
      try solve [exists 1; simpl; eauto].
  - edestruct IHp; eauto; cleanup.
    edestruct H; eauto; cleanup.
    eexists; rewrite Str_nth_tl_plus; eauto.
  - split_ors.
    + edestruct IHp; eauto; cleanup.
    + edestruct IHp; eauto; cleanup.
      edestruct H; eauto; cleanup.
      eexists; rewrite Str_nth_tl_plus; eauto.
  - split_ors.
    + edestruct IHp; eauto; cleanup.
    + edestruct IHp; eauto; cleanup.
      edestruct H; eauto; cleanup.
      eexists; rewrite Str_nth_tl_plus; eauto.
Qed.

(*
Lemma exec_crash_in:
  forall T (p: prog T) o o' d d',
    exec o d p o' (Crashed d') ->
    In Crash o.
Proof.
  induction p; simpl in *; intros;
    invert_exec; intuition; eauto.
  cleanup.
  apply in_app_iff; eauto.
Qed.
 *)

Theorem hoare_triple_pimpl :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 pre2 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall o1 d,
         pre1 o1 d ->
         (forall o2 r, post1 o2 r =p=> pre2 o2)) ->
      (forall o1 d r,
         pre1 o1 d ->
         (forall o2, post1 o2 r =p=> pre2 o2) ->
          hoare_triple pre2 (p2 r) post2 crash2) ->
    (forall o o2 d,
      pre1 o d ->
      crash1 o2 =p=> crash2 o2) ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  specialize H0 with (1:=H3).
  specialize H1 with (1:=H3).
  split_ors.
  - (* p1 Finished *)    
    edestruct H1; eauto.
    eapply H0; eauto.
    cleanup.
    split_ors; cleanup.
    + (* p2 Finished *)
      do 2 eexists. intuition eauto.
    + (* p2 Crashed *)
      do 2 eexists. intuition eauto.
  - (* p1 Crashed *)
    do 2 eexists. intuition eauto.
    right; intuition eauto.
    eexists; intuition eauto.
    eapply H2; eauto.
Qed.


Theorem hoare_triple_equivalence :
  forall T (p p': prog T) pre post crash,
    hoare_triple pre p post crash ->
    prog_equiv p p' ->
    hoare_triple pre p' post crash.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
Qed.


Ltac monad_simpl_one :=
  match goal with
  | [ |- hoare_triple _ (Bind (Bind _ _) _) _ _ ] =>
    eapply hoare_triple_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.

Lemma Str_firstn_hd:
  forall T (m : nat) (s2 s1 : Stream T),
  Str_firstn m s1 = Str_firstn m s2 ->
  hd (Str_nth_tl m s1) = hd (Str_nth_tl m s2) ->
  hd s1 = hd s2 /\ Str_firstn m (tl s1) = Str_firstn m (tl s2).
Proof.
  induction m; simpl; intros; eauto.
  cleanup.
  edestruct IHm; eauto.
  destruct s1, s2; simpl in *.
  destruct m; simpl in *; cleanup; eauto.
Qed.

Lemma Str_firstn_Str_nth_tl_eq:
  forall T n m (s1 s2: Stream T),
    Str_firstn m s1 = Str_firstn m s2 ->
    Str_firstn n (Str_nth_tl m s1) =
    Str_firstn n (Str_nth_tl m s2) ->
    Str_firstn (n + m) s1 = Str_firstn (n + m) s2.
Proof.
  induction n; simpl; intros; eauto.
  cleanup.
  repeat rewrite tl_nth_tl in H3.
  erewrite IHn.
  3: eauto.
  destruct m; simpl in *; cleanup.
  rewrite Nat.add_0_r; eauto.
  eauto.

  eapply Str_firstn_hd in H; eauto; cleanup; eauto.
Qed.

Lemma exec_finished_deterministic:
  forall T (p: prog T) o1 o1' o2 o2' st st1 st2 r1 r2,
    exec o1 st p o1' (Finished st1 r1)->
    exec o2 st p o2' (Finished st2 r2) ->
    st1 = st2 /\ r1 = r2 /\
    exists n,
      Str_firstn n o1 = Str_firstn n o2 /\
      Str_nth_tl n o1 = o1' /\
      Str_nth_tl n o2 = o2'.
Proof.
    unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
    destruct_pairs; cleanup; eauto;
    try solve [intuition;
    exists 1; simpl; intuition].
    specialize IHp with (1:=H0)(2:=H1); eauto; cleanup.
    specialize H with (1:=H2)(2:=H3); cleanup.
    repeat rewrite Str_nth_tl_plus; eauto.
    intuition.
    eexists; repeat split; try reflexivity.
    eapply Str_firstn_Str_nth_tl_eq; eauto.
Qed.

(*
Lemma exec_finished_oracle_app:
  forall T (p: prog T) o1 o2 st st1 r1 ret,
    exec o1 st p (Finished st1 r1)->
    exec (o1++o2) st p ret ->
    o2 = [] /\ ret = Finished st1 r1.
Proof.
    unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
      destruct_pairs; cleanup; eauto.
    -
      eapply exec_finished_deterministic in H0; eauto; cleanup.
      eapply exec_finished_deterministic in H4; eauto; cleanup.
      rewrite <- app_assoc in H3.
      apply app_inv_head in H3; cleanup; eauto.
      setoid_rewrite <- app_nil_r in H3 at 4.
      apply app_inv_head in H3; cleanup; eauto.
    - split_ors.
      +
        rewrite <- app_assoc in H1; eauto.
        edestruct IHp; eauto; inversion H4.
      +
        eapply exec_finished_deterministic in H0; eauto; cleanup.
        rewrite <- app_assoc in H4.
        apply app_inv_head in H4; cleanup; eauto.
    - split_ors.
      +
        rewrite <- app_assoc in H1; eauto.
        edestruct IHp; eauto; inversion H4.
      +
        eapply exec_finished_deterministic in H0; eauto; cleanup.
        rewrite <- app_assoc in H4.
        apply app_inv_head in H4; cleanup; eauto.
Qed.
 *)

Lemma deterministic_prog:
  forall T (p: prog T) o o1 o2 st ret1 ret2,
    exec o st p o1 ret1 ->
    exec o st p o2 ret2 ->
    o1 = o2 /\ ret1 = ret2.
Proof.
  unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
      destruct_pairs; cleanup; eauto;
try solve [
              eapply exec_finished_deterministic in H0; eauto; cleanup;
              eapply exec_finished_deterministic in H3; eauto; cleanup; eauto];
try solve [
          destruct H0; cleanup; eauto;
          [
            eapply IHp in H0; eauto; cleanup |
            eapply exec_finished_deterministic in H0; eauto; cleanup;
            eauto] ];
  try solve [
          destruct H1; cleanup; eauto;
          [
            eapply IHp in H0; eauto; cleanup |
            eapply exec_finished_deterministic in H0; eauto; cleanup;
            eauto] ];
  try solve [
        destruct H0; destruct H1; cleanup; [
          specialize IHp with (1:= H0)(2:=H1); cleanup; eauto |
          eapply IHp in H0; eauto; cleanup |
          eapply IHp in H0; eauto; cleanup |    
          eapply exec_finished_deterministic in H0; eauto; cleanup;
          eauto] ].
Qed.
