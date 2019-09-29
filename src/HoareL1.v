Require Import List BaseTypes Layer1 ProgAuto CommonAutomation.
Require Import Disk Memx Predx SepAuto Simulation.
Import ListNotations.

Set Implicit Arguments.


(** ** Hoare logic *)
Definition precond := oracle token -> @pred addr addr_dec (set value).
Definition postcond {T: Type} := T -> @pred addr addr_dec (set value).
Definition crashcond := @pred addr addr_dec (set value).


Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond):=
  forall o d ret,
    pre o d ->
    exec o d p ret ->
    ((exists d' r,
         ret = Finished d' r
         /\ post r d') \/
     (exists d',
        ret = Crashed d' /\ crash d'))%type.


  
Notation
  "<< o >> pre p << r >> post crash" :=
  (forall F, hoare_triple
          (fun (o:oracle token) => F * pre)%pred
          p
          (fun  r => F * post)%pred
          (F * crash)%pred)
    (at level 10, o at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Notation
  "{{ e1 }} << o >> pre p << r >> post crash" :=
   (exists e1, (forall F, hoare_triple
          (fun (o:oracle token) => F * pre)%pred
          p
          (fun r => F * post)%pred
          (F * crash)%pred))
    (at level 10, o at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '{{' e1 '}}' '//' '[  ' '<<' o '>>' '//' pre '//' p ']' '//' '[  ' '<<' r '>>' '//' post '//' crash ']' ']'").


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
  (forall  o d r,
      pre o d ->
      post r =p=>
      post' r) ->
  hoare_triple pre p post' crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup.
  left; repeat eexists; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall (r: T),
      post r =p=>
      post' r) ->
  hoare_triple pre p post' crash.
Proof.
  intros; eapply hoare_triple_weaken_post_weak; eauto.
Qed.

Theorem hoare_triple_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall  o d,
      pre o d ->
      crash =p=>
      crash') ->
  hoare_triple pre p post crash'.
Proof.
  unfold  hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup.
  right; repeat eexists; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (crash =p=> crash') ->
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

(*
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

Theorem hoare_triple_pimpl :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall o d r,
          pre1 o d ->
          hoare_triple (fun o' => post1 o o' r)%pred (p2 r) post2 crash2) ->
    (forall o d o',
      pre1 o d ->
      crash1 o o' =p=> crash2 o o') ->
    (forall o d o' d' o'' r r2,
      pre1 o d ->
      post1 o o' r d' ->
      post2 o' o'' r2 =p=> post2 o o'' r2) ->
    (forall o d o' d' o'' r,
      pre1 o d ->
      post1 o o' r d' ->
      crash2 o' o'' =p=> crash2 o o'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  invert_exec.
  {
    edestruct H; eauto; cleanup;
    edestruct H0; eauto; cleanup.
    left; repeat eexists; eauto.
    eapply H2; eauto.
  }
  {
    destruct H5; cleanup;
    edestruct H; eauto; cleanup.
    - right; repeat eexists; eauto.
      eapply H1; eauto.
    - edestruct H0; eauto; cleanup.
      right; repeat eexists; eauto.
      eapply H3; eauto.
  }
  {
    destruct H5; cleanup;
    edestruct H; eauto; cleanup;
    edestruct H0; eauto; cleanup.
  }
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


Lemma deterministic_prog:
  forall T (p: prog T) st ret1 ret2,
    exec st p ret1 ->
    exec st p ret2 ->
    ret1 = ret2.
Proof.
  unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
      destruct_pairs; cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  eauto.
  
  destruct H0; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H0; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  
  destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H0; cleanup; destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  eauto.

  destruct H0; cleanup; destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  
  destruct H0; cleanup; destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H0; cleanup; destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  eauto.
Qed.
*)