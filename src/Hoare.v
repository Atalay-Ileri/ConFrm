Require Import BaseTypes Prog ProgAuto.
Require Import Disk SepLogic.
Import PredNotations.
Open Scope pred_scope.

Set Implicit Arguments.


(** ** Hoare logic *)
Definition precond := user -> oracle ->  store -> @pred addr valueset.
Definition postcond {T: Type} := user -> oracle ->  store ->
                                 oracle -> store -> T -> @pred addr valueset.
Definition crashcond := user -> oracle ->  store ->
                        oracle -> store -> @pred addr valueset.

Definition can_exec {T: Type} (pre: precond) (p: prog T):=
  forall u o d s,
    pre u o s d ->
    (exists  o' d' s' r tr, exec u o d s p (Finished o' d' s' r) tr).

Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond):=
  forall u o d s ret tr,
    pre u o s d ->
    exec u o d s p ret tr ->
    ((exists o' d' s' r,
         ret = Finished o' d' s' r
         /\ post u o s o' s' r d') \/
     (exists o' d' s',
        ret = Crashed _ o' d' s' /\ crash u o s o' s' d')) /\
    trace_ok tr.

Notation
  "<< u , o , s >> pre p" :=
  (forall F, can_exec (fun (u:user) (o:oracle) (s: store) => F * pre) p)
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level,
     format "'[v  ' '<<' u ','  o ','  s '>>' '//' '[' pre ']' '//' '[' p ']' ']'").


  
Notation
  "<< u , o , s >> pre p << o' , s' , r >> post crash" :=
  (forall F, hoare_triple (fun (u:user) (o:oracle) (s: store) => F * pre) p (fun (u:user) (o:oracle) (s: store) (o':oracle) (s': store) r => F * post ) (fun u (o:oracle) (s: store) o' s' => F * crash))
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level, o' at next level, s' at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' u ','  o ','  s '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' o' ','  s' ','  r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Example read_can_exec:
  forall a v,
    << u, o, s >>
      (a |-> v)
      (Read a).
Proof. intros. Abort.

Example read_spec:
  forall a v,
    <<u, o, s>>
      (a |-> v)
      (Read a)
    << o', s', r >>
      ([s' r = Some (fst v)] * a |-> v)
      (a |-> v).
Proof. intros. Abort.


Definition complete {T: Type} (pre: precond) (p: prog T) (post: postcond) (crash: crashcond):=
  can_exec pre p /\ hoare_triple pre p post crash.

Theorem can_exec_strengthen_pre:
  forall T (p: prog T) (pre pre': precond),
  can_exec pre p ->
  (forall  u o s, pre' u o s ===>  pre u o s) ->
  can_exec pre' p.
Proof.
  unfold complete, can_exec; intros;
  edestruct H; intros; eauto.  
  eapply H0; eauto.
Qed.

Theorem hoare_triple_strengthen_pre:
  forall T (p: prog T) (pre pre': precond) post crash,
  hoare_triple pre p post crash ->
  (forall  u o s, pre' u o s ===>  pre u o s) ->
  hoare_triple pre' p post crash.
Proof.
  unfold complete, hoare_triple; intros;
    edestruct H; intros; eauto.
  eapply H0; eauto.
Qed.

Theorem complete_strengthen_pre:
  forall T (p: prog T) (pre pre': precond) post crash,
  complete pre p post crash ->
  (forall  u o s, pre' u o s ===>  pre u o s) ->
  complete pre' p post crash.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  eapply H, H0; eauto.
  eapply H1. eapply H0; eauto.
  eauto.
Qed.

Theorem hoare_triple_weaken_post_weak:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall  u o d s o' d' s' r tr,
      pre u o s d ->
      exec u o d s p (Finished o' d' s' r) tr ->
      post u o s o' s' r d' ->
      post' u o s o' s' r d') ->
  hoare_triple pre p post' crash.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    edestruct H; intros; eauto.
  split; eauto; destruct H3; eauto.
  cleanup.
  left; repeat eexists; eauto.
Qed.


Theorem complete_weaken_post_weak:
  forall T (p: prog T) pre (post post': postcond) crash,
  complete pre p post crash ->
  (forall  u o d s o' d' s' r tr,
      pre u o s d ->
      exec u o d s p (Finished o' d' s' r) tr ->
      post u o s o' s' r d' ->
      post' u o s o' s' r d') ->
  complete pre p post' crash.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  edestruct H1; eauto.
  split; eauto; destruct H4; eauto.
  cleanup.
  left; repeat eexists; eauto.
Qed.

Theorem hoare_triple_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall  u o s o' s' (r: T),
      post u o s o' s' r ===>
      post' u o s o' s' r) ->
  hoare_triple pre p post' crash.
Proof.
  intros; eapply hoare_triple_weaken_post_weak; eauto.
  intros; eapply H0; eauto.
Qed.


Theorem complete_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  complete pre p post crash ->
  (forall  u o s o' s' (r: T),
      post u o s o' s' r ===>
      post' u o s o' s' r) ->
  complete pre p post' crash.
Proof.
  intros; eapply complete_weaken_post_weak; eauto.
  intros; eapply H0; eauto.
Qed.

Theorem hoare_triple_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall  u o d s o' d' s' tr,
      pre u o s d ->
      exec u o d s p (Crashed _ o' d' s') tr ->
      crash u o s o' s' d' ->
      crash' u o s o' s' d') ->
  hoare_triple pre p post crash'.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    edestruct H; intros; eauto.
  split; eauto; destruct H3; eauto.
  cleanup.
  right; repeat eexists; eauto.
Qed.

Theorem complete_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  complete pre p post crash ->
  (forall  u o d s o' d' s' tr,
      pre u o s d ->
      exec u o d s p (Crashed _ o' d' s') tr ->
      crash u o s o' s' d' ->
      crash' u o s o' s' d') ->
  complete pre p post crash'.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  edestruct H1; eauto.
  split; eauto; destruct H4; eauto.
  cleanup.
  right; repeat eexists; eauto.
Qed.

Theorem hoare_triple_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall  u o s o' s', crash u o s o' s' ===> crash' u o s o' s') ->
  hoare_triple pre p post crash'.
Proof.
  intros; eapply hoare_triple_weaken_crash_weak; eauto.
  intros; eapply H0; eauto.
Qed.

Theorem complete_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  complete pre p post crash ->
  (forall  u o s o' s', crash u o s o' s' ===> crash' u o s o' s') ->
  complete pre p post crash'.
Proof.
  intros; eapply complete_weaken_crash_weak; eauto.
  intros; eapply H0; eauto.
Qed.

Theorem complete_pimpl_strong :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 pre2 post1 post2 crash1 crash2,
      complete pre1 p1 post1 crash1 ->
      (forall r, complete pre2 (p2 r) post2 crash2) ->
    (forall  u o d s o' d' s' r tr,
      pre1 u o s d ->
      exec u o d s p1 (Finished o' d' s' r) tr ->
      post1 u o s o' s' r d' ->
      pre2 u o' s' d') ->
    (forall u o d s o' d' s' tr,
      pre1 u o s d ->
      exec u o d s p1 (Crashed _ o' d' s') tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
    (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      pre2 u o' s' d' ->
      exec u o' d' s' (p2 r) (Finished o'' d'' s'' r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      pre2 u o' s' d' ->
      exec u o' d' s' (p2 r) (Crashed _ o'' d'' s'') tr ->
      crash2 u o s o'' s'' d'') ->
    complete pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  {
    edestruct H; eauto; cleanup.
    edestruct H0; eauto.
    edestruct H8; eauto.
    eapply H1; eauto.
    edestruct H5; eauto.
    destruct H10; cleanup; eauto.
    cleanup; eauto.
    repeat eexists; econstructor; eauto.
  }
  {
    inv_exec_perm.
    {
      edestruct H5; eauto.
      destruct H9; cleanup.
      edestruct H0; eauto.
      edestruct H12; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app; eauto.
    }
    {
      destruct H7.
      - edestruct H5; eauto; destruct H8; cleanup.
        split; eauto; right; repeat eexists; eauto.
      - cleanup.
        edestruct H5; eauto; destruct H9; cleanup.
        edestruct H0; eauto.
        edestruct H12; eauto; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        apply trace_ok_app; eauto.
    }
  }
Qed.

Theorem complete_pimpl_weak :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 pre2 post1 post2 crash1 crash2,
      complete pre1 p1 post1 crash1 ->
      (forall u o d s o' d' s' r tr,
      pre1 u o s d ->
      exec u o d s p1 (Finished o' d' s' r) tr ->
      complete pre2 (p2 r) post2 crash2) ->
    (forall  u o d s o' d' s' r tr,
      pre1 u o s d ->
      exec u o d s p1 (Finished o' d' s' r) tr ->
      post1 u o s o' s' r d' ->
      pre2 u o' s' d') ->
    (forall u o d s o' d' s' tr,
      pre1 u o s d ->
      exec u o d s p1 (Crashed _ o' d' s') tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
     (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      pre2 u o' s' d' ->
      exec u o' d' s' (p2 r) (Finished o'' d'' s'' r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      pre2 u o' s' d' ->
      exec u o' d' s' (p2 r) (Crashed _ o'' d'' s'') tr ->
      crash2 u o s o'' s'' d'') ->
    complete pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  {
    edestruct H; eauto; cleanup.
    edestruct H0; eauto.
    edestruct H8; eauto.
    eapply H1; eauto.
    edestruct H5; eauto; destruct H10; cleanup; eauto.
    cleanup.
    repeat eexists; econstructor; eauto.
  }
  {
    inv_exec_perm.
    {
      edestruct H5; eauto; destruct H9; cleanup.
      edestruct H0; eauto.
      edestruct H12; eauto; destruct H13; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app; eauto.
    }
    {
      destruct H7.
      - edestruct H5; eauto; destruct H8; cleanup.
        split; eauto; right; repeat eexists; eauto.
      - cleanup.
        edestruct H5; eauto; destruct H9; cleanup.
        edestruct H0; eauto.
        edestruct H12; eauto; destruct H13; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        apply trace_ok_app; eauto.
    }
  }
Qed.

Theorem complete_equivalence :
  forall T (p p': prog T) pre post crash,
    complete pre p post crash ->
    prog_equiv p p' ->
    complete pre p' post crash.
Proof.
  unfold complete, can_exec, hoare_triple; intros;
    destruct H; split; intros; eauto.
  edestruct H; eauto; cleanup.
  repeat eexists; eauto.
  eapply H0; eauto.

  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
Qed.


Ltac monad_simpl_one :=
  match goal with
  | [ |- complete _ (Bind (Bind _ _) _) _ _ ] =>
    eapply complete_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.