Require Import BaseTypes Prog ProgAuto.
Require Import Disk Memx Predx SepAuto.

Set Implicit Arguments.


(** ** Hoare logic *)
Definition precond := user -> oracle ->  store -> @pred addr addr_dec valueset.
Definition postcond {T: Type} := user -> oracle ->  store ->
                                 oracle -> store -> T -> @pred addr addr_dec valueset.
Definition crashcond := user -> oracle ->  store ->
                        oracle -> store -> @pred addr addr_dec valueset.


Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond):=
  forall u o d s ret tr,
    pre u o s d ->
    exec u o d s p ret tr ->
    ((exists o' d' s' r,
         ret = Finished o' d' s' r
         /\ post u o s o' s' r d') \/
     (exists o' d' s',
        ret = Crashed _ o' d' s' /\ crash u o s o' s' d'))%type /\
    trace_ok tr.


  
Notation
  "<< u , o , s >> pre p << o' , s' , r >> post crash" :=
  (forall F, hoare_triple
          (fun (u:user) (o:oracle) (s: store) => F * pre)%pred
          p
          (fun (u:user) (o:oracle) (s: store) (o':oracle) (s': store) r => F * post)%pred
          (fun u (o:oracle) (s: store) o' s' => F * crash)%pred)
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level, o' at next level, s' at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' u ','  o ','  s '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' o' ','  s' ','  r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Notation
  "{{ e1 }} << u , o , s >> pre p << o' , s' , r >> post crash" :=
   (exists e1, (forall F, hoare_triple
          (fun (u:user) (o:oracle) (s: store) => F * pre)%pred
          p
          (fun (u:user) (o:oracle) (s: store) (o':oracle) (s': store) r => F * post)%pred
          (fun u (o:oracle) (s: store) o' s' => F * crash)%pred))
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level, o' at next level, s' at next level, r at next level, post at next level, crash at next level,
     format "'[v' '{{' e1 '}}' '//' '[  ' '<<' u ','  o ','  s '>>' '//' pre '//' p ']' '//' '[  ' '<<' o' ','  s' ','  r '>>' '//' post '//' crash ']' ']'").

Notation
  "{{ e1 e2 }} << u , o , s >> pre p << o' , s' , r >> post crash" :=
   (exists e1 e2, (forall F, hoare_triple
          (fun (u:user) (o:oracle) (s: store) => F * pre)%pred
          p
          (fun (u:user) (o:oracle) (s: store) (o':oracle) (s': store) r => F * post)%pred
          (fun u (o:oracle) (s: store) o' s' => F * crash)%pred))
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level, o' at next level, s' at next level, r at next level, post at next level, crash at next level,
     format  "'[v' '{{' e1 e2 '}}' '//' '[  ' '<<' u ','  o ','  s '>>' '//' pre '//' p ']' '//' '[  ' '<<' o' ','  s' ','  r '>>' '//' post '//' crash ']' ']'").


Notation
  "{{ e1 e2 e3 }} << u , o , s >> pre p << o' , s' , r >> post crash" :=
   (exists e1 e2 e3, (forall F, hoare_triple
          (fun (u:user) (o:oracle) (s: store) => F * pre)%pred
          p
          (fun (u:user) (o:oracle) (s: store) (o':oracle) (s': store) r => F * post)%pred
          (fun u (o:oracle) (s: store) o' s' => F * crash)%pred))
    (at level 10, u at next level, o at next level, s at next level, pre at next level, p at next level, o' at next level, s' at next level, r at next level, post at next level, crash at next level,
     format  "'[v' '{{' e1 e2 e3 '}}' '//' '[  ' '<<' u ','  o ','  s '>>' '//' pre '//' p ']' '//' '[  ' '<<' o' ','  s' ','  r '>>' '//' post '//' crash ']' ']'").


Theorem hoare_triple_strengthen_pre:
  forall T (p: prog T) (pre pre': precond) post crash,
  hoare_triple pre p post crash ->
  (forall  u o s, pre' u o s =p=>  pre u o s) ->
  hoare_triple pre' p post crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_post_weak:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall  u o d s o' s' r,
      pre u o s d ->
      post u o s o' s' r =p=>
      post' u o s o' s' r) ->
  hoare_triple pre p post' crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  split; eauto; destruct H3; eauto.
  cleanup.
  left; repeat eexists; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall  u o s o' s' (r: T),
      post u o s o' s' r =p=>
      post' u o s o' s' r) ->
  hoare_triple pre p post' crash.
Proof.
  intros; eapply hoare_triple_weaken_post_weak; eauto.
Qed.

Theorem hoare_triple_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall  u o d s o' s',
      pre u o s d ->
      crash u o s o' s' =p=>
      crash' u o s o' s') ->
  hoare_triple pre p post crash'.
Proof.
  unfold  hoare_triple; intros;
    edestruct H; intros; eauto.
  split; eauto; destruct H3; eauto.
  cleanup.
  right; repeat eexists; eauto.
  eapply H0; eauto.
Qed.


Theorem hoare_triple_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall  u o s o' s', crash u o s o' s' =p=> crash' u o s o' s') ->
  hoare_triple pre p post crash'.
Proof.
  intros; eapply hoare_triple_weaken_crash_weak; eauto.
Qed.


Theorem hoare_triple_pimpl_strong :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 pre2 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall r, hoare_triple pre2 (p2 r) post2 crash2) ->
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
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  inv_exec_perm.
  {
      edestruct H; eauto.
      destruct H8; cleanup.
      edestruct H0; eauto.
      destruct H8; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app; eauto.
    }
    {
      destruct H6.
      - edestruct H; eauto; destruct H7; cleanup.
        split; eauto; right; repeat eexists; eauto.
      - cleanup.
        edestruct H; eauto; destruct H8; cleanup.
        edestruct H0; eauto.
        destruct H8; eauto; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        apply trace_ok_app; eauto.
    }
Qed.

Theorem hoare_triple_pimpl' :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall r, hoare_triple (fun u o' s' => exists o s d, [[pre1 u o s d]] * post1 u o s o' s' r)%pred (p2 r) post2 crash2) ->
    (forall u o d s o' d' s' tr,
      pre1 u o s d ->
      exec u o d s p1 (Crashed _ o' d' s') tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
    (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      exec u o' d' s' (p2 r) (Finished o'' d'' s'' r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      exec u o' d' s' (p2 r) (Crashed _ o'' d'' s'') tr ->
      crash2 u o s o'' s'' d'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  inv_exec_perm.
  {
      edestruct H; eauto.
      destruct H7; cleanup.
      edestruct H0; eauto.
      pred_apply; cancel; eauto.
      destruct H7; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app; eauto.
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
        apply trace_ok_app; eauto.
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
      exec u o d s p1 (Crashed _ o' d' s') tr ->
      crash1 u o s o' s' d' ->
      crash2 u o s o' s' d') ->
    (forall  u o s o' d' s' o'' s'' d'' r r2 tr,
      post1 u o s o' s' r d' ->
      exec u o' d' s' (p2 r) (Finished o'' d'' s'' r2) tr ->
      post2 u o s o'' s'' r2 d'') ->
    (forall  u o s o' d' s' o'' s'' d'' r tr,
      post1 u o s o' s' r d' ->
      exec u o' d' s' (p2 r) (Crashed _ o'' d'' s'') tr ->
      crash2 u o s o'' s'' d'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  inv_exec_perm.
  {
      edestruct H; eauto.
      destruct H7; cleanup.
      edestruct H0; eauto.
      pred_apply; cancel; eauto.
      destruct H7; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      apply trace_ok_app; eauto.
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
        apply trace_ok_app; eauto.
    }
Qed.


Theorem hoare_triple_pimpl :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) pre1 post1 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall u o s d r,
          pre1 u o s d ->
          hoare_triple (fun u' o' s' => [[u = u']] * post1 u' o s o' s' r)%pred (p2 r) post2 crash2) ->
    (forall u o d s o' s',
      pre1 u o s d ->
      crash1 u o s o' s' =p=> crash2 u o s o' s') ->
    (forall  u o s d o' d' s' o'' s'' r r2,
      pre1 u o s d ->
      post1 u o s o' s' r d' ->
      post2 u o' s' o'' s'' r2 =p=> post2 u o s o'' s'' r2) ->
    (forall  u o s d o' d' s' o'' s'' r,
      pre1 u o s d ->
      post1 u o s o' s' r d' ->
      crash2 u o' s' o'' s'' =p=> crash2 u o s o'' s'') ->
    hoare_triple pre1 (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  inv_exec_perm.
  {
      edestruct H; eauto.
      destruct H7; cleanup.
      edestruct H0; eauto.
      pred_apply; cancel; eauto.
      destruct H7; eauto; cleanup; eauto.
      split. left.
      repeat eexists; eauto.
      eapply H2; eauto.
      apply trace_ok_app; eauto.
    }
    {
      destruct H5.
      - edestruct H; eauto; destruct H6; cleanup.
        split; eauto; right; repeat eexists; eauto.
        eapply H1; eauto.
      - cleanup.
        edestruct H; eauto; destruct H7; cleanup.
        edestruct H0; eauto.
        pred_apply; cancel; eauto.
        destruct H7; eauto; cleanup; eauto.
        split. right.
        repeat eexists; eauto.
        eapply H3; eauto.
        apply trace_ok_app; eauto.
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