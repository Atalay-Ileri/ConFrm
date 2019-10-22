Require Import List BaseTypes Layer1 ProgAuto CommonAutomation.
Require Import Disk Memx Predx SepAuto Simulation.
Import ListNotations.

Set Implicit Arguments.


(** ** Hoare logic *)
Definition precond := oracle -> @pred addr addr_dec (set value).
Definition postcond {T: Type} := oracle -> disk (set value) -> T -> @pred addr addr_dec (set value).
Definition crashcond := oracle -> disk (set value) -> @pred addr addr_dec (set value).


Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond):=
  forall o d,
    pre o d ->
    (exists ret,
        exec o d p ret /\
        ((exists d' r,
             ret = Finished d' r
             /\ post o d r d') \/
         (exists d',
             ret = Crashed d' /\ crash o d d')))%type.


  
Notation
  "<< o >> pre p << d , r >> post crash" :=
  (forall F, hoare_triple
          (fun o d => (F * pre * [[ oracle_ok p o d ]]) d)%pred
          p%pred
          (fun o d r => F * post)%pred
          (fun o d => F * crash)%pred)
    (at level 10, o at next level, d at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' d ',' r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

(*
Notation
  "{{ e1 }} << o >> pre p << r >> post crash" :=
   (exists e1, (forall F, hoare_triple
          (fun o => F * pre)%pred
          p
          (fun r => F * post)%pred
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
  (forall  o d r,
      pre o d ->
      post o d r =p=>
      post' o d r) ->
  hoare_triple pre p post' crash.
Proof.
  unfold hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup; split_ors; cleanup.
  eexists; split; eauto.  
  left; repeat eexists; eauto.
  eapply H0; eauto.
  eexists; split; eauto.
Qed.


Theorem hoare_triple_weaken_post_strong:
  forall T (p: prog T) pre (post post': postcond) crash,
  hoare_triple pre p post crash ->
  (forall o d (r: T),
      post o d r =p=>
      post' o d r) ->
  hoare_triple pre p post' crash.
Proof.
  intros; eapply hoare_triple_weaken_post_weak; eauto.
Qed.

Theorem hoare_triple_weaken_crash_weak:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall o d,
      pre o d ->
      crash o d =p=>
      crash' o d) ->
  hoare_triple pre p post crash'.
Proof.
  unfold  hoare_triple; intros;
    edestruct H; intros; eauto.
  cleanup; split_ors; cleanup.
  eexists; split; eauto.
  eexists; split; eauto.  
  right; repeat eexists; eauto.
  eapply H0; eauto. 
Qed.


Theorem hoare_triple_weaken_crash_strong:
  forall T (p: prog T) pre post (crash crash': crashcond),
  hoare_triple pre p post crash ->
  (forall o d, crash o d =p=> crash' o d) ->
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


Theorem hoare_triple_pimpl :
    forall T1 T2 (p1: prog T1) (p2: T1 -> prog T2) (pre: precond) pre1 post1 pre2 post2 crash1 crash2,
      hoare_triple pre1 p1 post1 crash1 ->
      (forall o d,
          pre o d ->
          exists o1 o2,
            o = o1++o2 /\
            (o2 = [] \/ ~In Crash o1) /\
            pre1 o1 d) ->
      (forall o1 d,
         pre1 o1 d ->
         (forall o2 r, post1 o1 d r =p=> pre2 o2)) ->
      (forall o1 d r,
         pre1 o1 d ->
         (forall o2, post1 o1 d r =p=> pre2 o2) ->
          hoare_triple pre2 (p2 r) post2 crash2) ->
    (forall o d,
      pre1 o d ->
      crash1 o d =p=> crash2 o d) ->
    (forall o1 o2 d1 d2 r1 r2,
        pre1 o1 d1 ->
        post1 o1 d1 r1 d2 ->
        pre2 o2 d2 ->
        post2 o2 d2 r2  =p=> post2 (o1++o2) d1 r2) ->
    (forall o1 o2 d1 d2 r1,
        pre1 o1 d1 ->
        post1 o1 d1 r1 d2 ->
        pre2 o2 d2 ->
        crash2 o2 d2  =p=> crash2 (o1++o2) d1) ->
    hoare_triple pre (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  edestruct H0; eauto; cleanup.
  edestruct H; eauto; cleanup.
  specialize H1 with (1:=H9).
  specialize H3 with (1:=H9).
  split_ors.
  - (* p1 Finished *)    
    edestruct H2; eauto.
    eapply H1; eauto.
    cleanup.
    split_ors; cleanup.
    + (* p2 Finished *)
      clear H8.
      eexists; split; eauto.
      left; do 2 eexists; intuition eauto.
      eapply H4; eauto.
      eapply H1; eauto.
    + (* p2 Crashed *)
      clear H8.
      eexists. intuition eauto.
      right; eexists; intuition eauto.
      eapply H5; eauto.
      eapply H1; eauto.
  - (* p1 Crashed *)
    split_ors; cleanup.
    eexists. intuition eauto.
    cleanup; rewrite app_nil_r;
      econstructor; eauto.
    cleanup; rewrite app_nil_r; eauto.
    apply exec_crash_in in H7; intuition.   
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

Theorem bind_ok:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 crash3,
  << o >>
   (pre1 o)
   p1
  << d, r >>
   (post1 o d r)
   (crash1 o d) ->
  (forall o o',
      pre1 (o++o') =p=> pre1 o ) ->
  (forall F o o' d r,
      (F * pre1 o)%pred d ->
      post1 o d r =p=> pre2 o') ->
  (forall F o d d' r,
      (F * pre1 o)%pred d ->
      (F * post1 o d r)%pred d' ->
      << o >>
         (pre2 o)
         (p2 r)
       << d, r >>
       (post2 o d r)
       (crash2 o d)) ->
  (forall F d1 d2 r1 r2 o1 o2,
      (F * pre1 o1)%pred d1 ->
      (F * post1 o1 d1 r1)%pred d2 ->
      (F * pre2 o2)%pred d2 ->
      post2 o2 d2 r2 =p=> post2 (o1++o2) d1 r2) ->
  (forall F o d,
      (F * pre1 o)%pred d ->
      crash1 o d =p=> crash3 o d) ->
  (forall F d1 d2 r1 o1 o2,
      (F * pre1 o1)%pred d1 ->
      (F * post1 o1 d1 r1)%pred d2 ->
      (F * pre2 o2)%pred d2 ->
      crash2 o2 d2 =p=> crash3 (o1++o2) d1) ->
  << o >>
     (pre1 o)
     (Bind p1 p2)
  << d, r >>
     (post2 o d r)
     (crash3 o d).
Proof.
  unfold hoare_triple; intros.
  simpl in *; destruct_lifts; cleanup.
  rewrite H0 in H6.
  edestruct H; eauto.
  pred_apply' H6; cancel; eauto.
  apply sep_star_comm.
  
  cleanup.
  split_ors; cleanup.
  - specialize H9 with (1:=H7).
    edestruct H2; eauto.
    pred_apply' H12; norm.
    cancel.
    rewrite H1;
      intuition eauto.
    cancel; eauto.
    intuition eauto.

    cleanup.
    split_ors; cleanup;
    eexists; split; intuition eauto.
    left; do 2 eexists; intuition eauto.
    pred_apply; cancel.
    eapply H3; eauto.
    erewrite <- H1; eauto.
    
    right; eexists; intuition eauto.
    pred_apply; cancel.
    eapply H5; eauto.
    erewrite <- H1; eauto.
  - specialize H10 with (1:=H7); cleanup.
    rewrite app_nil_r.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply; cancel.
    eauto.
Qed.


Theorem crash_weaken:
  forall T (p: prog T) pre post crash1 crash2,
  << o >>
   (pre o)
   p
  << d, r >>
   (post r)
   (crash1 o d) ->
  (forall o d, crash1 o d =p=> crash2 o d) ->
  << o >>
     (pre o)
     p
  << d, r >>
     (post r)
     (crash2 o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  right; eexists; intuition eauto.
  pred_apply; cancel; eauto.
Qed.


Theorem post_weaken:
  forall T (p: prog T) pre post1 post2 crash,
  << o >>
   (pre o)
   p
  << d, r >>
   (post1 r)
   (crash o d)  ->
  (forall r, post1 r =p=> post2 r) ->
  << o >>
     (pre o)
     p
  << d, r >>
     (post2 r)
     (crash o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen:
  forall T (p: prog T) pre1 pre2 post crash,
  << o >>
   (pre1 o)
   p
  << d, r >>
   (post r)
   (crash o d) ->
  (forall o, pre2 o =p=> pre1 o) ->
  << o >>
     (pre2 o)
     p
  << d, r >>
     (post r)
     (crash o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem add_frame:
  forall T (p: prog T) pre post crash F,
  << o >>
   (pre o)
   p
  << d, r >>
   (post r)
   (crash o d) ->
  << o >>
     (F * pre o)
     p
  << d, r >>
     (F * post r)
     (F * crash o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply' H0; cancel; eauto.
  rewrite sep_star_assoc; cancel.
  cleanup; split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  pred_apply; cancel; eauto.
  right; eexists; intuition eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem extract_exists:
  forall T V (p: prog T) pre post crash,
  (forall (v:V), << o >>
   (pre o v)
   p
  << d, r >>
   (post r)
   (crash o d)) ->
  << o >>
     (exists v, pre o v)
     p
  << d, r >>
     (post r)
     (crash o d).
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.