Require Import Primitives Simulation Layer1.Definitions ProgAuto.

Set Implicit Arguments.


(** ** Hoare logic *)
Definition precond := oracle -> @pred addr addr_dec (set value).
Definition postcond {T: Type} := T -> @pred addr addr_dec (set value).
Definition crashcond := @pred addr addr_dec (set value).
Definition augpostcond {T: Type} := oracle -> disk (set value) -> T -> @pred addr addr_dec (set value).
Definition augcrashcond := oracle -> disk (set value) -> @pred addr addr_dec (set value).

Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond) (augpost: augpostcond) (augcrash: augcrashcond):=
  fun o d =>
    pre o d ->
    (exists ret,
        exec o d p ret /\
        ((exists d' r,
             ret = Finished d' r
             /\ post r d' /\ augpost o d r d') \/
         (exists d',
             ret = Crashed d' /\ crash d' /\ augcrash o d d')))%type.


  
Notation
  "<< o , d >> pre p << r >> post crash" :=
  (forall F, hoare_triple
          (fun o d => (F * pre * [[ oracle_ok p o d ]]) d)%pred
          p%pred
          (fun r => F * post)%pred
          (F * crash)%pred
          (fun _ _ _ => any)
          (fun _ _ => any)
          o d)      
    (at level 10, o at next level, d at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o ','  d '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Notation
  "<< o , d >> pre p << r >> post crash augpost augcrash" :=
  (forall F, hoare_triple
          (fun o d => (F * pre * [[ oracle_ok p o d ]]) d)%pred
          p%pred
          (fun r => F * post)%pred
          (F * crash)%pred
          (fun o d r => F * augpost)%pred
          (fun o d => F * augcrash)%pred
          o d)      
    (at level 10, o at next level, d at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level, augpost at next level, augcrash at next level,
     format "'[v' '[  ' '<<' o ','  d '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r '>>' '//' '[' post ']' '//' '[' crash ']' '//' '[' augpost ']' '//' '[' augcrash ']' ']' ']'").

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

(*
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
         (forall o2 r, post1 r =p=> pre2 o2)) ->
      (forall o1 d r,
         pre1 o1 d ->
         (forall o2, post1 r =p=> pre2 o2) ->
          hoare_triple pre2 (p2 r) post2 crash2) ->
    (forall o d,
      pre1 o d ->
      crash1 =p=> crash2) ->
    hoare_triple pre (Bind p1 p2) post2 crash2.
Proof.
  unfold hoare_triple; intros.
  edestruct H0; eauto; cleanup.
  edestruct H; eauto; cleanup.
  specialize H1 with (1:=H7).
  specialize H3 with (1:=H7).
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
*)

Theorem hoare_triple_equivalence :
  forall T (p p': prog T) o d pre post crash ap ac,
    hoare_triple pre p post crash ap ac o d ->
    prog_equiv p p' ->
    hoare_triple pre p' post crash ap ac o d.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
Qed.

Theorem remember_oracle_ok :
  forall T (p: prog T) o d pre post crash ap ac,
    (oracle_ok p o d ->
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d)) ->
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d).
Proof.
  unfold hoare_triple; intros.
  eapply H; eauto.
  destruct_lift  H0; eauto.
Qed.

Ltac monad_simpl_one :=
  match goal with
  | [ |- hoare_triple _ (Bind (Bind _ _) _) _ _ ] =>
    eapply hoare_triple_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.

Theorem bind_ok:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 pre3 post3 crash3 o d,
  (forall o1,
   (exists o2, o = o1++o2) ->      
   << o1, d >>
   pre1
   p1
  << r >>
   (post1 r)
   crash1) ->
  ( pre3 =p=> pre1 ) ->
  (forall F r,
      (F * pre1)%pred d ->
      post1 r =p=> pre2) ->
  (forall F d2 r1 r2,
      (F * pre1)%pred d ->
      (F * post1 r1)%pred d2 ->
      (F * pre2)%pred d2 ->
      post2 r2 =p=> post3 r2) ->
  (forall F,
      (F * pre1)%pred d ->
      crash1 =p=> crash3) ->
  (forall F d2 r1,
      (F * pre1)%pred d ->
      (F * post1 r1)%pred d2 ->
      (F * pre2)%pred d2 ->
      crash2 =p=> crash3) ->
  (forall F o2 d2 r,
      (F * pre1)%pred d ->
      (F * post1 r)%pred d2 ->
      (exists o1, o = o1++o2) ->   
      << o2, d2 >>
         pre2
         (p2 r)
       << r >>
       (post2 r)
       crash2) ->
  << o, d >>
     pre3
     (Bind p1 p2)
  << r >>
     (post3 r)
     crash3.
Proof.
  unfold hoare_triple; intros.
  simpl in *; destruct_lifts; cleanup.
  rewrite H0 in H6.
  edestruct H; eauto.
  pred_apply' H6; cancel; eauto.
  
  cleanup.
  split_ors; cleanup.
  - specialize H9 with (1:=H7).
    edestruct H5; eauto.
    pred_apply' H12; norm.
    cancel.
    erewrite H1; eauto; cancel.
    intuition eauto.

    cleanup.
    split_ors; cleanup;
      eexists; split; intuition eauto.

    left; do 2 eexists; intuition eauto.
    pred_apply; cancel; eauto.
    eapply H2; eauto.
    erewrite <- H1; eauto.
    
    right; eexists; intuition eauto.
    pred_apply; cancel; eauto.
    eapply H4; eauto.
    erewrite <- H1; eauto.
  - specialize H10 with (1:=H7); cleanup.
    rewrite app_nil_r.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H12; cancel.
    eauto.
Qed.


Theorem crash_weaken:
  forall T (p: prog T) pre post crash1 crash2 o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash1 ->
  (crash1 =p=> crash2) ->
  << o, d >>
     pre
     p
  << r >>
     (post r)
     crash2.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  right; eexists; intuition eauto.
  clear H5; pred_apply; cancel; eauto.
Qed.


Theorem post_weaken:
  forall T (p: prog T) pre post1 post2 crash o d,
  << o, d >>
   pre
   p
  << r >>
   (post1 r)
   crash  ->
  (forall r, post1 r =p=> post2 r) ->
  << o, d >>
     pre
     p
  << r >>
     (post2 r)
     crash.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  clear H5; pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen:
  forall T (p: prog T) pre1 pre2 post crash o d,
  << o, d >>
   pre1
   p
  << r >>
   (post r)
   crash ->
  (pre2 =p=> pre1) ->
  << o, d >>
     pre2
     p
  << r >>
     (post r)
     crash.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen_aug:
  forall T (p: prog T) pre1 pre2 post crash ap ac o d,
  << o, d >>
   pre1
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d) ->
  (pre2 =p=> pre1) ->
  << o, d >>
     pre2
     p
  << r >>
     (post r)
     crash
     (ap o d r)
     (ac o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.


Theorem add_frame:
  forall T (p: prog T) pre post crash F o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash  ->
  << o, d >>
     (F * pre)
     p
  << r >>
     (F * post r)
     (F * crash).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply' H0; cancel; eauto.
  cleanup; split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  clear H4; pred_apply; cancel; eauto.
  right; eexists; intuition eauto.
  clear H4; pred_apply; cancel; eauto.
Qed.

Theorem extract_exists:
  forall T V (p: prog T) pre post crash o d,
    (forall (v:V),
  << o, d >>
   (pre v)
   p
  << r >>
   (post r)
   crash) ->
  << o, d >>
     (exists v, pre v)
     p
  << r >>
     (post r)
     crash.
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem extract_exists_aug:
  forall T V (p: prog T) pre post crash ap ac o d,
    (forall (v:V),
  << o, d >>
   (pre v)
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d)) ->
  << o, d >>
     (exists v, pre v)
     p
  << r >>
     (post r)
     crash
     (ap o d r)
     (ac o d).
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem remove_augcons:
  forall T (p: prog T) pre post crash (augpost: augpostcond) (augcrash: augcrashcond) o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash ->
  (forall F d' r,
      (F * pre)%pred d ->
      exec o d p (Finished d' r) ->
      (F * post r)%pred d' ->
      (F * augpost o d r)%pred d') ->
  (forall F d',
      (F * pre)%pred d ->
      exec o d p (Crashed d') ->
      (F * crash)%pred d' ->
      (F * augcrash o d)%pred d') ->
  << o, d >>
     pre
     p
  << r >>
     (post r)
     crash
     (augpost o d r)
     (augcrash o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  
  split_ors; cleanup.
  - 
    eexists; split; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eapply H0; eauto.
    pred_apply; cancel.
    
  - 
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    eapply H1; eauto.
    pred_apply; cancel.
Qed.


Theorem bind_ok_aug:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 pre3 post3 crash3 augpost augcrash o d,
  (forall o1,
   (exists o2, o = o1++o2) ->
   << o1, d >>
   pre1
   p1
  << r >>
   (post1 r)
   crash1) ->
  ( pre3 =p=> pre1 ) ->
  (forall F r,
      (F * pre1)%pred d ->
      post1 r =p=> pre2) ->
  (forall F d2 r1 r2,
      (F * pre1)%pred d ->
      (F * post1 r1)%pred d2 ->
      (F * pre2)%pred d2 ->
      post2 r2 =p=> post3 r2) ->
  (forall F,
      (F * pre1)%pred d ->
      crash1 =p=> crash3) ->
  (forall F d2 r1,
      (F * pre1)%pred d ->
      (F * post1 r1)%pred d2 ->
      (F * pre2)%pred d2 ->
      crash2 =p=> crash3) ->
  (forall o1 o2 F d1 r1,
      (F * pre1)%pred d ->
      exec o1 d p1 (Finished d1 r1) ->
      (F * post1 r1)%pred d1 ->
      (o = o1++o2) ->
      << o2, d1 >>
         pre2
         (p2 r1)
       << r >>
       (post2 r)
       crash2
       (augpost o d r)
       (augcrash o d)
       ) ->
  (forall F o1 d',
      (F * pre1)%pred d ->
      exec o1 d p1 (Crashed d') ->
      (F * crash1)%pred d' ->
      (exists o2, o = o1++o2) ->
      (F * augcrash o d)%pred d') ->
  << o, d >>
     pre3
     (Bind p1 p2)
  << r >>
     (post3 r)
     crash3
     (augpost o d r)
     (augcrash o d)
     .
Proof.
  unfold hoare_triple; intros.
  simpl in *; destruct_lifts; cleanup.
  rewrite H0 in H7.
  edestruct H; eauto.
  pred_apply' H7; cancel; eauto.
  
  cleanup.
  split_ors; cleanup.
  - specialize H10 with (1:=H8).
    edestruct H5; eauto.
    pred_apply' H13; norm.
    cancel.
    erewrite H1; eauto; cancel.
    intuition eauto.

    cleanup.
    split_ors; cleanup;
      eexists; split; intuition eauto.

    left; do 2 eexists; intuition eauto.
    pred_apply' H16; cancel; eauto.
    eapply H2; eauto.
    erewrite <- H1; eauto.
    
    right; eexists; intuition eauto.
    pred_apply' H16; cancel; eauto.
    eapply H4; eauto.
    erewrite <- H1; eauto.
  - specialize H11 with (1:=H8); cleanup.
    rewrite app_nil_r in *.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H13; cancel.
    eauto.
    eapply H6; eauto.
    exists nil; rewrite app_nil_r; eauto.
Qed.