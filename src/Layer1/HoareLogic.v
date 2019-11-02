Require Import Primitives Simulation Layer1.Definitions ProgAuto.

Module Layer1 <: Layer.
  Definition oracle := oracle.
  Definition data := set value.
  Definition prog := prog.
  Definition exec := exec.
  Definition oracle_ok := (fun T => @oracle_ok T).
End Layer1.

Module Layer1HL := HoareLogic Layer1.
Export Layer1.
Export Layer1HL.

Arguments exec {T}.

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
  unfold exec in *.
  eauto.
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
  unfold hoare_triple, exec; intros.
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
  unfold hoare_triple, exec; intros.
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