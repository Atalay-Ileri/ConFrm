Require Import Primitives Simulation Layer1.Definitions Layer1.Automation.

Module Layer1 <: Layer.
  Definition oracle := oracle.
  Definition data := set value.
  Definition aux_state := ((list key * encryptionmap) * hashmap)%type.
  Definition state := (aux_state * disk data)%type.
  Definition prog := prog.
  Definition exec := exec.
  Definition oracle_ok := (fun T => @oracle_ok T).
End Layer1.

Module Layer1HL := HoareLogic Layer1.
Export Layer1.
Export Layer1HL.

Arguments exec {T}.

Theorem hoare_triple_equivalence :
  forall T (p p': prog T) o d a pre post crash ap ac,
    hoare_triple pre p post crash ap ac o d a ->
    prog_equiv p p' ->
    hoare_triple pre p' post crash ap ac o d a.
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
  | [ |- hoare_triple _ (Bind (Bind _ _) _) _ _ _ _ _ _ _] =>
    eapply hoare_triple_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.


Theorem bind_ok:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 pre3 post3 crash3 o d a,
  (forall o1,
   (exists o2, o = o1++o2) ->      
   << o1, d, a >>
   (pre1 a)
   p1
  << r, ar >>
   (post1 r ar)
   (crash1 ar)) ->
  ( pre3 a =*=> pre1 a) ->
  (forall F r ar,
      (F * pre1 a)%pred d ->
      post1 r ar =*=> pre2 ar) ->
  (forall F d2 r1 ar1 r2 ar2,
      (F * pre1 a)%pred d ->
      (F * post1 r1 ar1)%pred d2 ->
      (F * pre2 ar1)%pred d2 ->
      post2 r2 ar2 =*=> post3 r2 ar2) ->
  (forall F ar,
      (F * pre1 a)%pred d ->
      crash1 ar =*=> crash3 ar) ->
  (forall F d2 r1 ar1 ar2,
      (F * pre1 a)%pred d ->
      (F * post1 r1 ar1)%pred d2 ->
      (F * pre2 ar1)%pred d2 ->
      crash2 ar2 =*=> crash3 ar2) ->
  (forall F o2 d2 r a2,
      (F * pre1 a)%pred d ->
      (F * post1 r a2)%pred d2 ->
      (exists o1, o = o1++o2) ->   
      << o2, d2, a2 >>
         (pre2 a2)
         (p2 r)
       << r, ar >>
       (post2 r ar)
       (crash2 ar)) ->
  << o, d, a >>
     (pre3 a)
     (Bind p1 p2)
  << r, ar >>
     (post3 r ar)
     (crash3 ar).
Proof.
  unfold hoare_triple, exec; intros.
  simpl in *; destruct_lifts; cleanup.
  (* rewrite H0 in H6. *)
  edestruct H; eauto.
  pred_apply' H6; cancel; eauto.
  eassign F; cancel; eauto.
  
  cleanup.
  split_ors; cleanup.
  - specialize H9 with (1:=H7).
    edestruct H5; eauto.
    pred_apply; cancel; eauto.
    pred_apply' H12; norm.
    cancel.
    eassign F; cancel.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    intuition eauto.
    destruct x2; simpl in *; eauto.

    cleanup.
    destruct x2; simpl in *.
    split_ors; cleanup;
      eexists; split; intuition eauto.

    left; do 2 eexists; intuition eauto.
    pred_apply; cancel; eauto.
    eapply H2; eauto.
    pred_apply; cancel; eauto.
    pred_apply' H12; cancel; eauto.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    
    right; eexists; intuition eauto.
    pred_apply; cancel; eauto.
    eapply H4; eauto.
    pred_apply; cancel; eauto.
    pred_apply' H12; cancel; eauto.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    
  - specialize H10 with (1:=H7); cleanup.
    rewrite app_nil_r.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H12; cancel.
    eapply H3.
    pred_apply; eassign F; cancel; eauto.
Qed.

Theorem bind_ok_aug:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 pre3 post3 crash3 augpost augcrash o d a,
  (forall o1,
   (exists o2, o = o1++o2) ->
   << o1, d, a >>
   (pre1 a)
   p1
  << r, ar >>
   (post1 r ar)
   (crash1 ar)) ->
  ( pre3 a =*=> pre1 a) ->
  (forall F r ar,
      (F * pre1 a)%pred d ->
      post1 r ar =*=> pre2 ar) ->
  (forall F d2 r1 ar1 r2 ar2,
      (F * pre1 a )%pred d ->
      (F * post1 r1 ar1)%pred d2 ->
      (F * pre2 ar1)%pred d2 ->
      post2 r2 ar2 =*=> post3 r2 ar2) ->
  (forall F ar,
      (F * pre1 a)%pred d ->
      crash1 ar =*=> crash3 ar) ->
  (forall F d2 r1 ar1 ar2,
      (F * pre1 a)%pred d ->
      (F * post1 r1 ar1)%pred d2 ->
      (F * pre2 ar1)%pred d2 ->
      crash2 ar2 =*=> crash3 ar2) ->
  (forall o1 o2 F d' r1,
      let a1 := fst d' in
      let d1 := snd d' in
      (F * pre1 a)%pred d ->
      exec o1 (a, d) p1 (Finished d' r1) ->
      (F * post1 r1 a1)%pred d1 ->
      (o = o1++o2) ->
      << o2, d1, a1 >>
         (pre2 a1)
         (p2 r1)
       << r, ar >>
       (post2 r ar)
       (crash2 ar)
       (augpost o a d r)
       (augcrash o a d)
       ) ->
  (forall F o1 d',
      (F * pre1 a)%pred d ->
      exec o1 (a, d) p1 (Crashed d') ->
      (F * crash1 (fst d'))%pred (snd d') ->
      (exists o2, o = o1++o2) ->
      (F * augcrash o a d)%pred (snd d')) ->
  << o, d, a >>
     (pre3 a)
     (Bind p1 p2)
  << r, ar >>
     (post3 r ar)
     (crash3 ar)
     (augpost o a d r)
     (augcrash o a d)
     .
Proof.
  unfold hoare_triple, exec; intros.
  simpl in *; destruct_lifts; cleanup.
  (* rewrite H0 in H7. *)
  edestruct H; eauto.
  pred_apply' H7; cancel; eauto.
  eassign F; cancel; eauto.  
  
  cleanup.
  split_ors; cleanup; destruct x2; simpl in *.
  - specialize H10 with (1:=H8).
    edestruct H5; eauto.
    pred_apply; cancel; eauto.
    pred_apply' H13; norm.
    eassign F; cancel.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    intuition eauto.

    cleanup.
    split_ors; cleanup;
      eexists; split; intuition eauto.

    left; do 2 eexists; intuition eauto.
    pred_apply' H16; cancel; eauto.
    eapply H2; eauto.    
    pred_apply; cancel; eauto.
    pred_apply' H13; norm. cancel.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    intuition.
    
    right; eexists; intuition eauto.
    pred_apply' H16; cancel; eauto.
    eapply H4; eauto.
    pred_apply; cancel; eauto.
    pred_apply' H13; norm. cancel.
    eapply H1.
    pred_apply; eassign F; cancel; eauto.
    intuition.
    
  - specialize H11 with (1:=H8); cleanup.
    rewrite app_nil_r in *.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H13; cancel.
    eapply H3; eauto.    
    pred_apply; eassign F; cancel; eauto.
    eapply H6; eauto.
    pred_apply; cancel; eauto.
    exists nil; rewrite app_nil_r; eauto.
Qed.