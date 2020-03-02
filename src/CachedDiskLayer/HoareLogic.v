(*
Require Import String.
Require Import Primitives Simulation.
Require Import DiskLayer CacheLayer.
Require Import CachedDiskLayer.Definitions CachedDiskLayer.Automation.

(* TODO: I need a more general Hoare Logic framework here *)
Module CachedDiskLayer <: Layer.
  Definition oracle := oracle.
  Definition data := value.
  Definition aux_state := unit.
  Definition state := (aux_state * (DiskLayer.state * CacheLayer.state))%type.
  Definition prog := prog.
  Definition exec := exec.
  Definition oracle_ok := (fun T => @oracle_ok T).
End CachedDiskLayer.

Module CacheLayerHL := HoareLogic CacheLayer.
Export CacheLayer.
Export CacheLayerHL.

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
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 o d a, 
   (forall o1 o2,
    Marker "bind_ok spec for" p1 ->
    o = o1++o2 ->
   << o1, d, a >>
   (pre1 o1 a)
   p1
  << r, ar >>
   (post1 r ar)
   (crash1 ar)) ->
  (forall o1 o2,
     o = o1++o2 ->
     pre1 o a =*=> pre1 o1 a) ->
  (forall F r ar o1 o2,
     Marker "bind_ok post1 =*=> pre2 for" (Bind p1 p2) ->
     o = o1++o2 ->
      (F * pre1 o1 a)%pred d ->
      post1 r ar =*=> pre2 o2 ar) ->
  (forall F ar o1 o2,
     Marker "bind_ok crash1 =*=> crash2 for" (Bind p1 p2) ->
     o = o1++o2 ->
      (F * pre1 o1 a)%pred d ->
      crash1 ar =*=> crash2 ar) ->

  (forall F d2 r a2 o1 o2,
     Marker "bind_ok after" p1 ->
     o = o1++o2 ->
      (F * pre1 o1 a)%pred d ->
      (F * post1 r a2)%pred d2 ->  
      << o2, d2, a2 >>
         (pre2 o2 a2)
         (p2 r)
       << r, ar >>
       (post2 r ar)
       (crash2 ar)) ->
  << o, d, a >>
     (pre1 o a)
     (Bind p1 p2)
  << r, ar >>
     (post2 r ar)
     (crash2 ar).
Proof.
  unfold Marker, hoare_triple, exec; intros.
  simpl in *; destruct_lifts; cleanup.
  (* rewrite H0 in H6. *)
  edestruct H; eauto.
  pred_apply' H4; cancel; eauto.
  eassign F; cancel; eauto.
  
  cleanup.
  split_ors; cleanup.
  - specialize H7 with (1:=H5).
    edestruct H3; eauto.
    pred_apply' H4; cancel; eauto.
    clear H11.
    pred_apply; cancel; eauto.
    eassign F; cancel.
    eapply H1; eauto.
    pred_apply' H4; cancel; eauto.
    eassign F; cancel; eauto.
      
    destruct x2; simpl in *; eauto.

    cleanup.
    destruct x2; simpl in *.
    split_ors; cleanup;
      eexists; split; intuition eauto.
    
  - specialize H8 with (1:=H5); cleanup.
    rewrite app_nil_r.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H10; cancel.
    eapply H2; eauto.
    pred_apply' H4; cancel; eauto.
    eassign F; cancel; eauto.  
Qed.

Theorem bind_ok_aug:
  forall T T' (p1: prog T) (p2: T -> prog T') pre1 post1 crash1 pre2 post2 crash2 augpost augcrash o d a,
    (forall o1,
   Marker "bind_ok_aug spec for" p1 ->  
   (exists o2, o = o1++o2) ->
   << o1, d, a >>
   (pre1 a)
   p1
  << r, ar >>
   (post1 r ar)
   (crash1 ar)) ->
  (forall F r ar,
     Marker "bind_ok_aug post1 =*=> pre2 for" (Bind p1 p2) ->
      (F * pre1 a)%pred d ->
      post1 r ar =*=> pre2 ar) ->
  (forall F ar,
     Marker "bind_ok_aug crash1 =*=> crash2 for" (Bind p1 p2) ->
      (F * pre1 a)%pred d ->
      crash1 ar =*=> crash2 ar) ->
  (forall o1 o2 F d' r1,
      let a1 := fst d' in
      let d1 := snd d' in
      Marker "bind_ok_aug after" p1 ->
      (F * pre1 a)%pred d ->
      exec o1 (a, d) p1 (Finished d' r1) ->
      (F * post1 r1 a1)%pred d1 ->
      (exists o1, o = o1++o2) ->
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
     Marker "bind_ok_aug crash1 =*=> augcrash for" (Bind p1 p2) ->
      (F * pre1 a)%pred d ->
      exec o1 (a, d) p1 (Crashed d') ->
      (exists o2, o = o1++o2) ->
      crash1 (fst d') =*=> augcrash o a d) ->
  << o, d, a >>
     (pre1 a)
     (Bind p1 p2)
  << r, ar >>
     (post2 r ar)
     (crash2 ar)
     (augpost o a d r)
     (augcrash o a d)
     .
Proof.
  unfold Marker, hoare_triple, exec; intros.
  simpl in *; destruct_lifts; cleanup.
  (* rewrite H0 in H7. *)
  edestruct H; eauto.
  pred_apply' H4; cancel; eauto.
  
  cleanup.
  split_ors; cleanup; destruct x2; simpl in *.
  - specialize H7 with (1:=H5).
    edestruct H2; eauto.
    simpl; pred_apply' H10; norm.
    eassign F; cancel.
    eapply H0; eauto.
    intuition eauto.

    cleanup.
    split_ors; cleanup;
      eexists; split; intuition eauto.
    
  - specialize H8 with (1:=H5); cleanup.
    rewrite app_nil_r in *.
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    pred_apply' H10; cancel.
    eapply H1; eauto.    
    simpl; pred_apply' H10; cancel; eauto.
    specialize (H3 F x (a0, d0)); simpl in *.
    eapply H3; eauto.
    exists nil; rewrite app_nil_r; eauto.
Qed.

Global Opaque Marker.

Create HintDb specs.



Local Ltac ret_step :=
  eapply post_impl;
    [eapply crash_impl;
     [eapply pre_impl;
      [eapply add_frame;
       eauto with specs
      |]
     |]
    |];
    try solve [crush_pimpl].

Local Ltac bind_step :=
  eapply bind_ok;
  [ intros;
    eapply pre_impl;
    [ eapply add_frame;
      eauto with specs
    |]
  | | | | ];
  try solve [simpl; crush_pimpl].

Ltac step :=
  intros;
  match goal with
  | [ |- hoare_triple _ ?p _ _ _ _ _ _ _ ] => 
    simpl p
  end;
  match goal with
  | [ |- hoare_triple _ (Ret _) _ _ _ _ _ _ _ ] => 
    ret_step
  | [ |- hoare_triple _ (Bind _ _) _ _ (fun _ _ _ _ => any) (fun _ _ _ => any) _ _ _ ] => 
    bind_step
  | [ |- hoare_triple _ (Bind _ _) _ _ _ _ _ _ _ ] => 
    bind_step
  end.
*)