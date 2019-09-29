Require Import Primitives Layer1 BlockAllocator.
Require Import Layer2 SimulationLayer.
Require Import FunctionalExtensionality Omega.

Section Layer1to2Refinement.
  
  Fixpoint compile {T} (p1: Layer2.prog T) : Layer1.prog T :=
    match p1 with
    | Read a => read a
    | Write a v => write a v
    | Alloc v => alloc v
    | Free a => free a
    | Ret v => Layer1.Ret v
    | Bind px py => Layer1.Bind (compile px) (fun x => compile (py x))
    end.
  
  Fixpoint oracle_matches T (d1: Layer1.state) (p: Layer2.prog T)  (o1: oracle Layer1.token) (o2: oracle Layer2.token) :=
    match p with
    | Alloc v =>
      forall d1',
        (Layer1.exec o1 d1 (compile (Alloc v)) (Crashed d1') ->
         o2 = [Crash]) /\
        (forall r, Layer1.exec o1 d1 (compile (Alloc v)) (Finished d1' r) ->
         match r with
         | Some a =>
           o2 = [BlockNum a]
         | None =>
           o2 = [DiskFull]
         end)
    | @Bind T1 T2 p1 p2 =>
       forall d1',
        (Layer1.exec o1 d1 (compile p1) (Crashed d1') ->
         oracle_matches T1 d1 p1 o1 o2) /\
        (forall r o1' o1'' o2' o2'',
           o1 = o1'++o1'' ->
           o2 = o2'++o2'' ->
           Layer1.exec o1' d1 (compile p1) (Finished d1' r) ->
           oracle_matches T1 d1 p1 o1' o2' /\
           oracle_matches T2 d1' (p2 r) o1'' o2'')
    | _ =>
      forall d1',
        (Layer1.exec o1 d1 (compile p) (Crashed d1') ->
         o2 = [Crash]) /\
        (forall r, Layer1.exec o1 d1 (compile p) (Finished d1' r) ->
         o2 = [Cont])
    end.

  Definition refines_to d1 d2 :=
    rep d2 d1.

  Definition compiles_to T p2 p1 :=
    p1 = @compile T p2.

  Definition low := Build_LTS Layer1.token Layer1.state Layer1.prog Layer1.exec.

  Definition high := Build_LTS Layer2.token Layer2.state Layer2.prog Layer2.exec.

  Lemma rep_eq:
    forall d s1 s2,
      rep s1 d ->
      rep s2 d ->
      s1 = s2.
  Proof.
    intros.
    extensionality k.
    unfold rep in *.
    destruct_lift H. destruct_lift H0.
    eapply_fresh ptsto_valid in H.
    eapply_fresh ptsto_valid in H0; cleanup.
    destruct_fresh (nth k (bits (value_to_bits dummy2)) 0).
    rewrite H4, H6; eauto.
    destruct (value_to_bits dummy2); simpl in *.
    unfold valid_bitlist in *; cleanup.
    destruct (nth_in_or_default k bits 0); [|cleanup; omega].
    apply H2 in i; cleanup.
    destruct n; cleanup; try omega.
    specialize (H3 _ D).
    specialize (H5 _ D); cleanup; eauto.
  Qed.
  
  Theorem sbs :
    forall valid_h valid_op_h,
    StrongBisimulation low high
                       (refines_to_valid refines_to valid_h)
                       (compiles_to_valid valid_op_h compiles_to)
                       valid_h
                       valid_op_h
                       compiles_to refines_to
                       oracle_matches.
  Proof.
    unfold refines_to_valid, refines_to,
    compiles_to_valid, compiles_to, oracle_matches; intros.
    constructor.
    intros T p1 p2.
    generalize dependent p1.
    induction p2; intros.
    - (* Read *)
      simpl in *; cleanup.
      split.
      + (* Low to High *)
        intros.
        eapply_fresh read_ok in H0.
        2: instantiate (2:= emp); pred_apply; cancel.
        split_ors; cleanup.
        * (* Finished *)
          destruct_lifts.
          specialize (H5 x0); cleanup.
          eexists.
          split.
          econstructor; eauto.
          simpl in *.
          repeat split; eauto.
          intuition (cleanup; eauto).
          unfold rep in *.
          destruct_lift H7.
          erewrite H13; eauto; simpl.
          apply nth_overflow; simpl.
          destruct (value_to_bits dummy); simpl.
          unfold valid_bitlist in *; cleanup; eauto.
          intros.
          erewrite rep_eq; eauto.

        * (* Crashed *)
          destruct_lifts.
          specialize (H5 x0); cleanup.
          eexists.
          split.
          eapply ExecOpCrash; eauto.
          intros; intuition.
          inversion H9.
          simpl in *.
          repeat split; eauto.
          intuition (cleanup; eauto).
          erewrite rep_eq; eauto.

      + (*High to low*)
        intros.
        inversion H0; sigT_eq.
        (* Total correctness needed 
           to show that such execution exists *)
  Abort.

End Layer1to2Refinement.