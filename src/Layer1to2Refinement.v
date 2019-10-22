Require Import Primitives Layer1 BlockAllocator ListUtils.
Require Import Layer2 SimulationLayer Layer1to2RefinementDefinitions.
Require Import FunctionalExtensionality Omega.

Section Layer1to2Refinement.

  
  Axiom oracle_refines_to_deterministic:
    forall T (p: Layer2.prog T) s o o1 o2,
      oracle_refines_to T s p o o1 ->
      oracle_refines_to T s p o o2 ->
      o1 = o2.
  
  Axiom layer1_exec_compiled_preserves_refines_to:
    forall T (p2: Layer2.prog T) o1 s1 s1',
      Layer1.exec o1 s1 (compile p2) s1' ->
      (exists s2, refines_to s1 s2) ->
      (exists s2', refines_to (extract_state s1') s2').
  
  Hint Resolve oracle_ok_nonempty.
  
  (*
  Lemma oracle_refinement_deterministic:
    forall T p2 ol1 ol2 oh sl1 sl2 p1 sl1' sl2', (* sh1 sh2 sh1' sh2' ,
      refines_to sl1 sh1 ->
      refines_to sl2 sh2 ->
      *)
      compilation_of T p1 p2 ->
      Layer1.exec ol1 sl1 p1 sl1' ->
      Layer1.exec ol2 sl2 p1 sl2' ->
      result_same sl1' sl2' ->
      (forall def, extract_ret def sl1' = extract_ret def sl2') ->
      (*
      Layer2.exec oh sh1 p2 sh1' ->
      Layer2.exec oh sh2 p2 sh2' ->
      result_same sl1' sh1' ->
      result_same sl2' sh2' ->
      result_same sh1' sh2' ->
                                *)
      oracle_refines_to T sl1 p2 ol1 oh ->
      oracle_refines_to T sl2 p2 ol2 oh ->
      ol1 = ol2.
  Proof.
    unfold compilation_of; induction p2; simpl; intros.
    - (* Read *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Write *)
        cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Alloc *)
      destruct (in_dec token_dec Layer1.Crash ol1), (in_dec token_dec Layer1.Crash ol2);
        try solve [cleanup; tauto].
      cleanup.
      + (* Crashed *)
        admit.
      + destruct H4, H5.
        clear H0 H1 H6 H7; cleanup.
        clear H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t; try tauto.
        erewrite H1; eauto.
    - (* Free *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Ret *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t0; try tauto.
        erewrite H1; eauto.
    - (* Bind *)
      cleanup.
      invert_exec; invert_exec; try tauto.
      + (* Both Finished *)
        specialize (H8 x1).
        specialize (H7 x5).
        cleanup.
        edestruct H10; eauto; cleanup.
        edestruct H11; eauto; cleanup.
        specialize IHp2 with (2:= H0)(3:=H2); simpl in *.
        edestruct IHp2; eauto.
        specialize H with (2:= H1)(3:=H9); simpl in *.
        
      destruct oh; simpl in *.
        cleanup; try tauto.
        unfold refines_to in *; cleanup.
        eapply read_ok in H; cleanup.
        split_ors; destruct_lifts; cleanup.
        edestruct H4.
        
        split_ors; cleanup.
        
        edestruct read_ok.
        pred_apply' H; cancel.
        eassign
   *)

  Arguments oracle_ok T p o s : simpl never.
  Arguments oracle_refines_to T d1 p o1 o2 : simpl never.
  
  Lemma Axiom1:
    forall T p2 p1 ol sl sl',
      (exists sh, refines_to sl sh) ->
      oracle_ok p1 ol sl ->
      Layer1.exec ol sl p1 sl' ->
      compilation_of T p1 p2 ->
      exists oh, oracle_refines_to T sl p2 ol oh.
  Proof.
    unfold refines_to, compilation_of;
    induction p2; simpl; intros; cleanup.

    - (* Read *)
      edestruct read_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
      cleanup; destruct_lifts; eauto.
    - (* Write *)
      edestruct write_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; eauto.
      split_ors; cleanup; eauto.
        
    - (* Alloc *)
      edestruct alloc_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; 
          split_ors; cleanup; eauto.
    - (* Free *)
      edestruct free_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; eauto;
          split_ors; cleanup; eauto.
    - (* Ret *)
      destruct sl';
      unfold oracle_refines_to; simpl;
        destruct (in_dec token_dec Crash ol); eauto.
    - (* Bind *)
      invert_exec; cleanup.      
      + (* Finished *)
        eapply_fresh oracle_ok_bind_finished_split in H1; eauto; cleanup.
        edestruct IHp2; eauto.
        (* intros d Hx; inversion Hx. *)
        edestruct layer1_exec_compiled_preserves_refines_to; try apply H2; eauto.
        unfold refines_to; eauto.
        edestruct H; eauto; simpl in *.
        exists (x5++x7).
        unfold oracle_refines_to; simpl; fold oracle_refines_to.
        split; eauto.
        
        do 2 eexists; intuition eauto.
        match goal with
        | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
          eapply_fresh oracle_ok_exec_crashed_app_nil in H;
          eauto; cleanup
        end.
        exfalso; eapply oracle_ok_nonempty; eauto.
        match goal with
        | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
          eapply_fresh oracle_ok_exec_crashed_app_nil in H;
          eauto; cleanup
        end.
        repeat match goal with
        | [H: Layer1.exec _ _ _ (Finished _ _),
           H0: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
          eapply deterministic_prog in H;
          try apply H0; eauto; cleanup
        end.
        
        do 2 eexists; intuition eauto.
        
      + (* Crashed *)
        split_ors; cleanup.
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_crashed_split in H;
          eauto; cleanup
          end.
          
          edestruct IHp2; eauto.
          (* intros d Ha; inversion Ha. *)
          exists x1.
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split.
          unfold oracle_ok; simpl;
          fold (@oracle_ok T); fold (@oracle_ok T').

          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Crashed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Crashed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
        
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_finished_split in H;
          eauto; cleanup
          end.
          edestruct IHp2; eauto.
          (* intros d Hx; inversion Hx. *)
          
          edestruct H;
          try match goal with
          | [H: oracle_ok (compile (_ _)) _ _ |- _ ] =>
            apply H
          end; eauto; simpl in *.

          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply layer1_exec_compiled_preserves_refines_to in H;
            eauto; cleanup
          end.
          unfold refines_to; eauto.
          
          exists (x5++x6).
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split; eauto.

          do 2 eexists; intuition eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          exfalso; eapply oracle_ok_nonempty; eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _),
             H0: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply deterministic_prog in H;
            try apply H0; eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
    
  Qed.

  Theorem sbs_read :
    forall a,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of
        refines_to
        oracle_refines_to
        (Read a).              
  Proof.
    constructor; intros.
    
    unfold refines_to,
    compiles_to_valid, compilation_of in *; intros.
    simpl in *;
      split.
    
    + (* Low to High *)
      intros; cleanup.
      edestruct (read_ok a); eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *; cleanup;
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
      
      * (* Finished *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
        intuition (cleanup; eauto).
        unfold rep in *.
        destruct_lifts.          
        symmetry; eauto.
  
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct (read_ok a); cleanup.
      pred_apply' H; norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
        
      split_ors; cleanup;
      destruct_lifts;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end.
      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
        intuition (cleanup; eauto).
        unfold rep in *.
        destruct_lifts;          
        symmetry; eauto.
          
      * (* Crashed *)
          eexists; split.
          eauto.
          simpl in *.
          repeat split; eauto.
  Qed.

  Theorem sbs_write :
    forall a v,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to
        (Write a v).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct write_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished 1 *)
        eexists; split.
        eapply ExecWriteFail; eauto.
        simpl in *.
        repeat split; eauto.

      * (* Finished 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct write_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Finished 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
Qed.

  Theorem sbs_free :
    forall a,
    StrongBisimulationForProgram
      layer1_lts layer2_lts
      compilation_of refines_to
      oracle_refines_to
      (Free a).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct free_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct free_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
  Qed.
 

  Theorem sbs_ret :
    forall T (v: T),
    StrongBisimulationForProgram
      layer1_lts layer2_lts
      compilation_of refines_to
      oracle_refines_to
      (Ret v).              
  Proof.
        constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      invert_exec; cleanup;
      unfold oracle_refines_to in *;
      cleanup; simpl in *;
      try split_ors; intuition; try congruence.

      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
          
    + (*High to low*)
      intros; cleanup.
      
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence;
      unfold oracle_refines_to, oracle_ok in *;
      cleanup; simpl in *;
      repeat (split_ors; cleanup; simpl in *);
      intuition; try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        intros; congruence.
        simpl in *.
        repeat split; eauto.
  Qed.

   Theorem sbs_alloc :
     forall v,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to
        (Alloc v).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct alloc_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct alloc_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
  Qed.

  Theorem sbs_bind:
    forall T1 T2 (p1: Layer2.prog T1) (p2: T1 -> Layer2.prog T2),
      StrongBisimulationForProgram layer1_lts layer2_lts
          compilation_of refines_to oracle_refines_to p1 ->
    (forall t,
      StrongBisimulationForProgram layer1_lts layer2_lts
        compilation_of refines_to oracle_refines_to 
        (p2 t)) ->
    StrongBisimulationForProgram layer1_lts layer2_lts
          compilation_of refines_to oracle_refines_to (Layer2.Bind p1 p2).
  Proof.
    intros.
    edestruct H.
    constructor; intros.
    unfold compilation_of, oracle_refines_to in *;
    simpl in *; cleanup;
    fold oracle_refines_to in *.
    unfold oracle_ok in *; simpl in *; cleanup.
    fold (@oracle_ok T1) in *; fold (@oracle_ok T2) in *.

    split; intros.
    - (* Low to High *)
      invert_exec; cleanup; intuition.
      eapply_fresh oracle_ok_finished_eq in H9; eauto; cleanup.
      (* Oct 18: Fix oracle_refines_to definition for Bind *)
  Admitted.
    
  Hint Resolve sbs_alloc sbs_free sbs_read sbs_ret sbs_write sbs_bind.
  
  Theorem sbs :
      StrongBisimulation
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to.              
  Proof.
    apply bisimulation_restrict_prog.
    induction p; eauto.
  Qed.

  Hint Resolve sbs.

  Theorem sbs_general:
    forall valid_state_h valid_prog_h,
      exec_compiled_preserves_validity layer1_lts layer2_lts
    compilation_of (refines_to_valid refines_to valid_state_h) ->
    exec_preserves_validity layer2_lts valid_state_h ->
      StrongBisimulationForValidStates
        layer1_lts layer2_lts
        (refines_to_valid refines_to valid_state_h)
        (compiles_to_valid valid_prog_h compilation_of)
        valid_state_h
        valid_prog_h
        compilation_of refines_to
        oracle_refines_to.  
  Proof.
    intros.
    eapply bisimulation_restrict_state; eauto.
  Qed.
    
End Layer1to2Refinement.