Require Import Framework CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LoggedDisk.Definitions.
Require Import FunctionalExtensionality Omega.

Section Layer1to2Refinement.

  Opaque read write.
  
  Lemma oracle_refines_to_deterministic:
    forall T (p: LoggedDiskHL.Lang.prog T) s s' o o1 o2,
      CachedDiskHL.Lang.exec o s (compile p) s' ->
      oracle_refines_to T s p o o1 ->
      oracle_refines_to T s p o o2 ->
      o1 = o2.
  Proof.
    induction p; simpl; intros; cleanup; eauto.
    -
      repeat split_ors; eauto;
      eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    -
      repeat split_ors; eauto;
      try eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H2;
      try eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H3;
      eauto; cleanup; try congruence.
    -
      repeat split_ors; eauto;
      try eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H2;
      try eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H3;
      eauto; cleanup; try congruence.
      
    -
      CachedDiskHL.Lang.invert_exec.
      +
        repeat split_ors; cleanup;
        try solve [
              eapply CachedDiskHL.Lang.finished_not_crashed_oracle_app in H0;
              eauto; cleanup; exfalso; eauto ].
        
        repeat (eapply_fresh CachedDiskHL.Lang.exec_finished_deterministic_prefix in H0; eauto; cleanup).
        repeat (eapply_fresh CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H1; eauto; cleanup).
        specialize IHp with (1:=H0)(2:=H16)(3:=H13); cleanup.
        specialize H with (1:=H1)(2:=H17)(3:=H14); cleanup; eauto.
        
      +
        repeat split_ors; cleanup;
        try solve [
              try eapply CachedDiskHL.Lang.finished_not_crashed_oracle_prefix in H1;
              eauto; cleanup; exfalso; eauto ].
        
        try eapply CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H8; eauto; cleanup.
        repeat (eapply_fresh CachedDiskHL.Lang.exec_finished_deterministic_prefix in H1; eauto; cleanup).
        eapply CachedDiskHL.Lang.finished_not_crashed_oracle_app in H1; eauto; cleanup; exfalso; eauto.        
        repeat (eapply_fresh CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H1; eauto; cleanup).
        eapply CachedDiskHL.Lang.finished_not_crashed_oracle_app in H1; eauto; cleanup; exfalso; eauto.

        
        repeat (eapply_fresh CachedDiskHL.Lang.exec_finished_deterministic_prefix in H1; eauto; cleanup).
        repeat (eapply_fresh CachedDiskHL.Lang.exec_deterministic_wrt_oracle in H17; eauto; cleanup).
        
        specialize IHp with (1:=H1)(2:=H15)(3:=H12); cleanup.
        specialize H with (1:=H17)(2:=H16)(3:=H13); cleanup; eauto.
        Unshelve.
        all: eauto.
  Qed.

  (*
  Axiom layer1_exec_compiled_preserves_refines_to:
    forall T (p2: Layer2.prog T) o1 s1 s1',
      Layer1.exec o1 s1 (compile p2) s1' ->
      (exists s2, refines_to s1 s2) ->
      (exists s2', refines_to (extract_state s1') s2').
      
`       *)
  Hint Resolve oracle_ok_nonempty.

  Arguments oracle_ok T p o s : simpl never.
  Arguments oracle_refines_to T d1 p o1 o2 : simpl never.

  
  Lemma high_oracle_exists_ok':
    forall T p2 p1 ol sl sl',
      (exists sh, refines_to sl sh) ->
      CachedDiskHL.Lang.oracle_ok p1 ol sl ->
      CachedDiskHL.Lang.exec ol sl p1 sl' ->
      compilation_of T p1 p2 ->
      exists oh, oracle_refines_to T sl p2 ol oh.
  Proof.
    unfold refines_to, compilation_of;
      induction p2; simpl; intros; cleanup.
    - (* Read *)
      edestruct read_ok; eauto.
      intuition eauto.
      admit.
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
        cleanup; destruct_lifts; eauto;
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
        unfold oracle_refines_to; simpl; fold oracle_refines_to; eauto.
        split; eauto.
        do 2 eexists; intuition eauto.
        right; do 3 eexists; intuition eauto.
        
      + (* Crashed *)
        split_ors; cleanup.
        *
          match goal with
          | [H: Layer1.oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_crashed_split in H;
          eauto; cleanup
          end.
          
          edestruct IHp2; eauto.
          (* intros d Ha; inversion Ha. *)
          exists x1.
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split; eauto.

          do 2 eexists; intuition eauto.          
          rewrite app_nil_r; eauto.
        
        *
          match goal with
          | [H: Layer1.oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_finished_split in H;
          eauto; cleanup
          end.
          edestruct IHp2; eauto.
          (* intros d Hx; inversion Hx. *)
          
          edestruct H;
          try match goal with
          | [H: Layer1.oracle_ok (compile (_ _)) _ _ |- _ ] =>
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
          right; do 3 eexists; intuition eauto. 
  Qed.

  Lemma high_oracle_exists_ok :
    @high_oracle_exists layer1_lts layer2_lts refines_to compilation_of oracle_refines_to. 
  Proof.
    unfold high_oracle_exists; intros.
    eapply high_oracle_exists_ok'; eauto.
    eapply exec_then_oracle_ok; eauto.
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
      eapply_fresh exec_then_oracle_ok in H2.
      edestruct (read_ok o1 s1 a); eauto.
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
      edestruct (read_ok o1 s1 a); cleanup.
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
      repeat (split_ors; cleanup; simpl in * );
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
      repeat (split_ors; cleanup);
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
          compilation_of refines_to oracle_refines_to (Bind p1 p2).
  Proof.
    intros.
    edestruct H.
    constructor; intros.
    unfold compilation_of in *;
    simpl in *; cleanup.

    split; intros.
    - (* Low to High *)
      invert_exec; cleanup; intuition.
      
      +
        unfold oracle_refines_to in H3; cleanup; fold oracle_refines_to in *.
        simpl in *.
        eapply oracle_ok_bind_finished_split in H3 as Hx; eauto; cleanup.
        split_ors; cleanup.
        *
          eapply oracle_ok_exec_crashed_app_nil in H6; eauto; cleanup.
          exfalso; eauto.
          eapply oracle_ok_nonempty; eauto.
        *
          eapply_fresh exec_finished_deterministic in H6; eauto; cleanup.
          apply app_inv_head in H5; cleanup.
          eapply_fresh deterministic_prog in H9; eauto; cleanup.
          edestruct strong_bisimulation_for_program_correct; eauto.
          
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H4.
          edestruct H0.
          edestruct strong_bisimulation_for_program_correct0; eauto.
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H4.
          cleanup.
          eexists; eauto.

      +
        unfold oracle_refines_to in H3; cleanup; fold oracle_refines_to in *.
        split_ors; cleanup.
        *
          rewrite app_nil_r in *.
          eapply_fresh deterministic_prog in H3; eauto; cleanup.
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; try intuition; clear H6 H7.
          eexists; eauto.

        *
          eapply oracle_ok_bind_finished_split in H2 as Hx; eauto; cleanup.
          eapply oracle_ok_exec_crashed_app_nil in H4; eauto; cleanup.
          exfalso; eauto.
          eapply oracle_ok_nonempty; eauto.
          
      +
        cleanup.
        unfold oracle_refines_to in H3; cleanup; fold oracle_refines_to in *.
        simpl in *.
        eapply oracle_ok_bind_finished_split in H3 as Hx; eauto; cleanup.
        split_ors; cleanup.
        *
          eapply oracle_ok_exec_crashed_app_nil in H6; eauto; cleanup.
          exfalso; eauto.
          eapply oracle_ok_nonempty; eauto.
        *
          eapply_fresh exec_finished_deterministic in H6; eauto; cleanup.
          apply app_inv_head in H5; cleanup.
          eapply_fresh deterministic_prog in H9; eauto; cleanup.
          edestruct strong_bisimulation_for_program_correct; eauto.
          
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H4.
          edestruct H0.
          edestruct strong_bisimulation_for_program_correct0; eauto.
          edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H4.
          cleanup; eexists; eauto.

    - (* High to Low *)
      inversion H2; sigT_eq; cleanup; clear H2.
      +
        unfold oracle_refines_to in H3; cleanup; fold oracle_refines_to in *.
        split_ors; cleanup.

        *
          rewrite app_nil_r in *.
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H5; eauto; simpl in *; cleanup; intuition; clear H5 H6.
          exfalso; eapply layer2_finished_not_crashed_oracle_app; eauto.
        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H8; eauto; simpl in *; cleanup; intuition.
          eapply_fresh layer2_exec_finished_deterministic in H9; eauto; cleanup.
          eapply app_inv_head in H7; cleanup.

          edestruct H10; eauto; simpl in *; cleanup; intuition; clear H8 H10.
          simpl in *; cleanup.
          eapply deterministic_prog in H3; eauto; cleanup.

          edestruct H0.
          edestruct strong_bisimulation_for_program_correct0; eauto.
          edestruct H8; eauto; simpl in *; cleanup; try intuition; clear H3 H8.
          cleanup; eexists; eauto.

      +
        unfold oracle_refines_to in H3; cleanup; fold oracle_refines_to in *.
        split_ors; cleanup.
        *
          rewrite app_nil_r in *.
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; intuition; clear H5 H6.
          eapply deterministic_prog in H3; eauto; cleanup.
          eexists; intuition eauto.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H7; eauto; simpl in *; cleanup; intuition.
          exfalso; eapply layer2_finished_not_crashed_oracle_app; eauto.
          
  Qed.
    
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
