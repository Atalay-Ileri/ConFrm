Require Import Framework FSParameters AuthenticatedDiskLayer FileDiskLayer.
Require Import File FileToFileDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low_op'" := TransactionalDiskOperation.
Notation "'high_op'" := (FileDiskOperation inode_count).
Notation "'low'" := TransactionalDiskLang.
Notation "'high'" := (FileDiskLang inode_count).
Notation "'refinement'" := FileDiskRefinement.

Section FileDiskBisimulation.

  Axiom exec_compiled_preserves_refinement:
    exec_compiled_preserves_refinement refinement.

  Axiom exec_preserves_refinement:
    exec_preserves_refinement refinement.


  Lemma merge_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      merge m1 m2 a = Some v.
  Proof.
    unfold merge; simpl; intros.
    cleanup; eauto.
  Qed.
  
  Lemma merge_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      merge m1 m2 a = m2 a.
  Proof.
    unfold merge; simpl; intros.
    cleanup; eauto.
  Qed.

  Lemma apply_list_app:
    forall A AEQ V  l l' (m: @mem A AEQ V), 
      apply_list m (l++l') =
      apply_list (apply_list m l) l'.
  Proof.
    induction l; simpl; eauto.
  Qed.
   
  Lemma wp_low_to_high_read :
    forall inum a,
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Read inum a|).
  Proof.
    unfold wp_low_to_high_prog'; intros; cleanup.
    unfold  compilation_of in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H3; eauto.

    cleanup; simpl in *; cleanup; eauto;
    eexists; intuition eauto; unfold refines_to in *; cleanup;
    try congruence.      
    rewrite apply_list_get_latest_eq in D0; eauto.
    right; intuition.        
    rewrite <- apply_list_get_latest_eq; eauto.
    }
    cleanup; eauto.
    cleanup; simpl in *; cleanup.
  Qed.

  Lemma wp_high_to_low_read :
    forall a,
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros.
    simpl in *; subst.
    destruct H2; try solve [cleanup; split_ors; cleanup ].
    cleanup.
    repeat invert_exec.
    cleanup.
    eapply exec_to_wp; eauto; simpl.
    split; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2') in H; eauto.
    unfold read in *; simpl in *.
    cleanup; simpl in *.        
    rewrite apply_list_get_latest_eq in H; cleanup; simpl in *; cleanup;
    unfold refines_to in H; simpl in *; cleanup;    
    repeat split_ors; cleanup; eauto;
    try setoid_rewrite H2 in D; cleanup; eauto.
    try setoid_rewrite H3 in D; cleanup; eauto.
  Qed.

  Lemma wcp_low_to_high_read :
    forall a,
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; subst.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.

    split_ors; cleanup; eauto.
    eexists; intuition eauto.
    - right; intuition eauto.
      unfold refines_to in *; cleanup;
      setoid_rewrite H2 in D; cleanup.
      rewrite <- apply_list_get_latest_eq; eauto.
    - right; intuition eauto.
      unfold refines_to in *; cleanup;
      setoid_rewrite H2 in D; cleanup.
      rewrite <- apply_list_get_latest_eq; eauto.
  Qed.

  Lemma wcp_high_to_low_read :
    forall a,
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat (split_ors; cleanup);
    repeat invert_exec;
    cleanup;
    repeat match goal with
    | [H: Operation.exec _ _ _ _ _ |- _ ] =>
      inversion H; clear H; cleanup
    | [H: exec' _ _ _ _ |- _ ] =>
      inversion H; clear H; cleanup
    end;
    eapply exec_to_wcp; eauto.
  Qed.

  Lemma wp_low_to_high_write :
    forall a vl,
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; eauto.
    unfold write in *.
    simpl in *; cleanup.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H1 H17; unfold refines_to in *; simpl in *; cleanup.
    rewrite apply_list_app; eauto.
  Qed.

  Lemma wp_high_to_low_write :
    forall a vl,
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat invert_exec; cleanup.
    repeat (split_ors; cleanup).
    eapply exec_to_wp; simpl; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H; eauto.
    unfold write in *.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H1; unfold refines_to in *; simpl in *; cleanup.
    rewrite apply_list_app; eauto.
    rewrite <- H1 at 1; rewrite apply_list_app; simpl; eauto.
  Qed.

  
  Lemma wcp_low_to_high_write :
    forall a vl,
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup;
    eexists; intuition eauto.

    right; intuition eauto.
    apply refines_to_upd; eauto.
  Qed.

  Lemma wcp_high_to_low_write :
    forall a vl,
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat split_ors; cleanup; repeat invert_exec;
    try inversion H8; try clear H8; cleanup;
    try inversion H9; try clear H9; cleanup;
    eapply exec_to_wcp; eauto.
    - split_ors; cleanup; eauto.
      
    - split_ors; cleanup; eauto.
      repeat invert_exec;
      repeat match goal with
             | [H: Operation.exec _ _ _ _ _ |- _ ] =>
               inversion H; clear H; cleanup
             | [H: exec' _ _ _ _ |- _ ] =>
               inversion H; clear H; cleanup
             end.
      eapply refines_to_upd; eauto.
  Qed.

  Lemma wp_low_to_high_start :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H0 H9.
    unfold refines_to in *; cleanup; eauto.
  Qed.

  Lemma wp_high_to_low_start :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H H5.
    unfold refines_to in *; cleanup; eauto.
  Qed.

  Lemma wcp_low_to_high_start :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup; eauto.
    eexists; intuition eauto.
    right; unfold refines_to in *; cleanup; eauto.
  Qed.

  Lemma wcp_high_to_low_start :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wcp; eauto.
    split_ors; cleanup.
    repeat invert_exec; eauto.
    repeat invert_exec; eauto.
    cleanup.
    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.
    unfold refines_to in *; cleanup; eauto.
  Qed.

  
  Lemma wp_low_to_high_abort :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H1 H9.
    unfold refines_to in *; simpl in *; cleanup; eauto.
  Qed.

  Lemma wp_high_to_low_abort :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    clear H1 H5.
    unfold refines_to in *; simpl; cleanup; eauto.
  Qed.

  Lemma wcp_low_to_high_abort :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup; eauto.
    eexists; intuition eauto.
    right; unfold refines_to in *; cleanup; eauto.
  Qed.

  Lemma wcp_high_to_low_abort :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wcp; eauto.
    split_ors; cleanup.
    repeat invert_exec; eauto.
    repeat invert_exec; eauto.
    cleanup.
    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.
    unfold refines_to in *; cleanup; eauto.
  Qed.

  
  Lemma wp_low_to_high_commit :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.    
    unfold refines_to; simpl; cleanup; eauto.
    intuition.
    unfold refines_to in H1; cleanup; intuition;
    setoid_rewrite H14 in D; cleanup.
    rewrite <- H7; eauto.
  Qed.

  Lemma wp_high_to_low_commit :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    unfold refines_to; simpl; cleanup; eauto.
    intuition.
    unfold refines_to in H1; cleanup; intuition;
    setoid_rewrite H2 in D; cleanup.
    rewrite <- H7; eauto.
  Qed.

  Lemma wcp_low_to_high_commit :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup; eauto.
    eexists; intuition eauto.
    right; intuition eauto.
    unfold refines_to; simpl; cleanup; eauto.
    intuition.
    unfold refines_to in H1; cleanup; intuition;
    setoid_rewrite H2 in D; cleanup; eauto.
  Qed.

  Lemma wcp_high_to_low_commit :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wcp; eauto.
    split_ors; cleanup.
    repeat invert_exec; eauto.
    repeat invert_exec; eauto.
    cleanup.
    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.
    unfold refines_to; simpl; cleanup; eauto.
    clear H4; intuition.
    unfold refines_to in H1; cleanup; intuition;
    setoid_rewrite H2 in D; cleanup; eauto.
  Qed.
  

  Lemma wp_low_to_high_ret :
    forall T (v: T),
    wp_low_to_high_prog' _ _ _ _ refinement _ (Ret v).
  Proof.
    unfold wp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    invert_exec; intuition eauto.
  Qed.

  Lemma wp_high_to_low_ret :
    forall T (v: T),
    wp_high_to_low_prog' _ _ _ _ refinement _ (Ret v).
  Proof.
    unfold wp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    clear H4; eapply exec_to_wp; simpl; eauto.
    econstructor.
  Qed.

  Lemma wcp_low_to_high_ret :
    forall T (v: T),
    wcp_low_to_high_prog' _ _ _ _ refinement _ (Ret v).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    invert_exec; eauto.
  Qed.

  Lemma wcp_high_to_low_ret :
    forall T (v: T),
    wcp_high_to_low_prog' _ _ _ _ refinement _ (Ret v).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of; simpl; intros; cleanup.
    unfold compilation_of in *; simpl in *; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wcp; eauto.
    econstructor; eauto.
  Qed.
    
  Theorem sbs_read :
    forall a,
      StrongBisimulationForProgram refinement (|Read a|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    eapply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_read.
    apply wp_high_to_low_read.    
    apply wcp_low_to_high_read.
    apply wcp_high_to_low_read.
  Qed.

  Theorem sbs_write :
    forall a lv,
      StrongBisimulationForProgram refinement (|Write a lv|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    eapply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_write.
    apply wp_high_to_low_write.
    apply wcp_low_to_high_write.
    apply wcp_high_to_low_write.
  Qed.

  Theorem sbs_start :
      StrongBisimulationForProgram refinement (|Start|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_start.
    apply wp_high_to_low_start.
    apply wcp_low_to_high_start.
    apply wcp_high_to_low_start.
  Qed.

  Theorem sbs_abort :
      StrongBisimulationForProgram refinement (|Abort|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_abort.
    apply wp_high_to_low_abort.
    apply wcp_low_to_high_abort.
    apply wcp_high_to_low_abort.
  Qed.

  Theorem sbs_commit :
      StrongBisimulationForProgram refinement (|Commit|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_commit.
    apply wp_high_to_low_commit.
    apply wcp_low_to_high_commit.
    apply wcp_high_to_low_commit.
  Qed.

  
  Theorem sbs_ret :
    forall T (v: T),
    StrongBisimulationForProgram refinement (Ret v).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    eapply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_ret.
    apply wp_high_to_low_ret.
    apply wcp_low_to_high_ret.
    apply wcp_high_to_low_ret.
  Qed.

  Theorem sbs_bind:
    forall T1 T2 (p1: high.(prog) T1) (p2: T1 -> high.(prog) T2),
      StrongBisimulationForProgram refinement p1 ->
      (forall t, StrongBisimulationForProgram refinement (p2 t)) ->
      StrongBisimulationForProgram refinement (Bind p1 p2).
  Proof.
    intros.
    edestruct H.
    constructor; intros.
    simpl in *; unfold compilation_of in *;
    simpl in *; cleanup.

    split; intros.
    - (* Low to High *)
      invert_exec; cleanup.
      
      + split_ors; cleanup.
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup.
     
        eapply_fresh exec_finished_deterministic_prefix in H5; eauto; cleanup.
        eapply_fresh exec_deterministic_wrt_oracle in H6; eauto; cleanup.
        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
        edestruct H0.
        simpl in *; unfold compilation_of in *;
        edestruct strong_bisimulation_for_program_correct0; eauto.
        edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
        cleanup.
        eexists; intuition eauto.
        econstructor; eauto.
        simpl; eauto.
        
      +
        split_ors; cleanup;
        split_ors; cleanup;
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H4; eauto; cleanup;
        try solve [eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup].
        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; try intuition; clear H6 H7.
          exists (Crashed s); repeat (split; eauto).
          eapply ExecBindCrash; eauto.

        *
          eapply_fresh exec_finished_deterministic_prefix in H5; eauto; cleanup.
           eapply_fresh exec_deterministic_wrt_oracle in H6; eauto; cleanup.
           edestruct strong_bisimulation_for_program_correct; eauto.
           edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
           edestruct H0.
           simpl in *; unfold compilation_of in *;
           edestruct strong_bisimulation_for_program_correct0; eauto.
           edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H3.
           cleanup.
           eexists; intuition eauto.
           econstructor; eauto.
           simpl; eauto.

    - (* High to Low *)
      invert_exec; cleanup.
      

      + split_ors; cleanup.
        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H7; eauto; simpl in *; cleanup; try intuition; clear H7 H8.
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H2; eauto; cleanup.

        edestruct strong_bisimulation_for_program_correct; eauto.
        edestruct H9; eauto; simpl in *; cleanup; try intuition; clear H9 H10.
        eapply_fresh exec_finished_deterministic_prefix in H2; eauto; cleanup.
        simpl in *.
        edestruct H0.
        simpl in *; unfold compilation_of in *;
        edestruct strong_bisimulation_for_program_correct0; eauto.
        edestruct H4; eauto; simpl in *; cleanup; try intuition; clear H4 H9; cleanup.           
        eapply_fresh exec_deterministic_wrt_oracle in H3; eauto; cleanup.
        eexists; intuition eauto.
        econstructor; eauto.
        
      +
        split_ors; cleanup;
        split_ors; cleanup;
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H4; eauto; cleanup;
        try solve [eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup].
        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H6; eauto; simpl in *; cleanup; try intuition; clear H6 H7.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.
          simpl in *.
          exists (Crashed x5); repeat (split; eauto).
          eapply ExecBindCrash; eauto.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H8; eauto; simpl in *; cleanup; try intuition; clear H8 H9.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H7; eauto; simpl in *; cleanup; try intuition; clear H7 H8.
          eapply_fresh exec_deterministic_wrt_oracle_prefix in H3; eauto; cleanup.

        *
          edestruct strong_bisimulation_for_program_correct; eauto.
          edestruct H9; eauto; simpl in *; cleanup; try intuition; clear H9 H10.
           eapply_fresh exec_finished_deterministic_prefix in H3; eauto; cleanup.
           edestruct H0.
           simpl in *; unfold compilation_of in *;
           edestruct strong_bisimulation_for_program_correct0; eauto.
           edestruct H2; eauto; simpl in *; cleanup; try intuition; clear H2 H9.
           cleanup.
           eapply_fresh exec_deterministic_wrt_oracle in H4; eauto; cleanup.
           eexists; intuition eauto.
           econstructor; eauto.
    Unshelve.
    all: eauto.
  Qed.

  Hint Resolve sbs_read sbs_write sbs_start sbs_abort sbs_commit sbs_ret sbs_bind : core.
  
  Theorem sbs :
      StrongBisimulation refinement.              
  Proof.
    apply bisimulation_restrict_prog.
    induction p; eauto.
    destruct p; eauto.
  Qed.

  Hint Resolve sbs : core.

  Theorem sbs_general:
    forall valid_state_h valid_prog_h,
      exec_compiled_preserves_validity refinement
        (refines_to_valid refinement valid_state_h) ->
      
      exec_preserves_validity TransactionalDiskLang valid_state_h ->
      
      StrongBisimulationForValidStates refinement
        (refines_to_valid refinement valid_state_h)
        valid_state_h
        (compiles_to_valid refinement valid_prog_h)        
        valid_prog_h.  
  Proof.
    intros.
    eapply bisimulation_restrict_state; eauto.
  Qed.

End TransactionalDiskBisimulation.

Section TransferToTransactionCache.

   Lemma write_all_app :
          forall V l1 l2 (l3 l4: list V) m,
            length l1 = length l3 ->
            (forall i, In i l1 -> m i <> None) ->
            write_all m (l1++l2) (l3++l4) = write_all (write_all m l1 l3) l2 l4.
        Proof.
          induction l1; simpl in *; destruct l3; simpl in *;
          intros; cleanup; try congruence.
          destruct_fresh (m a); simpl in *.
          erewrite IHl1; eauto.
          intros; simpl.
          unfold upd_disk.
          destruct (addr_dec a i); subst; [rewrite upd_eq; eauto | rewrite upd_ne; eauto];
          congruence.
          exfalso; eapply H0; eauto.
        Qed.
      
      Lemma write_all_merge_apply_list:
        forall x6 x4 x,
          refines_to (Some x6, x4) x ->
          write_all x4 (map fst (rev x6)) (map snd (rev x6)) =
          merge (apply_list empty_mem (rev x6)) x4.
      Proof.
        induction x6; simpl in *; intros; eauto.
        unfold refines_to in *; simpl in *; cleanup.
        repeat rewrite map_app; simpl in *.
        rewrite write_all_app, apply_list_app in *; eauto; simpl in *.
        unfold addrs_match in *.
        destruct a, x; simpl in *.
        erewrite IHx6; eauto.
        unfold upd_disk.
        extensionality a'; simpl.
        unfold merge at 4; simpl.
        - destruct (addr_dec a a'); subst; simpl;
        [rewrite upd_eq; eauto
        | rewrite upd_ne; eauto].
          
          + destruct_fresh (d0 a');
            [| exfalso; eapply H1; eauto;
               rewrite upd_eq; eauto; congruence ].
            destruct_fresh (apply_list empty_mem (rev x6) a').
            * edestruct merge_some_l
                with (m2:= d0); eauto.
              congruence.
              cleanup.
              pose proof H.
              unfold merge in H; simpl.
              rewrite D0, D in H.
              destruct (merge (apply_list
                 empty_mem (rev x6)) d0 a');
              try congruence; cleanup.
              rewrite upd_eq; eauto.
      Admitted.
              
Lemma high_oracle_exists_ok':
  forall T p2 p1 ol sl sl',
    (exists sh, refines_to sl sh) ->
    low.(exec) ol sl p1 sl' ->
    compilation_of T p1 p2 ->
    exists oh, oracle_refines_to T sl p2 ol oh.
Proof.
  unfold compilation_of;
  induction p2; simpl; intros; cleanup.
  - (* Start *)
    destruct sl'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      simpl in *; cleanup.
      eexists; left; do 2 eexists; intuition eauto.
      destruct s; simpl in *.
      unfold refines_to in *; simpl in *; intuition subst; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      simpl in *; cleanup.
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       try (inversion H1; clear H1); cleanup; eauto;
       try solve [
             eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
    }
  - (* Read *)
    destruct sl'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      unfold read in Hx; simpl in Hx; cleanup;
      cleanup; simpl in *; cleanup;
      
      eexists; left; do 2 eexists; intuition eauto;
      destruct s; cleanup; simpl in *; cleanup; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
       unfold read in Hx; repeat (simpl in *; cleanup).
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       try (inversion H1; clear H1); cleanup; eauto;
       try solve [
             eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
       eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto.       
    }
  - (* Write *)
    destruct sl'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      unfold write in Hx; simpl in *; cleanup;
      cleanup; simpl in *; cleanup;      
      try destruct s; cleanup; simpl in *; cleanup; eauto;
      eexists; left; do 2 eexists; intuition eauto;
      try destruct s; cleanup; simpl in *; cleanup; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      unfold write in Hx; repeat (simpl in *; cleanup).
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       inversion H1; clear H1; cleanup; eauto;
       try solve [
             eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
       eexists; right; do 2 eexists; intuition eauto;
       destruct s; simpl in *; cleanup; eauto.
    }
  - (* Commit *)
    destruct sl'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      simpl in *; cleanup.
      cleanup; simpl in *; cleanup;
      eexists; left; do 2 eexists; intuition eauto;
      destruct s; cleanup; simpl in *; cleanup; eauto.
      eexists; intuition eauto.
      rewrite <- map_fst_split, <- map_snd_split.
      erewrite write_all_merge_apply_list; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
       simpl in *; cleanup.
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       try solve [
             inversion H1; clear H1; cleanup; eauto;
             eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
       
       destruct s; simpl in *; cleanup; eauto.
       eexists; right; do 2 eexists; intuition eauto.
       admit. (* TODO: Solve this *)

       inversion H1; clear H1; cleanup; eauto.
       eexists; right; do 2 eexists; intuition eauto;
       destruct s; simpl in *; cleanup; eauto.
       admit. (* TODO: Solve this *)
    
       eexists; right; do 2 eexists; intuition eauto;
       destruct s; simpl in *; cleanup; eauto.
       right; intuition eauto; eexists; intuition eauto.
       admit. (* TODO: Solve this *)       
    }
    
  - (* Abort *)
    destruct sl'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      simpl in *; cleanup.
      eexists; left; do 2 eexists; intuition eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; eauto.
      simpl in *; cleanup.
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       try (inversion H1; clear H1); cleanup; eauto;
       try solve [
             eexists; right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
    }
  - destruct sl'; eexists; eauto.
  - (* Bind *)
    invert_exec.
    + (* Finished *)
      edestruct IHp2; eauto.
      eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *;  eauto.
      cleanup; simpl in *; eauto.
      edestruct H; eauto.
      do 5 eexists; repeat (split; eauto).
      right; eauto.
      do 3 eexists; repeat (split; eauto).        
      unfold compilation_of; eauto.
    + (* Crashed *)
      split_ors; cleanup.
      * (* p1 crashed *)
        edestruct IHp2; eauto.
        do 5 eexists; repeat (split; eauto).
      * (* p2 Crashed *)
        edestruct IHp2; eauto.
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; eauto.
        cleanup; simpl in *; eauto.
        edestruct H; eauto.
        do 5 eexists; repeat (split; eauto).
        right; eauto.
        do 3 eexists; repeat (split; eauto).
        unfold compilation_of; eauto.
        Unshelve.
        all: constructor.
Admitted.

Lemma high_oracle_exists_ok :
  high_oracle_exists refinement. 
Proof.
  unfold high_oracle_exists; intros.
  eapply high_oracle_exists_ok'; eauto.
Qed.


Theorem transfer_to_TransactionCache:
    forall related_states_h
    valid_state_h
    valid_prog_h,
    
    SelfSimulation
      high
      valid_state_h
      valid_prog_h
      related_states_h ->
    
    oracle_refines_to_same_from_related refinement related_states_h ->

    exec_compiled_preserves_validity refinement                           
    (refines_to_valid refinement valid_state_h) ->
    
    SelfSimulation
      low
      (refines_to_valid refinement valid_state_h)
      (compiles_to_valid refinement valid_prog_h)
      (refines_to_related refinement related_states_h).
Proof.
  intros; eapply transfer_high_to_low; eauto.
  apply sbs.
  apply high_oracle_exists_ok.
Qed.

End TransferToTransactionCache.
