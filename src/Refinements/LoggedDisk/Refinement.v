Require Import Framework CacheLayer DiskLayer CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.

  Axiom exec_compiled_preserves_refinement:
    exec_compiled_preserves_refinement LoggedDiskRefinement.

  Axiom exec_preserves_refinement:
    exec_preserves_refinement LoggedDiskRefinement.


  Lemma merge_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      m2 a <> None ->
      exists vs, merge m1 m2 a = Some vs /\
            fst vs = v.
  Proof.
    unfold merge; simpl; intros.
    cleanup.
    destruct (m2 a); try congruence; eauto.
  Qed.
  
  Lemma merge_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      merge m1 m2 a = m2 a.
  Proof.
    unfold merge; simpl; intros.
    cleanup; eauto.
  Qed.
  
  Lemma cached_log_rep_cache_read :
    forall F s2 s1 a v,
      cached_log_rep F s2 s1 ->
      fst s1 a = Some v ->
      Disk.read s2 a = Some v.
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    cleanup.
    eapply merge_some_l in H0; eauto; cleanup.
    rewrite H0; eauto.
    eapply H1.
    congruence.
  Qed.
  
  Lemma cached_log_rep_disk_read :
    forall F s2 s1 a,
      cached_log_rep F s2 s1 ->
      fst s1 a = None ->
      Disk.read s2 a = Disk.read (snd (snd s1)) a.
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    cleanup.
    erewrite merge_some_r; eauto.
  Qed.
  
  Lemma wp_low_to_high_read :
    forall a,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold  compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; unfold refines_to in *; eauto.
    simpl in *.
    cleanup.
    {        
      cleanup; simpl in *; cleanup; eauto;
      eexists; intuition eauto.      
      eapply cached_log_rep_cache_read; eauto.
      erewrite cached_log_rep_disk_read; eauto.
    }

    cleanup; simpl in *.
    {
      cleanup.
      eexists; intuition eauto.
      rewrite <- H3 in H9.
      erewrite cached_log_rep_disk_read; eauto.
    }
    {
      cleanup; eauto.
      eexists; intuition eauto.
      erewrite cached_log_rep_disk_read; eauto.
    }
  Qed.

  Lemma wp_high_to_low_read :
    forall a,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    inversion H9; clear H9; cleanup.
    eapply exec_to_wp; eauto.

    eapply exec_to_sp with (P := fun o s => refines_to s s2') in H0; unfold refines_to in *; eauto.

    unfold read in *; simpl in *.
    cleanup; simpl in *.
    destruct x4; simpl in *; cleanup; eauto.
    - destruct x2; simpl in *; split; eauto.
      eapply cached_log_rep_cache_read in H0; eauto; cleanup.
      congruence.
      
    - destruct x2, s0; simpl in *; split; eauto.
      eapply cached_log_rep_disk_read in H0; eauto; cleanup.
      simpl in *; congruence.
  Qed.


  Lemma wcp_low_to_high_read :
    forall a,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    destruct x0, s0.
    eapply exec_to_scp with (P := fun o s => refines_to s s2) in H3; unfold refines_to in *; eauto.
    simpl in *; cleanup.
    repeat (split_ors; repeat (cleanup; simpl in *);
    try solve [ inversion H; cleanup; eexists; eauto ]).
  Qed.

  Lemma wcp_high_to_low_read :
    forall a,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    inversion H8; clear H8; cleanup.
    eapply exec_to_wcp; eauto.
    destruct x0, s0.
    eapply exec_to_scp with (P := fun o s => refines_to s s2') in H0; unfold refines_to in *; eauto.
    simpl in *; cleanup.
    repeat (split_ors; repeat (cleanup; simpl in *);
    try solve [ inversion H0; cleanup; eexists; eauto ]).
  Qed.

  Lemma wp_low_to_high_write :
    forall a vl,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H3; unfold refines_to in *; eauto.
    unfold write in *.
    simpl in *; cleanup.
    eexists; intuition eauto.
  Qed.

  Lemma wp_high_to_low_write :
    forall a vl,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    invert_exec.
    inversion H8; clear H8; cleanup.
    repeat (split_ors; cleanup).
    eapply exec_to_wp; eauto.
    eexists; eauto.
    destruct x3; eauto.
  Qed.

  
  Lemma wcp_low_to_high_write :
    forall a vl,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup;
    eexists; intuition eauto.
    - right; intuition eauto.
      admit. (* TODO: Check this *)
  Admitted.

  Lemma wcp_high_to_low_write :
    forall a vl,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    repeat split_ors; cleanup; repeat invert_exec;
    try inversion H8; try clear H8; cleanup;
    try inversion H9; try clear H9; cleanup;
    eapply exec_to_wcp; eauto.
    - admit. (* TODO: Check this *)
  Admitted.


  Lemma wp_low_to_high_ret :
    forall T (v: T),
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    invert_exec; intuition eauto.
  Qed.

  Lemma wp_high_to_low_ret :
    forall T (v: T),
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wp; eauto.
    econstructor; eauto.
  Qed.

  Lemma wcp_low_to_high_ret :
    forall T (v: T),
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wcp_low_to_high_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    invert_exec; eauto.
  Qed.

  Lemma wcp_high_to_low_ret :
    forall T (v: T),
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wcp_high_to_low_prog', compilation_of, refines_to; simpl; intros; cleanup.
    unfold compilation_of, refines_to in *; simpl in *; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wcp; eauto.
    econstructor; eauto.
  Qed.
    
  Theorem sbs_read :
    forall a,
      StrongBisimulationForProgram LoggedDiskRefinement (|Read a|).              
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
      StrongBisimulationForProgram LoggedDiskRefinement (|Write a lv|).              
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

  
  Theorem sbs_ret :
    forall T (v: T),
    StrongBisimulationForProgram LoggedDiskRefinement
      (Ret v).              
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
      StrongBisimulationForProgram LoggedDiskRefinement p1 ->
      (forall t, StrongBisimulationForProgram LoggedDiskRefinement (p2 t)) ->
      StrongBisimulationForProgram LoggedDiskRefinement (Bind p1 p2).
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

  Hint Resolve sbs_read sbs_ret sbs_write sbs_bind : core.
  
  Theorem sbs :
      StrongBisimulation LoggedDiskRefinement.              
  Proof.
    apply bisimulation_restrict_prog.
    induction p; eauto.
    destruct p; eauto.
  Qed.

  Hint Resolve sbs : core.

  Theorem sbs_general:
    forall valid_state_h valid_prog_h,
      exec_compiled_preserves_validity LoggedDiskRefinement
        (refines_to_valid LoggedDiskRefinement valid_state_h) ->
      
      exec_preserves_validity LoggedDiskLang valid_state_h ->
      
      StrongBisimulationForValidStates LoggedDiskRefinement
        (refines_to_valid LoggedDiskRefinement valid_state_h)
        valid_state_h
        (compiles_to_valid LoggedDiskRefinement valid_prog_h)        
        valid_prog_h.  
  Proof.
    intros.
    eapply bisimulation_restrict_state; eauto.
  Qed.
End LoggedDiskBisimulation.

Section TransferToCachedDisk.
              
Lemma high_oracle_exists_ok':
  forall T p2 p1 ol sl sl',
    (exists sh, refines_to sl sh) ->
    low.(exec) ol sl p1 sl' ->
    compilation_of T p1 p2 ->
    exists oh, oracle_refines_to T sl p2 ol oh.
Proof.
  unfold refines_to, compilation_of;
  induction p2; simpl; intros; cleanup.
  - (* Read *)
    destruct sl'; eexists; eauto.
  - (* Write *)
    destruct sl'; try solve [eexists; eauto].
    eexists; right; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol) in H0 as Hx; unfold refines_to in *; eauto.
    do 2 eexists; intuition eauto.
    admit. (* Doable *)
    
    destruct (excluded_middle_dec (s = sl));
    eexists; left; eauto.
    
  - (* Ret *)
    destruct sl'; eexists; eauto.
  - (* Bind *)
    invert_exec.
    + (* Finished *)
      edestruct IHp2; eauto.
      eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; unfold refines_to in *; eauto.
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
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; unfold refines_to in *; eauto.
        cleanup; simpl in *; eauto.
        edestruct H; eauto.
        do 5 eexists; repeat (split; eauto).
        right; eauto.
        do 3 eexists; repeat (split; eauto).
        unfold compilation_of; eauto.
        Unshelve.
        eauto.
Admitted.

Lemma high_oracle_exists_ok :
  high_oracle_exists LoggedDiskRefinement. 
Proof.
  unfold high_oracle_exists; intros.
  eapply high_oracle_exists_ok'; eauto.
Qed.


Theorem transfer_to_CachedDisk:
    forall related_states_h
    valid_state_h
    valid_prog_h,
    
    SelfSimulation
      LoggedDiskLang
      valid_state_h
      valid_prog_h
      related_states_h ->
    
    oracle_refines_to_same_from_related LoggedDiskRefinement related_states_h ->

    exec_compiled_preserves_validity LoggedDiskRefinement                           
    (refines_to_valid LoggedDiskRefinement valid_state_h) ->
    
    SelfSimulation
      CachedDiskLang
      (refines_to_valid LoggedDiskRefinement valid_state_h)
      (compiles_to_valid LoggedDiskRefinement valid_prog_h)
      (refines_to_related LoggedDiskRefinement related_states_h).
Proof.
  intros; eapply transfer_high_to_low; eauto.
  apply sbs.
  apply high_oracle_exists_ok.
Qed.

End TransferToCachedDisk.
