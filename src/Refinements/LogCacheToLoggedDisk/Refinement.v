Require Import Framework FSParameters CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.
Notation "'refinement'" := LoggedDiskRefinement.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.



Lemma wp_low_to_high_read :
  forall a,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wp_low_to_high_prog', refines_to; simpl; intros; cleanup.
  unfold refines_to in *; simpl; intros; cleanup.
  split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
  eexists; intuition eauto.
  eapply exec_to_sp with (P := fun o s => refines_to s (mem_map fst x2) /\ s = s1) in H2; unfold refines_to in *; eauto.
  simpl in *.
  cleanup.
  {        
    cleanup; simpl in *; cleanup; eauto;
    eexists; intuition eauto.
    simpl in *.
    eapply cached_log_rep_cache_read; eauto.
  }

  cleanup; simpl in *.
  {
    cleanup.
    do 4 eexists; split; eauto; simpl in *.
  }
  {
    unfold refines_to in *; cleanup.
    split_ors; cleanup;
    eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s (mem_map fst x2) /\ s = s1) in H2; unfold refines_to in *; eauto;
    try solve [do 3 eexists; eauto].
    simpl in *.
    cleanup.
    destruct x; simpl in *; cleanup; eauto; intuition eauto.
    eexists; intuition eauto.
    eapply cached_log_rep_disk_read in D; eauto.
    unfold Disk.read in *; cleanup; eauto.
    destruct p; simpl in *; cleanup; eauto.
    eapply mem_map_fst_some_elim; eauto.
    setoid_rewrite H6 in D1; congruence.
  }
Qed.

Lemma wp_high_to_low_read :
  forall a,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wp_high_to_low_prog'; intros; cleanup.
  simpl in H; cleanup.
  simpl in H1; cleanup; split_ors; cleanup.
  repeat invert_exec.
  eapply exec_to_wp; eauto.

  eapply exec_to_sp with (P := fun o s => refines_to s s2' /\ s = s1) in H; eauto.

  unfold read in *; simpl in *.
  cleanup; simpl in *.
  
  destruct x; simpl in *; split; eauto.
  -  unfold refines_to in *; cleanup.
    eapply mem_map_fst_some_exists in H4; cleanup.
    eapply cached_log_rep_cache_read in H; eauto; cleanup.
    unfold Disk.read in *; cleanup; simpl in *.
    congruence.

   - cleanup.
    unfold refines_to in *; cleanup.
    rewrite <- H1 in H4.
    eapply mem_map_fst_some_exists in H4; cleanup.
    eapply cached_log_rep_disk_read in H0; eauto; cleanup.
    unfold Disk.read in *; simpl in *; cleanup; eauto.
Qed.


Lemma wcp_low_to_high_read :
  forall a,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
  split_ors; cleanup. eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
  eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
  eexists; repeat split; eauto.
Qed.
          
Lemma wcp_high_to_low_read :
  forall a,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
Proof.
  unfold wcp_high_to_low_prog'; intros; cleanup.
  simpl in H, H1; intros; cleanup.
  split_ors; cleanup.
  repeat invert_exec.
  eapply exec_to_wcp; eauto.
Qed.

Lemma wp_low_to_high_write :
  forall a vl,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wp_low_to_high_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  split_ors; cleanup; simpl in *.
  {
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H2; eauto.
    unfold write in H2.
    destruct x1.
    cleanup; eexists; intuition eauto.
    unfold refines_to in *; cleanup; eauto.
    left; intuition eauto.
    edestruct H4; eauto; cleanup.
    do 3 eexists; intuition eauto.
    apply upd_batch_write_all_mem_map; eauto.
    admit. (** TODO: Check this **)
  }
  {
    split_ors; cleanup; simpl in *;
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
  }
Admitted.

Lemma wp_high_to_low_write :
  forall a vl,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wp_high_to_low_prog'; intros; cleanup.
  repeat invert_exec.
  simpl in H1; cleanup.
  repeat (split_ors; cleanup).
  destruct x0.
  eapply exec_to_wp; eauto.
  simpl in H0; unfold refines_to in H0; cleanup.
  edestruct H3; eauto; cleanup.
  simpl; split;
  eauto; unfold refines_to.
  do 3 eexists; split; eauto.
  apply upd_batch_write_all_mem_map; eauto.
  admit. (** TODO: Check this **)

  simpl in H1; cleanup.
  simpl in *;
  repeat (split_ors; cleanup); intuition;
  destruct x1;
  eapply exec_to_wp; eauto;
  unfold write in *; cleanup; intuition;
  try invert_exec; eauto.
Admitted.

Lemma wcp_low_to_high_write :
  forall a vl,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wcp_low_to_high_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  simpl in *; split_ors; cleanup;
  try eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
  simpl; split_ors; cleanup;
  try eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup;
  eexists; intuition eauto.
  eapply exec_to_scp with (P := fun o s => refines_to s s2 /\ s = s1) in H2.
  2: unfold refines_to; eauto.
  simpl in *.
  unfold write in H2; cleanup;
  try solve [simpl in *; cleanup; intuition].
  right; intuition eauto.  
  admit. (** TODO: Prove this *)
Admitted.

Lemma wcp_high_to_low_write :
  forall a vl,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wcp_high_to_low_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  repeat split_ors; cleanup; repeat invert_exec;
  eapply exec_to_wcp; eauto;
  split_ors; cleanup; eauto.
  simpl.
  admit. (** TODO: Prove this **)
Admitted.


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


Hint Resolve sbs_read sbs_write : core.

Theorem sbs :
  StrongBisimulation LoggedDiskRefinement.              
Proof.
  apply bisimulation_restrict_prog.
  induction p; eauto.
  destruct p; eauto.
  apply sbs_ret.
  apply sbs_bind; eauto.
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
                                     valid_prog_h.  
Proof.
  intros.
  eapply bisimulation_restrict_state; eauto.
Qed.
End LoggedDiskBisimulation.

Section TransferToCachedDisk.
  
  Lemma high_oracle_exists_ok:
    high_oracle_exists LoggedDiskRefinement. 
  Proof.
    unfold high_oracle_exists, refines_to;
    induction p2; simpl; intros; cleanup.
    {
      destruct p; simpl in *.
      - (* Read *)
        destruct s1'; do 2 eexists; intuition eauto.        
        left; do 2 eexists; intuition eauto.
        unfold read in *.
        repeat invert_exec; simpl in *;
        inversion H0; sigT_eq;
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.

        right; do 2 eexists; intuition eauto;
        unfold read in *;
        repeat (invert_exec; simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        simpl in *; cleanup; invert_exec; eauto.

        repeat (simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        simpl in *; cleanup; invert_exec; eauto.

        repeat (simpl in *; split_ors; cleanup);        
        try (inversion H0; sigT_eq);
        repeat invert_exec; simpl in *;
        destruct s1, s0; eauto.
        
      - (* Write *)
        destruct s1'.
        + do 2 eexists; intuition eauto;
          left; eauto.
          eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
          do 2 eexists; intuition eauto.
          admit. (* Doable *)
          
        + destruct (excluded_middle_dec (s = s1));
          do 2 eexists; intuition eauto;
          left; eauto.        
    }
    - (* Ret *)
      destruct s1'; eexists; eauto.
    - (* Bind *)
      invert_exec.
      + (* Finished *)
        edestruct IHp2; eauto.
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; eauto.
        cleanup; simpl in *; eauto.
        edestruct H; eauto.
        do 5 eexists; repeat (split; eauto).
        right; eauto.
        do 3 eexists; repeat (split; eauto).        

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
          
          Unshelve.
          eauto.
  Admitted.


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
