Require Import Framework FSParameters CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.
Notation "'refinement'" := LoggedDiskRefinement.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.

  

  
  Lemma exec_compiled_preserves_refinement:
    exec_compiled_preserves_refinement refinement.
  Proof.
    unfold exec_compiled_preserves_refinement.
    induction p2; simpl in *; intros; cleanup.
    {
      destruct p; simpl in *.
      {
        destruct ret.
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
        simpl in *; repeat (cleanup; simpl in *); eauto;
                            do 4 eexists; intuition eauto.

      eapply exec_to_scp with (P := fun o s' => refines_to s' x /\ s' = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; repeat (try split_ors; cleanup; simpl in *); eauto;
                          inversion H0; cleanup; eauto;
                          do 4 eexists; intuition eauto.
    }
    {
      destruct ret.
          
      assume (A:(forall s' t, strongest_postcondition CachedDiskLang (write l l0) (fun o s => exists s2, refines_to s s2) t s' ->
                         exists s2' : state', refines_to s' s2')).

      eapply A.
      eapply exec_to_sp; eauto.

      assume (A:(forall s', strongest_crash_postcondition CachedDiskLang (write l l0) (fun o s => exists s2, refines_to s s2) s' ->
                         exists s2' : state', refines_to s' s2')).
      eapply A.
      eapply exec_to_scp; eauto.
    }
    }

    {
      destruct ret.
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; cleanup; simpl; eauto; do 4 eexists; intuition eauto.
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; cleanup; simpl; eauto; do 4 eexists; intuition eauto.
    }

    {
      invert_exec; eauto.
      split_ors; cleanup; eauto.
      eapply IHp2 in H1; eauto.
    }
  Admitted.
  
  Lemma exec_preserves_refinement:
    exec_preserves_refinement refinement.
  Proof.
    unfold exec_preserves_refinement; induction p; simpl; intros.
    destruct ret.
    {
      eapply exec_to_sp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
      destruct p; simpl in *; cleanup; eauto.
      clear H; unfold refines_to in *; cleanup.
      admit. (* Doable *)
    }
    {
      eapply exec_to_scp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
      destruct p; simpl in *; cleanup; eauto.
      split_ors; cleanup; eauto.
      clear H; unfold refines_to in *; cleanup.
      admit. (* Doable *)
    }

    destruct ret.
    {
      eapply exec_to_sp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
      simpl in *; cleanup; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => exists x, refines_to x s) in H0; eauto.
    }
    
    invert_exec.
    eapply IHp in H1; eauto; simpl in *.
    split_ors; cleanup; eauto.
    eapply IHp in H1; eauto; simpl in *.
  Admitted.
      
  Lemma merge_set_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      m2 a <> None ->
      exists vs, merge_set m1 m2 a = Some vs /\
            fst vs = v.
  Proof.
    unfold merge_set; simpl; intros.
    cleanup.
    destruct (m2 a); try congruence; eauto.    
  Qed.
  
  Lemma merge_set_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      merge_set m1 m2 a = m2 a.
  Proof.
    unfold merge_set; simpl; intros.
    cleanup; eauto.
  Qed.

  
  Lemma cached_log_rep_cache_read :
    forall F s2 s1 a v log_state,
      cached_log_rep F s2 s1 log_state ->
      fst s1 (data_start + a) = Some v ->
      Disk.read s2 a = Some v.
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    cleanup; unfold shift; simpl in *.
    eapply merge_set_some_l in H0; eauto; cleanup.
    rewrite H0; eauto.
    eapply H1.
    congruence.
  Qed.
  
  Lemma cached_log_rep_disk_read :
    forall F s2 s1 a log_state,
      cached_log_rep F s2 s1 log_state ->
      fst s1 (data_start + a) = None ->
      Disk.read s2 a = Disk.read (snd (snd s1)) (data_start + a).
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    unfold shift in *; simpl; cleanup.
    erewrite merge_set_some_r; eauto.
  Qed.

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
      split_ors; cleanup.
      eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
      eexists; intuition eauto.
      eapply exec_to_sp with (P := fun o s => refines_to s (mem_map fst x2) /\ s = s1) in H2; unfold refines_to in *; eauto.
      simpl in *.
      cleanup.
      destruct x; simpl in *; cleanup; eauto; intuition eauto.
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
    destruct x2; simpl in *; cleanup; eauto.
    - destruct x; simpl in *; split; eauto.
      unfold refines_to in *; cleanup.
      eapply cached_log_rep_cache_read in H0; eauto; cleanup.
      congruence.
      
    - destruct x, s0; simpl in *; split; eauto.
      unfold refines_to in *; cleanup.
      eapply cached_log_rep_disk_read in H0; eauto; cleanup.
      unfold Disk.read in *; simpl in *; cleanup; eauto.
      simpl in *; congruence.
  Qed.


  Lemma wcp_low_to_high_read :
    forall a,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wcp_low_to_high_prog', refines_to; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    eexists; repeat split; eauto.
    eapply exec_to_scp with (P := fun o s => refines_to s s2) in H; unfold refines_to in *; eauto.
    simpl in *; cleanup.
    repeat (split_ors; repeat (cleanup; simpl in *);
    try solve [ inversion H; cleanup; eexists; eauto ]).
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
    destruct x1, s1.
    eapply exec_to_scp with (P := fun o s => refines_to s s2') in H0; unfold refines_to in *; eauto.
    simpl in *; cleanup.
    repeat (split_ors; repeat (cleanup; simpl in *);
    try solve [ inversion H0; cleanup; eexists; eauto ]).
  Qed.

  Lemma wp_low_to_high_write :
    forall a vl,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wp_low_to_high_prog'; intros; cleanup.
    simpl in H1; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H2; unfold refines_to in *; eauto.
    unfold write in *.
    simpl in *; cleanup.
    eexists; intuition eauto.
    unfold refines_to; eauto.
  Qed.

  Lemma wp_high_to_low_write :
    forall a vl,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wp_high_to_low_prog'; intros; cleanup.
    repeat invert_exec.
    simpl in H1; cleanup.
    repeat (split_ors; cleanup).
    eapply exec_to_wp; eauto.
    simpl; unfold refines_to.
    eexists; eauto.
    destruct x0; eauto.
  Qed.

  
  Lemma wcp_low_to_high_write :
    forall a vl,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wcp_low_to_high_prog'; intros; cleanup.
    simpl in H1; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    simpl; split_ors; cleanup;
    eexists; intuition eauto.
    right; intuition eauto.
    eapply exec_to_scp with (P := fun o s => refines_to s s2 /\ s = s1) in H2.
    2: unfold refines_to; eauto.
    admit. (* TODO: Check this *)
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
    admit. (* TODO: Check this *)
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
      - (* Write *)
        destruct s1'.
        + do 2 eexists; intuition eauto;
          right; eauto.
          eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; unfold refines_to in *; eauto.
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
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; unfold refines_to in *; eauto.
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
          eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; unfold refines_to in *; eauto.
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
