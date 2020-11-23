Require Import Framework FSParameters CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Lia.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.
Notation "'refinement'" := LoggedDiskRefinement.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.

  Definition cached_disk_reboot_list l_selector : list (low.(state) -> low.(state)) :=
    (map (fun selector (s: low.(state)) =>
            (empty_mem, (fst (snd s), select_mem selector (snd (snd s)))))
         l_selector).

  Definition logged_disk_reboot_list n := repeat (fun s : high.(state) => s) n.
  
Lemma recovery_simulation :
  forall l_selector,
    SimulationForProgramGeneral _ _ _ _ refinement _ (|Recover|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector))
                         refines_to_reboot refines_to.
Proof.
  unfold SimulationForProgramGeneral; induction l_selector; simpl; intros; cleanup.
  {
    destruct l_o_imp; intuition.
    cleanup; intuition.
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; intuition eauto;    
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    (** Need recover_finished here **)
    admit.
  }
  {
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; intuition eauto.
    eapply exec_deterministic_wrt_oracle in H10; eauto; cleanup.
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    edestruct IHl_selector.
    eapply H2; eauto.
    all: eauto.
    (** We need reboot_crashed here. **)
    admit.

    
    simpl in *; cleanup.
    exists (Recovered (extract_state_r x)).
    simpl; intuition eauto.
    
    unfold logged_disk_reboot_list; simpl.
    eapply ExecRecovered; eauto.
    repeat econstructor.
  }
Admitted.

Lemma read_simulation :
  forall a l_selector,
    SimulationForProgram refinement (|Read a|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;    
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup].
    {
      eapply exec_deterministic_wrt_oracle in H9; eauto; cleanup.
      (** Need read_finished here **)
      admit.
    }
    {
      eapply exec_deterministic_wrt_oracle in H8; eauto; cleanup.
    }
    {
      eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
      destruct l_selector; simpl in *; try congruence; cleanup.
      
      edestruct recovery_simulation; eauto.
      eapply H3; eauto.
      (** Need read_crashed here or refines_to -> refines_to_reboot **)
      admit.
      exists (Recovered (extract_state_r x)); simpl; intuition eauto.
      
      unfold logged_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Admitted.

Lemma write_simulation :
  forall l_a l_v l_selector,
    SimulationForProgram refinement (|Write l_a l_v|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;    
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup].
    {
      eapply exec_deterministic_wrt_oracle in H9; eauto; cleanup.
      (** Need write_finished here **)
      admit.
    }
    {
      split_ors; cleanup;
      eapply exec_deterministic_wrt_oracle in H9; eauto; cleanup.
    }
    {
      eapply exec_deterministic_wrt_oracle in H8; eauto; cleanup.
    }
    {
      split_ors; cleanup;
      eapply exec_deterministic_wrt_oracle in H8; eauto; cleanup;
      destruct l_selector; simpl in *; try congruence; cleanup.
      
      {
        edestruct recovery_simulation; eauto.
        eapply H3; eauto.
        (** Need write_crashed here or refines_to -> refines_to_reboot **)
        admit.
        exists (Recovered (extract_state_r x)); simpl; intuition eauto.
        
        unfold logged_disk_reboot_list; simpl.
        eapply ExecRecovered; eauto.
        repeat econstructor.
      }

      {
        edestruct recovery_simulation; eauto.
        eapply H3; eauto.
        (** Need write_crashed here or refines_to -> refines_to_reboot **)
        admit.
        exists (Recovered (extract_state_r x)); simpl; intuition eauto.
        
        unfold logged_disk_reboot_list; simpl.
        eapply ExecRecovered; eauto.
        (** Need something here **)
        admit.
      }
    }
Admitted.

Lemma wp_low_to_high_write :
  forall a vl,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
Proof.
  unfold wp_low_to_high_prog'; intros; cleanup.
  simpl in H1; intros; cleanup.
  split_ors; cleanup; simpl in *.
  {
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    eapply wp_to_exec in H; cleanup.
    eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    destruct x1.
    cleanup; eexists; intuition eauto.
    unfold refines_to in *; cleanup; eauto.
    Opaque Log.commit.
    unfold write in *; simpl in *.
    cleanup.
    {
      left; intuition eauto.
      admit. (** TODO: comes from successful exec *)
      
      edestruct H4; eauto.
      do 2 eexists; intuition eauto.
      apply upd_batch_write_all_mem_map; eauto.
      admit. (** TODO: comes from successful exec *)
    }
    {
      invert_exec.
      right; intuition eauto.
    }
    {
      invert_exec.
      right; intuition eauto.
    }
  }
  {
    split_ors; cleanup; simpl in *;
    eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
  }
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
  eapply wcp_to_exec in H; cleanup.
  try eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
 
  unfold write in *; simpl in *; cleanup;
  try solve [ invert_exec; intuition].

  repeat invert_exec; split_ors; cleanup.  
  admit. (** TODO: May be wrong *)
  
  cleanup; repeat (invert_exec; try split_ors; cleanup).
  admit.
  (** TODO: This needs checking *)  
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
