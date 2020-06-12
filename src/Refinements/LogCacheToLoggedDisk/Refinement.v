Require Import Framework FSParameters CachedDiskLayer.
Require Import LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := CachedDiskLang.
Notation "'high'" := LoggedDiskLang.
Notation "'refinement'" := LoggedDiskRefinement.

Axiom excluded_middle_dec: forall P: Prop, {P}+{~P}.

Section LoggedDiskBisimulation.

  Lemma sp_impl:
    forall T (p: prog low T) (P P': 
     list (Language.token' CachedDiskOperation) -> Operation.state CachedDiskOperation -> Prop) s' t,
      (forall o s, P' o s -> P o s) ->
      strongest_postcondition low p P' t s' ->
      strongest_postcondition low p P t s'.
  Proof.
    intros.
    eapply sp_to_exec in H0; cleanup.
    eapply exec_to_sp; eauto.
  Qed.

  Lemma sp_bind:
    forall T T' (p1: prog low T) (p2: T -> prog low T') P s' t,
      strongest_postcondition low (Bind p1 p2) P t s' ->
      exists s0 t0,
        strongest_postcondition low p1 (fun o s => exists o2, P (o++o2) s) t0 s0 /\
        strongest_postcondition low (p2 t0)
        (fun o s => strongest_postcondition low p1 (fun ox sx => P (ox++o) sx) t0 s0) t s'.
  Proof.
    intros.
    eapply sp_to_exec in H; cleanup.
    invert_exec.
    do 2 eexists; split.
    eapply exec_to_sp; eauto.
    intros.            
    repeat (eapply exec_to_sp; eauto).
  Qed.


  
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
        simpl in *; repeat (cleanup; simpl in *); eauto.

      eapply exec_to_scp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; repeat (try split_ors; cleanup; simpl in *); eauto;
      inversion H0; cleanup; eauto.
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
      simpl in *; cleanup; simpl; eauto.
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ s = s1) in H0; unfold refines_to in *; eauto.
      simpl in *; cleanup; simpl; eauto.
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
      fst s1 (data_start + a) = Some v ->
      Disk.read s2 a = Some v.
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    cleanup; unfold shift; simpl in *.
    eapply merge_some_l in H0; eauto; cleanup.
    rewrite H0; eauto.
    eapply H1.
    congruence.
  Qed.
  
  Lemma cached_log_rep_disk_read :
    forall F s2 s1 a,
      cached_log_rep F s2 s1 ->
      fst s1 (data_start + a) = None ->
      Disk.read s2 a = Disk.read (snd (snd s1)) (data_start + a).
  Proof.
    unfold cached_log_rep, Disk.read; intros.
    unfold shift in *; simpl; cleanup.
    erewrite merge_some_r; eauto.
  Qed.

  Lemma wp_low_to_high_read :
    forall a,
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wp_low_to_high_prog', refines_to; simpl; intros; cleanup.
    unfold refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H2; unfold refines_to in *; eauto.
    simpl in *.
    cleanup.
    {        
      cleanup; simpl in *; cleanup; eauto;
      eexists; intuition eauto.
      simpl in *.
      eapply cached_log_rep_cache_read; eauto.
      erewrite cached_log_rep_disk_read; eauto.
      unfold Disk.read in *; simpl; cleanup; eauto.
    }

    cleanup; simpl in *.
    {
      cleanup.
      eexists; split; eauto; simpl in *.
      unfold refines_to in *; cleanup.
      erewrite cached_log_rep_disk_read; eauto.
      unfold Disk.read in *; simpl; cleanup; eauto.
      split_ors; cleanup.
      eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
      eexists; intuition eauto.
      
    }
    {
      cleanup; eauto.
      eexists; intuition eauto.
      erewrite cached_log_rep_disk_read; eauto.      
      unfold Disk.read in *; simpl; cleanup; eauto.
    }
  Qed.

  Lemma wp_high_to_low_read :
    forall a,
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wp; eauto.

    eapply exec_to_sp with (P := fun o s => refines_to s s2' /\ s = s1) in H0; unfold refines_to in *; eauto.

    unfold read in *; simpl in *.
    cleanup; simpl in *.
    destruct x4; simpl in *; cleanup; eauto.
    - destruct x2; simpl in *; split; eauto.
      eapply cached_log_rep_cache_read in H0; eauto; cleanup.
      congruence.
      
    - destruct x2, s0; simpl in *; split; eauto.
      eapply cached_log_rep_disk_read in H0; eauto; cleanup.
      unfold Disk.read in *; simpl in *; cleanup; eauto.
      simpl in *; congruence.
  Qed.


  Lemma wcp_low_to_high_read :
    forall a,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Read a|).
  Proof.
    unfold wcp_low_to_high_prog', , refines_to; simpl; intros; cleanup.
    unfold  in *; simpl in *; intros; cleanup.
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
    unfold wcp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl in *; intros; cleanup.
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
    unfold wp_low_to_high_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl in *; intros; cleanup.
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
    unfold wp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl; intros; cleanup.
    repeat invert_exec.
    repeat (split_ors; cleanup).
    eapply exec_to_wp; eauto.
    eexists; eauto.
    destruct x3; eauto.
  Qed.

  
  Lemma wcp_low_to_high_write :
    forall a vl,
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wcp_low_to_high_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    split_ors; cleanup;
    eexists; intuition eauto.
    right; intuition eauto.
    eapply exec_to_scp with (P := fun o s => refines_to s s2 /\ s = s1) in H3.
    2: unfold refines_to; eauto.
    admit. (* TODO: Check this *)
  Admitted.

  Lemma wcp_high_to_low_write :
    forall a vl,
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (|Write a vl|).
  Proof.
    unfold wcp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl; intros; cleanup.
    repeat split_ors; cleanup; repeat invert_exec;
    eapply exec_to_wcp; eauto;
    split_ors; cleanup; eauto.
    admit. (* TODO: Check this *)
  Admitted.


  Lemma wp_low_to_high_ret :
    forall T (v: T),
    wp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wp_low_to_high_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    invert_exec; intuition eauto.
  Qed.

  Lemma wp_high_to_low_ret :
    forall T (v: T),
    wp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl; intros; cleanup.
    split_ors; cleanup.
    repeat invert_exec.
    eapply exec_to_wp; eauto.
    econstructor; eauto.
  Qed.

  Lemma wcp_low_to_high_ret :
    forall T (v: T),
    wcp_low_to_high_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wcp_low_to_high_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl in *; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    invert_exec; eauto.
  Qed.

  Lemma wcp_high_to_low_ret :
    forall T (v: T),
    wcp_high_to_low_prog' _ _ _ _ LoggedDiskRefinement _ (Ret v).
  Proof.
    unfold wcp_high_to_low_prog', , refines_to; simpl; intros; cleanup.
    unfold , refines_to in *; simpl in *; intros; cleanup.
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
    simpl in *; unfold  in *;
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
        simpl in *; unfold  in *;
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
           simpl in *; unfold  in *;
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
        simpl in *; unfold  in *;
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
           simpl in *; unfold  in *;
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
     T p1 p2 ->
    exists oh, oracle_refines_to T sl p2 ol oh.
Proof.
  unfold refines_to, ;
  induction p2; simpl; intros; cleanup.
  {
    destruct p; simpl in *.
    - (* Read *)
      destruct sl'; do 2 eexists; intuition eauto.
    - (* Write *)
      destruct sl'; try solve [do 2 eexists; intuition eauto].
      do 2 eexists; intuition eauto;
      right; eauto.
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = ol /\ s = sl) in H0 as Hx; unfold refines_to in *; eauto.
      do 2 eexists; intuition eauto.
      admit. (* Doable *)
      
    destruct (excluded_middle_dec (s = sl));
    do 2 eexists; intuition eauto;
    left; eauto.
  }  
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
      unfold ; eauto.
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
        unfold ; eauto.
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
