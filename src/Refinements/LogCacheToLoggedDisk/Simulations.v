Require Import Framework TotalMem FSParameters CachedDiskLayer.
Require Import Log Log.RepImplications Specs LogCache LoggedDiskLayer.
Require Import LogCacheToLoggedDisk.Definitions LogCacheToLoggedDisk.AbstractOracles.
Require Import ClassicalFacts FunctionalExtensionality Lia.

Set Nested Proofs Allowed.

Local Notation "'imp'" := CachedDiskLang.
Local Notation "'abs'" := (LoggedDiskLang log_length data_length).
Local Notation "'refinement'" := LoggedDiskRefinement.

  Lemma ext_or_take_out:
    forall A P Q R,
      (exists a: A, P a) \/ (exists a: A, Q a) \/ (exists a : A, R a)->
      exists a: A, P a \/ Q a \/ R a.
  Proof.
    intros; intuition (cleanup; eauto).
  Qed.

  
  
Lemma recovery_simulation :
  forall l_selector u,
    SimulationForProgramGeneral _ _ _ _ refinement u _ (|Recover|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector))
                         refines_reboot refines.
Proof.
  unfold SimulationForProgramGeneral; induction l_selector; simpl; intros; cleanup.
  {
    destruct l_o_imp; intuition; simpl in *.
    cleanup; try tauto.
    invert_exec; simpl in *; cleanup; try tauto.
    cleanup; intuition eauto; cleanup; 
    repeat unify_execs; cleanup.


    specialize (H2 (fun s => s)); cleanup.
    cleanup; intuition eauto; cleanup; 
    repeat unify_execs; cleanup.
    
    eexists; split; eauto.
    unfold logged_disk_reboot_list in *; simpl.
    instantiate (1:= RFinished s_abs tt). 
    repeat econstructor.
    unfold refines, refines_reboot in *;
    simpl in *; cleanup; eauto.
  }
  {
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; intuition eauto; repeat (unify_execs; cleanup).
    cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
    edestruct IHl_selector; eauto.
    instantiate (1:= s_abs).
    all: eauto.
    unfold refines_reboot in *; logic_clean.
    eapply_fresh recover_crashed in H11; eauto.
    cleanup; simpl in *; split; eauto.
    unfold cached_log_reboot_rep in *; cleanup.

    eapply ext_or_take_out in H2.
    cleanup.
    exists x0.
    simpl; split.
    cleanup; repeat split_ors;
    simpl in *; cleanup;
    try eapply reboot_rep_to_reboot_rep in H2;
    try eapply crash_rep_recover_to_reboot_rep in H2;
    try eapply log_rep_to_reboot_rep in H2;
    intuition eauto.
     
    assert (A: (map addr_list x0) = (map (map (Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x0)))). {
        rewrite map_map.
        setoid_rewrite map_ext_in at 2.
        rewrite map_id; eauto.
        intros.
        rewrite map_map.
        setoid_rewrite map_ext_in.
        rewrite map_id; eauto.
        intros; simpl.
        unfold log_rep, log_rep_general, log_crash_rep,
        log_reboot_rep, log_rep_explicit,
        log_rep_inner, txns_valid in *.
        simpl in *; logic_clean.
        repeat split_ors; cleanup;
        match goal with
        | [H: Forall (txn_well_formed _ _ _ _ _) _,
              H0: In _ (map _ _) |- _] =>
          apply in_map_iff in H0; logic_clean; subst;
          eapply Forall_forall in H; eauto;
          unfold txn_well_formed in H; logic_clean
        end;
        match goal with
        |[H: Forall (fun _ => _ > _ /\ _ >= _) _ |- _] =>
         eapply Forall_forall in H; eauto
        end;
        lia.
      }
      simpl.
      rewrite A.
      rewrite shift_list_upd_batch_set_comm.
      rewrite <- shift_select_total_mem_comm.
      rewrite select_total_mem_synced_noop.
      rewrite <- shift_list_upd_batch_set_comm.
      setoid_rewrite <- A; eauto.
      repeat split_ors; logic_clean; eauto;
      
      repeat rewrite total_mem_map_shift_comm in *;
      rewrite <- sync_list_upd_batch_set in H6;
      rewrite total_mem_map_fst_sync_noop in H6;
      eauto.
      
      {
        unfold sumbool_agree; intros.
        destruct (addr_dec x2 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
      }
      {
        intros.
        rewrite shift_some in H6.
        split_ors;
        rewrite H4 in H6; eauto.
        lia.
        unfold sync in H6.
        destruct_fresh (snd (snd s_imp) (data_start + a0));
        setoid_rewrite D in H6; inversion H6; simpl; eauto.
        lia.
      }
      {
        unfold sumbool_agree; intros.
        destruct (addr_dec x2 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
      }
      simpl in *.
      intros.
      eapply select_total_mem_synced in H6; eauto.
      
      simpl in *; logic_clean.
      exists (Recovered (extract_state_r x)).
      unfold logged_disk_reboot_list in *; simpl in *.
      econstructor.
      repeat econstructor; eauto.
      eauto.
  }
Qed. 

Lemma read_simulation :
  forall a l_selector u,
    SimulationForProgram refinement u (|Read a|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      specialize (H3 (fun s => s)); cleanup.
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      eapply_fresh read_finished in H10; cleanup; eauto.
      destruct l_selector; simpl in *; try congruence; cleanup.
      unfold logged_disk_reboot_list; simpl.
      split_ors; cleanup.
      {
        exists (RFinished s_abs (s_abs a));
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
      {
        exists (RFinished s_abs value0);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
    }
    {
      
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct l_selector; simpl in *; try congruence; cleanup.
      eapply_fresh read_crashed in H9; cleanup.
      
      edestruct recovery_simulation; eauto.
      unfold refines in *.
      apply H5 in H0.
      unfold refines_reboot; simpl.
      instantiate (1:= s_abs).
      unfold cached_log_rep, cached_log_reboot_rep in *; cleanup.
      eapply_fresh log_rep_to_reboot_rep in H1.
      intuition eauto.
      eexists; intuition eauto.
      simpl; eauto.

      unfold log_rep, log_reboot_rep, log_rep_general in *.
      logic_clean.
      setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
      rewrite shift_list_upd_batch_set_comm; eauto.
      rewrite shift_select_total_mem_synced.      
      repeat rewrite <- shift_list_upd_batch_set_comm.        
      repeat erewrite <- map_addr_list_eq_map_map; eauto.
      
      all: try apply sumbool_agree_addr_dec.
      intros; apply H6; lia.
      apply select_total_mem_synced in H4; eauto.
      repeat unify_execs; cleanup; eauto.
      repeat unify_execs; cleanup; eauto.
      exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
      unfold logged_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Qed.

Lemma write_simulation :
  forall l_a l_v l_selector u,
    SimulationForProgram refinement u (|Write l_a l_v|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;    
    unify_execs; cleanup].
    {
      specialize (H3 (fun s=> s)).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      unfold refines in *; cleanup.
      specialize H5 with (1:= H0).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      {
        eapply write_finished in H10; eauto.
        destruct l_selector; simpl in *; try congruence; cleanup.
        unfold logged_disk_reboot_list; simpl.
        split_ors; cleanup.
        {
          exists (RFinished s_abs tt);
          simpl; split; eauto.
          eapply ExecFinished.
          do 2 econstructor; eauto.
          clear H5.
          intuition eauto.
          erewrite addr_list_to_blocks_length_eq; eauto.
          rewrite map_length; eauto.
          destruct x3; eauto.
        }
      {
        clear H5. 
        exists (RFinished (upd_batch s_abs l_a l_v) tt);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
        rewrite map_length; eauto.
        destruct x3; eauto.
      }
    }
    {
      split_ors; cleanup;
      try unify_execs; cleanup;
      destruct l_selector; simpl in *; try congruence; cleanup.
      split_ors; cleanup;
      try unify_execs; cleanup;
      destruct l_selector; simpl in *; try congruence; cleanup.
    }
    }
    {
      unfold refines in *.
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct l_selector; simpl in *; try congruence; cleanup.
    
      specialize H4 with (1:= H0).
      repeat split_ors; cleanup; try unify_execs; cleanup.
      {
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup.
        {
          repeat unify_execs; cleanup.
          unfold cached_log_rep in *; cleanup.
          repeat split_ors; cleanup.          
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_reboot, cached_log_reboot_rep; simpl.
            split.
            eapply log_rep_to_reboot_rep in H4.
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H8; eauto.
          }
          {
          exists (Recovered (extract_state_r x2)); simpl; intuition eauto.        
          unfold logged_disk_reboot_list; simpl.
          eapply ExecRecovered.
          repeat econstructor.
          unfold refines, cached_log_rep in *; cleanup.
          unfold log_rep, log_reboot_rep, log_rep_general in *.
          logic_clean.
          erewrite map_addr_list_eq_map_map; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          erewrite <- shift_select_total_mem_synced.      
          repeat rewrite <- shift_list_upd_batch_set_comm.        
          repeat erewrite <- map_addr_list_eq_map_map; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          intros; apply H7; lia.
          }
        { (** During Apply Case **)
          unfold cached_log_crash_rep in *; cleanup.
          split_ors.
          {
            cleanup.
            eapply crash_rep_apply_to_reboot_rep in H2.
            repeat split_ors; edestruct recovery_simulation; eauto;
            try solve [eapply H3; eauto].
            {
              unfold refines_reboot, cached_log_reboot_rep; simpl.          
              split.          
              eexists; intuition eauto.
              intros.
              apply select_total_mem_synced in H10; eauto.
            }
            {
              exists (Recovered (extract_state_r x2)); simpl; intuition eauto.        
              unfold logged_disk_reboot_list; simpl.
              eapply ExecRecovered.
              repeat econstructor.
              assert (A: total_mem_map fst
              (shift (Nat.add data_start)
                 (list_upd_batch_set (snd (snd x1)) (map addr_list x0)
                    (map data_blocks x0))) =
                    total_mem_map fst
          (shift (Nat.add data_start)
             (list_upd_batch_set (select_total_mem t (snd (snd x1)))
                (map addr_list x0) (map data_blocks x0)))). {
              
              unfold refines, cached_log_rep in *; cleanup.
              unfold log_rep, log_reboot_rep, log_rep_general in *.
              logic_clean.
              
              rewrite <- H7.
              
              repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 extensionality a.
                 unfold shift; simpl.
                 destruct (list_list_in_EXM addr_dec (map addr_list x0) (data_start + a)); 
                 try logic_clean.
                 eapply list_upd_batch_in; eauto.
                 eexists; split; eauto.
                 apply in_seln; eauto.

                 apply forall_forall2.
                 apply Forall_forall; intros.
                 rewrite <- combine_map in H21.
                 apply in_map_iff in H21; logic_clean.
                 unfold log_rep_explicit, log_rep_inner,
                 txns_valid in *; logic_clean.
                 eapply Forall_forall in H38; eauto.
                 unfold txn_well_formed in H38; logic_clean; eauto.
                 destruct x15; simpl in *.
                 inversion H21; subst.
                 rewrite H49, <- H53, firstn_length_l; eauto. 
                 repeat rewrite map_length; eauto.
                 
                 repeat rewrite list_upd_batch_not_in; eauto.
                 unfold total_mem_map, select_total_mem.
                 rewrite select_for_addr_synced; simpl; eauto.
                 eapply H8 ; eauto.
                 lia.
                }
                setoid_rewrite <- H7.
                setoid_rewrite A; eauto.
            }
            {
              unfold refines_reboot, cached_log_reboot_rep; simpl.          
              split.
              eexists; intuition eauto.
              intros.
              apply select_total_mem_synced in H10; eauto.
            }
            {
              exists (Recovered (extract_state_r x2)); simpl; intuition eauto.        
              unfold logged_disk_reboot_list; simpl.
              eapply ExecRecovered.
              repeat econstructor.
              simpl in *; eauto.

              assert (A: total_mem_map fst
              (shift (Nat.add data_start)
                 (snd (snd x1))) =
                    total_mem_map fst
          (shift (Nat.add data_start) (select_total_mem t (snd (snd x1)))
                )). {
              
              unfold refines, cached_log_rep in *; cleanup.
              unfold log_rep, log_reboot_rep, log_rep_general in *.
              logic_clean.

              repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 extensionality a.
                 unfold shift; simpl.

                 repeat rewrite list_upd_batch_not_in; eauto.
                 unfold total_mem_map, select_total_mem.
                 rewrite select_for_addr_synced; simpl; eauto.
                 eapply H8; eauto.
                 lia.
                }
                setoid_rewrite A; eauto.
            }
          }
          {
            eapply log_rep_to_reboot_rep in H2.
            repeat split_ors; edestruct recovery_simulation; eauto;
            try solve [eapply H3; eauto].
            {
              unfold refines_reboot, cached_log_reboot_rep; simpl.          
              split.          
              eexists; intuition eauto.
              intros.
              apply select_total_mem_synced in H7; eauto.
            }
            {
              
              exists (Recovered (extract_state_r x2)); simpl; intuition eauto.        
              unfold logged_disk_reboot_list; simpl.
              eapply ExecRecovered.
              repeat econstructor.
              assert (A: total_mem_map fst
              (shift (Nat.add data_start)
                 (list_upd_batch_set (snd (snd x1)) (map addr_list x0)
                    (map data_blocks x0))) =
                    total_mem_map fst
          (shift (Nat.add data_start)
             (list_upd_batch_set (select_total_mem t (snd (snd x1)))
                (map addr_list x0) (map data_blocks x0)))). {
              
              unfold refines, cached_log_rep in *; cleanup.
              unfold log_rep, log_reboot_rep, log_rep_general in *.
              logic_clean.
              (* rewrite <- H13. *)

              repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 extensionality a.
                 unfold shift; simpl.
                 destruct (list_list_in_EXM addr_dec (map addr_list x0) (data_start + a)); 
                 try logic_clean.
                 eapply list_upd_batch_in; eauto.
                 eexists; split; eauto.
                 apply in_seln; eauto.

                 apply forall_forall2.
                 apply Forall_forall; intros.
                 rewrite <- combine_map in H19.
                 apply in_map_iff in H19; logic_clean.
                 unfold log_rep_explicit, log_rep_inner,
                 txns_valid in *; logic_clean.
                 eapply Forall_forall in H36; eauto.
                 unfold txn_well_formed in H36; logic_clean; eauto.
                 destruct x15; simpl in *.
                 inversion H19; subst.
                 rewrite H47, <- H51, firstn_length_l; eauto. 
                 repeat rewrite map_length; eauto.
                 
                 repeat rewrite list_upd_batch_not_in; eauto.
                 unfold total_mem_map, select_total_mem.
                 rewrite select_for_addr_synced; simpl; eauto.
                 eapply H6; eauto.
                 lia.
                 intros; logic_clean; eauto.
                 eapply H16; eauto.
                }
                setoid_rewrite A; eauto.
            }
          }        
        }
        {
          unfold cached_log_crash_rep in H2; cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_reboot, cached_log_reboot_rep; simpl.          
            split.          
            eapply log_rep_to_reboot_rep in H2.
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H7; eauto.
          }
          {
            exists (Recovered (extract_state_r x0)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl in *.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines, cached_log_rep in *; simpl in *; cleanup; eauto.
            (* rewrite <- H4; eauto. *)
            erewrite <- shift_select_total_mem_synced; eauto.
            intros; apply H6; lia.
          }
        }
      }        
      {(** After Commit case **)
        (* specialize H4 with (1:= H0). *)
        unfold cached_log_crash_rep in *; cleanup.
        edestruct recovery_simulation; eauto;
        try solve [eapply H3; eauto].
        {
          unfold refines_reboot, cached_log_reboot_rep; simpl.          
          split.          
          eapply log_rep_to_reboot_rep in H1.
          eexists; intuition eauto.
          apply select_total_mem_synced; eauto.
        }
        {
          exists (Recovered (extract_state_r x0)); simpl; intuition eauto.        
          unfold logged_disk_reboot_list; simpl.
          eapply ExecRecovered.
          repeat econstructor; eauto.
          unfold refines, cached_log_rep in *; simpl in *; cleanup; eauto.
          setoid_rewrite H2; eauto.
          {
            unfold log_rep, log_rep_general in H1.
            assert (A: total_mem_map fst
              (shift (Nat.add data_start)
                 (list_upd_batch_set (snd (snd x1)) (map addr_list x)
                    (map data_blocks x))) =
                    total_mem_map fst
          (shift (Nat.add data_start)
             (list_upd_batch_set (select_total_mem t (snd (snd x1)))
                (map addr_list x) (map data_blocks x)))). {
              
              unfold refines, cached_log_rep in *; cleanup.
              unfold log_rep, log_reboot_rep, log_rep_general in *.
              logic_clean.
              repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 extensionality a.
                 unfold shift; simpl.
                 destruct (list_list_in_EXM addr_dec (map addr_list x) (data_start + a)); 
                 try logic_clean.
                 eapply list_upd_batch_in; eauto.
                 eexists; split; eauto.
                 apply in_seln; eauto.

                 apply forall_forall2.
                 apply Forall_forall; intros.
                 rewrite <- combine_map in H22.
                 apply in_map_iff in H22; logic_clean.
                 unfold log_rep_explicit, log_rep_inner,
                 txns_valid in *; logic_clean.
                 eapply Forall_forall in H39; eauto.
                 unfold txn_well_formed in H39; logic_clean; eauto.
                 destruct x14; simpl in *.
                 inversion H22; subst.
                 rewrite H50, <- H54, firstn_length_l; eauto. 
                 repeat rewrite map_length; eauto.
                 
                 repeat rewrite list_upd_batch_not_in; eauto.
                 unfold total_mem_map, select_total_mem.
                 rewrite select_for_addr_synced; simpl; eauto.
                 eapply H4; eauto.
                 lia.
                }
                setoid_rewrite A; eauto.
          }
        }
      }
      {
        (* specialize H2 with (1:= H0); cleanup. *)
        split_ors; cleanup.
        
        {
          unfold cached_log_reboot_rep in *; simpl in *;
          cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_reboot, cached_log_reboot_rep; simpl.
            split.       
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H4; eauto.
          }
          {
            exists (Recovered (extract_state_r x0)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines, cached_log_rep in *; simpl in *; cleanup; eauto.
          }
        }        
        {(** During Commit case **)
          unfold cached_log_reboot_rep in *; simpl in *;
          cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_reboot, cached_log_reboot_rep; simpl.          
            split.       
            eexists; intuition eauto.
            eapply select_total_mem_synced; eauto.
          }
          {
            exists (Recovered (extract_state_r x0)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor; eauto. 
            unfold refines, cached_log_rep in *; simpl in *; cleanup; eauto.
            setoid_rewrite H4; eauto.
            }
          }
      }
    }
  }
Qed.


