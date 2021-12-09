Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS.
Require Import ATCD_TS_Recovery ATCD_TS_Common ATCD_TS_Operations.

Import FileDiskLayer.
Set Nested Proofs Allowed.
Opaque File.recover.


Lemma ATCD_TS_BatchOperations_encrypt_all:
  forall n u k l1 l2 txns1 txns2 hdr1 hdr2,
  length l1 = length l2 ->
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
  (@lift_L2 _ _ CachedDiskLang _
     (|CDDP| BatchOperations.encrypt_all k l1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
     (@lift_L2 _ _ CachedDiskLang _
        (|CDDP| BatchOperations.encrypt_all k l2)))
   (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement AD_valid_state)) 
  (fun s1 s2 => equivalent_for_recovery txns1 txns2
  Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall x, 
  consistent_with_upds (snd (fst (snd (snd (snd s1))))) (firstn x (map (encrypt k) l1)) (firstn x (map (fun v => (k, v)) l1)) ->
  consistent_with_upds (snd (fst (snd (snd (snd s2))))) (firstn x (map (encrypt k) l2)) (firstn x (map (fun v => (k, v)) l2))))
(ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
   intros; destruct n;
   repeat invert_exec.
   {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.

      eapply_fresh BatchOperations.encrypt_all_finished in H8; cleanup; eauto.
      eapply BatchOperations_TS_encrypt_all in H8; eauto; cleanup.
      eexists (RFinished _ _).
      repeat econstructor; eauto.
      repeat eapply lift2_exec_step; eauto.
      specialize (c (length l1)).
      do 4 rewrite firstn_oob in c.
      simpl in *.
      eapply c; eauto.
      all: repeat rewrite map_length; lia.
    }
    {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.

      eapply_fresh BatchOperations.encrypt_all_crashed in H8; cleanup.
      eapply BatchOperations_TS_encrypt_all_crashed in H8; eauto; cleanup.
      eapply_fresh BatchOperations.encrypt_all_crashed in H8; cleanup.
      repeat cleanup_pairs.
      simpl in *.
       edestruct ATCD_TS_recovery.
       3: eauto.
       3: shelve. (* eapply equivalent_for_recovery_after_reboot; eauto. *)
 
       3: {
          eexists (Recovered _); econstructor; eauto.
      repeat eapply lift2_exec_step_crashed; eauto.
      }

      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].
    }
    Unshelve.
    all: try exact ATCDLang.
    6: {
      unfold equivalent_for_recovery in *; simpl in *;
      cleanup.
      eexists (_, (_, _)), (_, (_,_)); split.
      simpl; intuition eauto.
      rewrite e2 in *;
      do 2 eexists; intuition eauto.
      eapply RepImplications.log_rep_explicit_after_reboot in l0; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
      eapply select_total_mem_synced in H3; eauto.
      
      simpl. split.
      repeat split.
      do 2 eexists; split.
      eapply RepImplications.log_rep_explicit_after_reboot in l; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
      all: intuition eauto.
      eapply select_total_mem_synced in H3; eauto.
    }
Qed.

Lemma ATCD_TS_BatchOperations_hash_all:
  forall n u l1 l2 h1 h2 txns1 txns2 hdr1 hdr2,
  length l1 = length l2 ->
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
  (@lift_L2 _ _ CachedDiskLang _
     (|CDDP| BatchOperations.hash_all h1 l1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
     (@lift_L2 _ _ CachedDiskLang _
        (|CDDP| BatchOperations.hash_all h2 l2)))
   (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement AD_valid_state)) 
  (fun s1 s2 => equivalent_for_recovery txns1 txns2
  Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall x,
  consistent_with_upds (snd (fst (fst (snd (snd (snd s1)))))) 
  (firstn x (rolling_hash_list h1 l1))
  (firstn x (combine (h1 :: rolling_hash_list h1 l1) l1)) ->
  consistent_with_upds (snd (fst (fst (snd (snd (snd s2)))))) 
  (firstn x (rolling_hash_list h2 l2))
  (firstn x (combine (h2 :: rolling_hash_list h2 l2) l2))))
(ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
   intros; destruct n;
   repeat invert_exec.
   {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.
      eapply BatchOperations_TS_hash_all in H8; eauto; cleanup.
      eexists (RFinished _ _).
      repeat econstructor; eauto.
      repeat eapply lift2_exec_step; eauto.
      eapply BatchOperations.hash_all_finished in H8; cleanup; eauto.
      specialize (c (length l1)).
      do 4 rewrite firstn_oob in c.
      apply c; eauto.
      all: repeat rewrite combine_length; try lia.

      

      all: rewrite rolling_hash_list_length; lia.
    }
    {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.
      eapply_fresh BatchOperations_TS_hash_all_crashed in H8; eauto; cleanup.
      eapply BatchOperations.hash_all_crashed in H8; cleanup.
      eapply_fresh BatchOperations.hash_all_crashed in H2; cleanup.
      repeat cleanup_pairs.
      simpl in *.
       edestruct ATCD_TS_recovery.
       3: eauto.
       3: shelve. (* eapply equivalent_for_recovery_after_reboot; eauto. *)
       3: {
         eexists (Recovered _); econstructor; eauto.
         repeat eapply lift2_exec_step_crashed; eauto.
       }
       (* 3: repeat cleanup_pairs; eauto. *)
       all: try solve [unfold AD_valid_state, 
       refines_valid, FD_valid_state; 
       intros; simpl; eauto].
    }
    Unshelve.
    all: try exact ATCDLang.
    6: {
      unfold equivalent_for_recovery in *; simpl in *;
      cleanup_no_match.
      eexists (_, (_, _)), (_, (_,_)); split.
      simpl; intuition eauto.
      rewrite e2 in *;
      do 2 eexists; intuition eauto.
      eapply RepImplications.log_rep_explicit_after_reboot in l4; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
      eapply select_total_mem_synced in H4; eauto.
      
      simpl. split.
      repeat split.
      do 2 eexists; split.
      eapply RepImplications.log_rep_explicit_after_reboot in l3; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
      all: intuition eauto.
      eapply select_total_mem_synced in H4; eauto.
    }
Qed.


Lemma ATCD_TS_BatchOperations_write_batch:
  forall n u la1 la2 lv1 lv2 txns1 txns2 hdr1 hdr2,
  length la1 = length la2 ->
  length lv1 = length lv2 ->
  length la2 = length lv2 ->
  Forall (fun a => a < disk_size) la2 ->
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
  (@lift_L2 _ _ CachedDiskLang _
     (|CDDP| BatchOperations.write_batch la1 lv1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
     (@lift_L2 _ _ CachedDiskLang _
        (|CDDP| BatchOperations.write_batch la2 lv2)))
   (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement AD_valid_state)) 
  (equivalent_for_recovery txns1 txns2
  Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
   intros; destruct n;
   repeat invert_exec.
   {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.
      eapply BatchOperations_TS_write_batch in H12; cleanup.
      eexists (RFinished _ _).
      repeat econstructor; eauto.
      repeat eapply lift2_exec_step; eauto.
      all: eauto.
    }
    {
      repeat invert_lift2; cleanup.
      destruct s2, s0, s2, s3.
      eapply_fresh BatchOperations_TS_write_batch_crashed in H12; cleanup.
      eapply BatchOperations.write_batch_crashed in H12; cleanup.
      eapply_fresh BatchOperations.write_batch_crashed in H5; cleanup.
      simpl in *.
       edestruct ATCD_TS_recovery.
       3: eauto.
       3: shelve. (* eapply equivalent_for_recovery_after_reboot; eauto. *)
      3: { 
         eexists (Recovered _); econstructor; eauto.
      repeat eapply lift2_exec_step_crashed; eauto.
    }
    all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

    Unshelve.
    all: try exact ATCDLang.
    6: {
       (* probably need to add the fact that 
       it is written to the end of the log *)
      admit. (*
      unfold equivalent_for_recovery in *; simpl in *;
      cleanup_no_match.
      eexists (_, (_, _)), (_, (_,_)); split.
      simpl; intuition eauto.
      do 2 eexists; intuition eauto.

      Search Log.log_rep_explicit upd_batch_set.
      eapply RepImplications.log_rep_explicit_after_reboot in l4; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
      eapply select_total_mem_synced in H3; eauto.
      
      simpl. split.
      repeat split.
      do 2 eexists; split.
      eapply RepImplications.log_rep_explicit_after_reboot in l3; simpl in *.
      eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
      all: intuition eauto.
      eapply select_total_mem_synced in H3; eauto.
      *)
    }
Admitted.
