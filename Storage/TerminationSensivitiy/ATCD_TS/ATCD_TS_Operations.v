Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS.
Require Import ATCD_TS_Recovery ATCD_TS_Common.

Import FileDiskLayer.
Set Nested Proofs Allowed.
Opaque File.recover.


Lemma ATCD_TS_TransactionCache_get:
  forall n u V txns1 txns2 hdr1 hdr2,
  Termination_Sensitive u
  (Simulation.Definitions.compile
   ATCD_Refinement
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (Get (prod addr value))))))
(Simulation.Definitions.compile
     ATCD_Refinement
     (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (Get (prod addr value))))))
(Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement V) 
  (equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  invert_exec'' H9; repeat invert_exec.
  eexists (RFinished _ _); repeat econstructor.

  invert_exec'' H12;
  repeat invert_exec; simpl in *.
  
  edestruct ATCD_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  Unshelve.
  6: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
Qed.



Lemma ATCD_TS_TransactionCache_delete:
  forall n u V txns1 txns2 hdr1 hdr2,
  Termination_Sensitive u
  (Simulation.Definitions.compile
   ATCD_Refinement
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (ListLayer.Delete (prod addr value))))))
(Simulation.Definitions.compile
     ATCD_Refinement
     (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (ListLayer.Delete (prod addr value))))))
(Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement V) 
  (equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  invert_exec'' H9; repeat invert_exec.
  eexists (RFinished _ _); repeat econstructor.

  invert_exec'' H12;
  repeat invert_exec; simpl in *.
  
  edestruct ATCD_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  Unshelve.
  6: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
Qed.


Lemma ATCD_TS_LogCache_read:
  forall n u V txns1 txns2 hdr1 hdr2 a1 a2,
  (a1 < data_length <-> a2 < data_length) -> 
  Termination_Sensitive u
  (Simulation.Definitions.compile
   ATCD_Refinement
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ (LoggedDiskLayer.Read a1)))))
   (Simulation.Definitions.compile
     ATCD_Refinement
   (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ (LoggedDiskLayer.Read a2)))))
(Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  V 
  (fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (fst (snd (snd s1)) (data_start + a1) = None <-> fst (snd (snd s2)) (data_start + a2) = None))
(ATCD_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
   repeat invert_lift2.
   unfold LogCache.read in *.
   cleanup; repeat invert_exec.
   {
      destruct s2, s0;
      destruct_fresh (fst s2 (data_start + a2));
      eexists (RFinished _ _); repeat econstructor.
      simpl Simulation.Definitions.compile; repeat econstructor.
      simpl app; repeat eapply lift2_exec_step.
      unfold LogCache.read; 
      destruct (Compare_dec.lt_dec a2 data_length); try lia.
      rewrite cons_app; repeat econstructor.
      rewrite D0; repeat econstructor.
      simpl in *; apply i in D0; congruence.
   }
   {
      destruct s2, s0;
      eexists (RFinished _ _); repeat econstructor.
      simpl Simulation.Definitions.compile; repeat econstructor.
      simpl app; repeat eapply lift2_exec_step.
      unfold LogCache.read; 
      destruct (Compare_dec.lt_dec a2 data_length); try lia.
      rewrite cons_app; repeat econstructor.
      destruct_fresh (fst s2 (data_start + a2)).
      simpl in *; apply i in H16; congruence.
      repeat econstructor.
      rewrite data_fits_in_disk; lia.
   }
   {
      destruct s2, s0;
      eexists (RFinished _ _); repeat econstructor.
      simpl Simulation.Definitions.compile; repeat econstructor.
      simpl app; repeat eapply lift2_exec_step.
      unfold LogCache.read; 
      destruct (Compare_dec.lt_dec a2 data_length); try lia.
      rewrite cons_app; repeat econstructor.
   }
  }
  {
   repeat invert_lift2.
   unfold LogCache.read in *.
   cleanup; repeat invert_exec.
   {
      split_ors; cleanup; repeat invert_exec.
      {
         edestruct ATCD_TS_recovery.
         3: eauto.
         3: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
         3: repeat cleanup_pairs; eauto.
         all: try solve [unfold AD_valid_state, 
         refines_valid, FD_valid_state; 
         intros; simpl; eauto].

         eexists (Recovered _); econstructor; eauto.
         destruct s2, s0;
         simpl Simulation.Definitions.compile; repeat econstructor.
         simpl app; repeat eapply lift2_exec_step_crashed.
         unfold LogCache.read.
         destruct (Compare_dec.lt_dec a2 data_length); try lia.
         destruct s2;
         repeat econstructor.
      }
      {
         cleanup; repeat invert_exec.
         {
            edestruct ATCD_TS_recovery.
            3: eauto.
            3: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
            3: repeat cleanup_pairs; eauto.
            all: try solve [unfold AD_valid_state, 
            refines_valid, FD_valid_state; 
            intros; simpl; eauto].
            destruct_fresh (fst (snd (snd s2)) (data_start + a2)).

            eexists (Recovered _); econstructor; eauto.
            destruct s2, s0;
            simpl Simulation.Definitions.compile; repeat econstructor.
            simpl app; repeat eapply lift2_exec_step_crashed.
            unfold LogCache.read.
            destruct (Compare_dec.lt_dec a2 data_length); try lia.
            rewrite cons_app; repeat econstructor.
            simpl in *; rewrite D1; destruct s2; repeat econstructor.

            intuition; repeat cleanup_pairs; try congruence.
         }
         {
            edestruct ATCD_TS_recovery.
            3: eauto.
            3: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
            3: repeat cleanup_pairs; eauto.
            all: try solve [unfold AD_valid_state, 
            refines_valid, FD_valid_state; 
            intros; simpl; eauto].
            
            eexists (Recovered _); econstructor; eauto.
            destruct s2, s0;
            simpl Simulation.Definitions.compile; repeat econstructor.
            simpl app; repeat eapply lift2_exec_step_crashed.
            unfold LogCache.read.
            destruct (Compare_dec.lt_dec a2 data_length); try lia.
            rewrite cons_app; repeat econstructor.
            repeat cleanup_pairs; intuition.
            simpl in *; rewrite H4; repeat econstructor.
         }
      }
   }
   {
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: simpl; eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      destruct s2, s0;
      simpl Simulation.Definitions.compile; repeat econstructor.
      simpl app; repeat eapply lift2_exec_step_crashed.
      unfold LogCache.read.
      destruct (Compare_dec.lt_dec a2 data_length); try lia.
      destruct s2;
      repeat econstructor.
   }
  }
  Unshelve.
  all: eauto.
  all: exact ATCDLang.
Qed.

Lemma ATCD_TS_Disk_read:
  forall n u a1 a2 txns1 txns2 hdr1 hdr2,
  (a1 < disk_size <-> a2 < disk_size) ->
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Read a1)))))
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Read a2)))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        ATC_Refinement File.recover))
  (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
        AD_valid_state))
  (equivalent_for_recovery txns1 txns2
     Log.Current_Part hdr1 hdr2)
  (ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
  invert_exec'' H10; repeat invert_exec.
   eexists (RFinished _ _).
   repeat econstructor; eauto.
   apply H; eauto.
   }
   {
      invert_exec'' H13; repeat invert_exec.
      simpl in *.
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      repeat econstructor.
      simpl; eauto.
   }
Qed.

Lemma ATCD_TS_Cache_flush:
  forall n u txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(Op (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
(@P1 (CacheOperation addr_dec value) CryptoDiskOperation _ (Flush addr value)))))
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(Op (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
(@P1 (CacheOperation addr_dec value) CryptoDiskOperation _ (Flush addr value)))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        ATC_Refinement File.recover))
  (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
        AD_valid_state))
  (equivalent_for_recovery txns1 txns2
     Log.Current_Part hdr1 hdr2)
  (ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
  invert_exec'' H9; repeat invert_exec.
   eexists (RFinished _ _).
   repeat econstructor; eauto.
  }
   {
      invert_exec'' H12; repeat invert_exec.
      simpl in *.
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      repeat econstructor.
      simpl; eauto.
   }
Qed.

Lemma ATCD_TS_Disk_write:
  forall n u a1 a2 v1 v2 txns1 txns2 hdr1 hdr2,
  (a1 < disk_size <-> a2 < disk_size) ->
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Write a1 v1)))))
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Write a2 v2)))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        ATC_Refinement File.recover))
  (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
        AD_valid_state))
  (equivalent_for_recovery txns1 txns2
     Log.Current_Part hdr1 hdr2)
  (ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
  invert_exec'' H10; repeat invert_exec.
   eexists (RFinished _ _).
   repeat econstructor; eauto.
   apply H; eauto.
   }
   {
      invert_exec'' H13; repeat invert_exec.
      simpl in *.
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      repeat econstructor.
      simpl; eauto.
   }
Qed.

Lemma ATCD_TS_Disk_sync:
  forall n u txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Sync)))))
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|DO| (DiskLayer.Sync)))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        ATC_Refinement File.recover))
  (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
        AD_valid_state))
  (equivalent_for_recovery txns1 txns2
     Log.Current_Part hdr1 hdr2)
  (ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
  invert_exec'' H9; repeat invert_exec.
   eexists (RFinished _ _).
   repeat econstructor; eauto.
   }
   {
      invert_exec'' H12; repeat invert_exec.
      simpl in *.
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      repeat econstructor.
      simpl; eauto.
   }
Qed.


Lemma ATCD_TS_Crypto_getkey:
  forall n u txns1 txns2 hdr1 hdr2 lo s1 s2,
Termination_Sensitive_explicit u lo s1 s2
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|CO| GetKey))))
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _ 
(@lift_L2 _ _ CryptoDiskLang _ 
(|CO| GetKey))))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        ATC_Refinement File.recover))
  (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
        AD_valid_state))
  (fun s1 s2 => equivalent_for_recovery txns1 txns2
     Log.Current_Part hdr1 hdr2 s1 s2 /\
     (forall t,
    In (OpToken ATCDCore (Token2 AuthenticationOperation TCDCore
       (Token2 (ListOperation (addr * value)) (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation) 
    (Token2 (CacheOperation addr_dec value) CryptoDiskOperation 
    (Token1 CryptoOperation 
    (DiskOperation addr_dec value (fun a => a < disk_size)) (Key t)))))) 
    (seln lo 0 []) ->
     ~ In t (fst (fst (fst (snd (snd (snd s1)))))) ->
       ~ In t (fst (fst (fst (snd (snd (snd s2))))))))
  (ATCD_reboot_list n).
Proof.
   unfold Termination_Sensitive_explicit, ATCD_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
  invert_exec'' H9; repeat invert_exec.
   eexists (RFinished _ _).
   repeat econstructor; eauto.
   cleanup; eauto.
   apply H2; eauto.
   simpl; intuition.
   }
   {
      invert_exec'' H12; repeat invert_exec.
      simpl in *.
      edestruct ATCD_TS_recovery.
      3: eauto.
      3: eapply equivalent_for_recovery_after_reboot; eauto.
      3: repeat cleanup_pairs; eauto.
      all: try solve [unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto].

      eexists (Recovered _); econstructor; eauto.
      destruct s2, s0, s2, s3. repeat econstructor.
   }
Qed.


Lemma ATCD_TS_Authentication_auth:
forall u u1 u2 n V txns1 txns2 hdr1 hdr2,
Termination_Sensitive u 
(Simulation.Definitions.compile
      ATCD_Refinement
(Op
   (HorizontalComposition AuthenticationOperation
      TransactionCacheOperation) 
      (@P1 AuthenticationOperation _ _ (Auth u1))))
(Simulation.Definitions.compile
      ATCD_Refinement
      (Op
   (HorizontalComposition AuthenticationOperation
      TransactionCacheOperation) 
      (@P1 AuthenticationOperation _ _ (Auth u2))))
(Simulation.Definitions.compile
      ATCD_Refinement
      (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
V (equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2) 
(ATCD_reboot_list n).
Proof.
 unfold Termination_Sensitive, ATCD_reboot_list;
 intros.
 destruct n; simpl in *.
 {
    repeat invert_exec.
    invert_exec'' H9; repeat invert_exec;
    destruct (user_dec u u2);
    eexists (RFinished _ _); try solve [repeat econstructor; eauto].
 }
 {
  repeat invert_exec.
  invert_exec'' H12; repeat invert_exec.
  simpl in *; edestruct ATCD_TS_recovery. 
  3: eauto.
  unfold refines_valid, AD_valid_state, 
  FD_valid_state, refines_valid; simpl; 
  intros; eauto.

  unfold refines_valid, AD_valid_state, 
  FD_valid_state, refines_valid; simpl; 
  intros; eauto.
  simpl; eapply equivalent_for_recovery_after_reboot; eauto.
  eexists (Recovered _); repeat econstructor; eauto.
 }
Qed.
