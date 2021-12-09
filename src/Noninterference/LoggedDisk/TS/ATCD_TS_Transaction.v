Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS.
Require Import ATCD_TS_Recovery ATCD_TS_Common ATCD_TS_Operations.
Require Import ATCD_TS_Log.

Import FileDiskLayer.
Set Nested Proofs Allowed.
Opaque File.recover.


(*
Functions
commit
   commit_txn - done with admits
   apply_log
      read_encrypted_log -Done
      flush_txns - done with admits
*)


Lemma ATCD_TS_LogCache_write:
  forall n u l_a1 l_a2 l_v1 l_v2 txns1 txns2 hdr1 hdr2 lo s1 s2,
  (NoDup l_a1 <-> NoDup l_a2) ->
  (length l_a1 = length l_v1 <-> length l_a2 = length l_v2) ->
   (Forall (fun a : nat => a < data_length) l_a1 <-> Forall (fun a : nat => a < data_length) l_a2) ->
   (length (addr_list_to_blocks l_a1) + length l_v1 <= log_length <-> length (addr_list_to_blocks l_a2) + length l_v2 <= log_length ) ->
   
   length (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1) =
length (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2) ->

(log_length <
Log.count (Log.current_part hdr1) +
(length (addr_list_to_blocks (map (Nat.add data_start) l_a1)) + length l_v1) <->
log_length <
Log.count (Log.current_part hdr2) +
(length (addr_list_to_blocks (map (Nat.add data_start) l_a2)) + length l_v2)) ->

  Termination_Sensitive_explicit u lo s1 s2
(@lift_L2 AuthenticationOperation _ TCDLang _
  (@lift_L2 _ _ CachedDiskLang _
     (LogCache.write l_a1 l_v1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
     (@lift_L2 _ _ CachedDiskLang _
        (LogCache.write l_a2 l_v2)))
   (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |))))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement AD_valid_state)) 
  (fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  equivalent_for_commit (seln lo 0 []) l_a1 l_v1 l_a2 l_v2 s1 s2)
(ATCD_reboot_list n).
Proof.
  unfold LogCache.write; intros.
  destruct (LogCache.Forall_dec (fun a : nat => a < data_length)
  (fun a : nat => Compare_dec.lt_dec a data_length) l_a1);
  destruct (LogCache.Forall_dec (fun a : nat => a < data_length)
  (fun a : nat => Compare_dec.lt_dec a data_length) l_a2); intuition.
  2:{ 
     eapply TS_explicit_to_TS; 
  eapply TS_eqv_impl.
  eapply ATCD_TS_ret.
  simpl; intuition eauto.
  }

  destruct (NoDup_dec l_a1);
  destruct (NoDup_dec l_a2); intuition.
  2:{ 
     eapply TS_explicit_to_TS; 
  eapply TS_eqv_impl. 
  eapply ATCD_TS_ret.
  simpl; intuition eauto.
  }
  destruct (PeanoNat.Nat.eq_dec (length l_a1) (length l_v1));
  destruct (PeanoNat.Nat.eq_dec (length l_a2) (length l_v2)); 
  intuition.
  2:{ 
     eapply TS_explicit_to_TS; 
  eapply TS_eqv_impl. 
  eapply ATCD_TS_ret.
  simpl; intuition eauto.
  }
  destruct (Compare_dec.le_dec
  (length (addr_list_to_blocks (map (Nat.add data_start) l_a1)) +
   length l_v1) log_length);
   destruct (Compare_dec.le_dec
   (length (addr_list_to_blocks (map (Nat.add data_start) l_a2)) +
    length l_v2) log_length); intuition.
  2: {
     erewrite addr_list_to_blocks_length_eq in l by (rewrite map_length; eauto).
     erewrite addr_list_to_blocks_length_eq in n2 by (rewrite map_length; eauto).
     lia.
   }
   2: {
     erewrite addr_list_to_blocks_length_eq in l by (rewrite map_length; eauto).
     erewrite addr_list_to_blocks_length_eq in n2 by (rewrite map_length; eauto).
     lia.
   }
   2:{ 
     eapply TS_explicit_to_TS; 
  eapply TS_eqv_impl. 
  eapply ATCD_TS_ret.
  simpl; intuition eauto.
  }

  simpl.
  eapply ATCD_TS_explicit_compositional.
   simpl.
  {
     intros; cleanup.
     eapply TS_explicit_eqv_impl.
     apply ATCD_TS_Log_commit; eauto.
     intuition eauto.
     cleanup; simpl.
     setoid_rewrite H7.
     intuition eauto.
     unfold equivalent_for_commit in *; cleanup.
     intuition eauto.
  }

   simpl; intros.
   repeat invert_lift2; cleanup.
   do 3 apply HC_map_ext_eq in H12; subst.
   eapply Log_commit_ret_eq in H26; eauto; subst.
   eapply ATCD_TS_explicit_compositional.
   simpl.
   {
      destruct r1; simpl.
      {
         intros. 
         eapply TS_explicit_to_TS; 
         eapply TS_eqv_impl. 
         eapply ATCD_TS_ret.
         shelve.
      }
      intros; eapply ATCD_TS_explicit_compositional.
      simpl.
      intros; eapply TS_explicit_to_TS; 
      eapply TS_eqv_impl. 
      eapply ATCD_TS_Log_apply_log.
      shelve.

      
      simpl; intros.
      repeat invert_lift2; cleanup.
      intros; eapply ATCD_TS_explicit_compositional.
      simpl; intros.
      eapply TS_explicit_to_TS;
      eapply TS_eqv_impl. 
      eapply ATCD_TS_Cache_flush.
      shelve.

      simpl; intros.
      repeat invert_lift2; cleanup.
      repeat invert_exec; cleanup.
      intros; eapply ATCD_TS_explicit_compositional.
      simpl; intros.
      eapply TS_explicit_eqv_impl.
      apply ATCD_TS_Log_commit; eauto.
      intuition eauto.
      cleanup; simpl.
      shelve.

      intros. 
      eapply TS_explicit_to_TS; 
      eapply TS_eqv_impl. 
      eapply ATCD_TS_ret.
      shelve.
      shelve.
      shelve.
      shelve.

      Unshelve.
      28: instantiate (5:= fun _ _ => equivalent_for_recovery _ _ Log.Current_Part _ _); simpl; eauto.
Admitted.



Lemma ATCD_TS_Transaction_read:
    forall n u a1 a2 txns1 txns2 hdr1 hdr2,
    (a1 < data_length <-> a2 < data_length) -> 
    Termination_Sensitive u
    (Simulation.Definitions.compile
        ATCD_Refinement
    (@lift_L2 AuthenticationOperation _ TransactionCacheLang _
        (Transaction.read a1)))
   (Simulation.Definitions.compile
        ATCD_Refinement
    (@lift_L2 AuthenticationOperation _ TransactionCacheLang  _
        (Transaction.read a2)))
   (Simulation.Definitions.compile
        ATCD_Refinement
        (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |))))
(refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement
     AD_valid_state))
  (fun s1 s2 =>
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (Transaction.get_first (fst (snd s1)) a1 = None <-> Transaction.get_first (fst (snd s2)) a2 = None) /\
  (fst (snd (snd s1)) (data_start + a1) = None <->
  fst (snd (snd s2)) (data_start + a2) = None) /\
  fst (snd (snd s1)) =
Mem.list_upd_batch empty_mem
  (map Log.addr_list txns1)
  (map Log.data_blocks txns1) /\
  fst (snd (snd s2)) =
Mem.list_upd_batch
  empty_mem
  (map Log.addr_list
     txns2)
  (map
     Log.data_blocks
     txns2))
  (ATCD_reboot_list n).
  Proof.
   Opaque LogCache.read.
    unfold Transaction.read; intros.
    destruct (Compare_dec.lt_dec a1 data_length);
    destruct (Compare_dec.lt_dec a2 data_length); try lia.

    intros.
    eapply ATCD_TS_compositional; simpl.
    intros; eapply TS_eqv_impl.
    intros; eapply ATCD_TS_TransactionCache_get.
    intros; cleanup; eauto.

    intros.
    cleanup.
    repeat invert_exec.
    destruct_fresh (Transaction.get_first (fst (snd s1)) a1);
    destruct_fresh (Transaction.get_first (fst (snd s2)) a2);
    try solve [intuition congruence].
    setoid_rewrite D;
    setoid_rewrite D0; simpl.
    eapply TS_eqv_impl.
    apply ATCD_TS_ret.
    shelve.
    apply H3 in D0; 
    setoid_rewrite D in D0; congruence.
    apply H3 in D; 
    setoid_rewrite D in D0; congruence.

    setoid_rewrite D;
    setoid_rewrite D0; simpl.
    eapply ATCD_TS_compositional; simpl; intros.
    eapply TS_eqv_impl.
    eapply ATCD_TS_LogCache_read; eauto.
    shelve.
    apply ATCD_TS_ret.
    shelve.
    shelve.
    eapply TS_eqv_impl. 
    apply ATCD_TS_ret.
    intuition eauto.
    Unshelve.
    17: {
       intros; repeat invert_exec.
       instantiate (1:= fun _ _ s1 s2 =>
       equivalent_for_recovery txns1
       txns2 Log.Current_Part hdr1
       hdr2 s1 s2 /\
     (Transaction.get_first
        (fst (snd s1)) a1 = None <->
      Transaction.get_first
        (fst (snd s2)) a2 = None) /\
     (fst (snd (snd s1))
        (data_start + a1) = None <->
      fst (snd (snd s2))
        (data_start + a2) = None) /\
        fst
       (snd (snd s1)) =
     Mem.list_upd_batch
       empty_mem
       (map
          Log.addr_list
          txns1)
       (map
          Log.data_blocks
          txns1) /\
          fst (snd (snd s2)) =
Mem.list_upd_batch
  empty_mem
  (map Log.addr_list
     txns2)
  (map
     Log.data_blocks
     txns2)); simpl; eauto.
    }
    5: simpl; intuition eauto.
    5: simpl; intuition eauto.
    5: {
       simpl in *; repeat invert_lift2.
       unfold equivalent_for_recovery in *; simpl in *.
       cleanup.
       eapply LogCache.read_finished in H15; eauto.
       eapply LogCache.read_finished in H19; eauto.
       cleanup.
       clear H0 H15.
       instantiate (1:= txns2).
       instantiate (1:= txns1).
       instantiate (1:= hdr2).
       instantiate (1:= hdr1).
       eexists (_, (_, _)), (_, (_, _)); simpl; intuition eauto.
       do 2 eexists; split; [eauto|].
       intros; congruence.
       do 2 eexists; split; [eauto|].
       intros; congruence.

       clear H15.
       unfold LogCache.cached_log_rep, Log.log_rep, Log.log_header_rep,
       Log.log_rep_general .
       eexists; intuition eauto.

       unfold LogCache.cached_log_rep, Log.log_rep, Log.log_header_rep,
       Log.log_rep_general .
       eexists; intuition eauto.
    }
Qed.


  Lemma ATCD_TS_abort:
   forall n u txns1 txns2 hdr1 hdr2,
  Termination_Sensitive u
  (Simulation.Definitions.compile
        ATCD_Refinement
  (compile_core
     (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
        Definitions.TDCoreRefinement)
        (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort)))
(Simulation.Definitions.compile
        ATCD_Refinement
        (compile_core
     (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
        Definitions.TDCoreRefinement)
        (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort)))

   (Simulation.Definitions.compile
        ATCD_Refinement
        (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |))))
  (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state)) 
  (equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2) 
  (ATCD_reboot_list n).
  Proof.
     unfold Termination_Sensitive, ATCD_reboot_list;
     intros.
     destruct n; simpl in *.
     {
        repeat invert_exec.
        invert_exec'' H9; repeat invert_exec.
        eexists (RFinished _ _); repeat econstructor; eauto.
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
      shelve.
      eexists (Recovered _); repeat econstructor; eauto.
     }
     Unshelve.
     all: try solve [exact (fun _ _ => True)].
     6: eapply equivalent_for_recovery_after_reboot; eauto.
  Qed.

Definition equivalent_for_LogCache_write l_a1 l_v1 l_a2 l_v2 hdr1 hdr2:= 
   (NoDup l_a1 <-> NoDup l_a2) /\
   (length l_a1 = length l_v1 <-> length l_a2 = length l_v2) /\
   (Forall (fun a : nat => a < data_length) l_a1 <-> Forall (fun a : nat => a < data_length) l_a2) /\
   (length (addr_list_to_blocks l_a1) + length l_v1 <= log_length <-> length (addr_list_to_blocks l_a2) + length l_v2 <= log_length ) /\
       
   length (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1) =
    length (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2) /\
    
    (log_length <
    Log.count (Log.current_part hdr1) +
    (length (addr_list_to_blocks (map (Nat.add data_start) l_a1)) + length l_v1) <->
    log_length <
    Log.count (Log.current_part hdr2) +
    (length (addr_list_to_blocks (map (Nat.add data_start) l_a2)) + length l_v2)).

Lemma ATCD_TS_commit:
  forall n u txns1 txns2 hdr1 hdr2 lo s1 s2,
 Termination_Sensitive_explicit u lo s1 s2
 (Simulation.Definitions.compile
        ATCD_Refinement
 (compile_core
    (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
       Definitions.TDCoreRefinement)
       (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit)))

 (Simulation.Definitions.compile
       ATCD_Refinement
       (compile_core
    (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
       Definitions.TDCoreRefinement)
       (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit)))
       (Simulation.Definitions.compile
       ATCD_Refinement
       (Simulation.Definitions.compile ATC_Refinement
    (Simulation.Definitions.compile FDRefinement
       (Op FileToFileDisk.Definitions.abs_core Recover))))
 (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state)) 
 (fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
 equivalent_for_commit (seln lo 0 [])
  (dedup_last addr_dec
     (rev (map fst (fst (snd s1)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s1))))
     (rev (map snd (fst (snd s1)))))
  (dedup_last addr_dec
     (rev (map fst (fst (snd s2)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s2))))
     (rev (map snd (fst (snd s2))))) s1 s2 /\
equivalent_for_LogCache_write (dedup_last addr_dec
     (rev (map fst (fst (snd s1)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s1))))
     (rev (map snd (fst (snd s1)))))
  (dedup_last addr_dec
     (rev (map fst (fst (snd s2)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s2))))
     (rev (map snd (fst (snd s2))))) hdr1 hdr2) 
 (ATCD_reboot_list n).
 Proof.
    intros; simpl compile_core.
    eapply ATCD_TS_explicit_compositional.
    intros; apply TS_explicit_to_TS;
    eapply TS_eqv_impl.
    apply ATCD_TS_TransactionCache_get.
    simpl; intuition eauto.
    2: intros; shelve.

    intros; repeat invert_exec.
    invert_exec'' H0;
    invert_exec'' H1; repeat invert_exec.
    eapply ATCD_TS_explicit_compositional.
    simpl. intros; cleanup.
    eapply TS_explicit_eqv_impl.
    unfold equivalent_for_LogCache_write in *; cleanup.
    eapply ATCD_TS_LogCache_write;
    eauto.
    shelve.
    simpl; intros.
    eapply TS_explicit_to_TS.
    apply ATCD_TS_TransactionCache_delete.
    shelve.
    Unshelve.
    5: {
       simpl in *; repeat invert_exec.
       instantiate (3:= fun r1 r2 s0 s3 => 
       equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s0 s3 /\
       equivalent_for_commit (seln lo 0 []) (dedup_last addr_dec (rev (map fst r1)))
         (dedup_by_list addr_dec (rev (map fst r1)) (rev (map snd r1)))
         (dedup_last addr_dec (rev (map fst r2)))
         (dedup_by_list addr_dec (rev (map fst r2)) (rev (map snd r2))) s0 s3).
         
      clear H1 H2.
      setoid_rewrite H; simpl.
      intros; intuition eauto.
      unfold equivalent_for_commit in *; intuition eauto.
      eapply H0; eauto; simpl; intuition.
      eapply H2; eauto; simpl; intuition.
      eapply H5; eauto; simpl; intuition.
    }
    {
       simpl in *; repeat invert_exec.
      simpl; intuition eauto.
    }
    5: {
      simpl; intros; intuition.
      repeat invert_lift2; cleanup.
      simpl in *.
      eapply LogCache.write_finished in H11; cleanup.
      eapply LogCache.write_finished in H15; cleanup.
      all: admit.
    }
Admitted.


  Lemma ATCD_TS_abort_then_ret:
  forall n u T (t1 t2: T) txns1 txns2 hdr1 hdr2,
  Termination_Sensitive u
  (RefinementLift.compile
     (HorizontalComposition
        AuthenticationOperation
        TCDCore)
     (HorizontalComposition
        AuthenticationOperation
        TransactionCacheOperation)
     ATCDLang ATCLang
     (HC_Core_Refinement
        ATCDLang
        ATCLang
        TCD_CoreRefinement)
     T
     (RefinementLift.compile
        (HorizontalComposition
           AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition
           AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length))
        ATCLang AD
        (HC_Core_Refinement
           ATCLang AD
           Definitions.TDCoreRefinement)
        T
        (Bind (Op
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length))
           (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
         (fun _ => Ret t2))))
         (RefinementLift.compile
     (HorizontalComposition
        AuthenticationOperation
        TCDCore)
     (HorizontalComposition
        AuthenticationOperation
        TransactionCacheOperation)
     ATCDLang ATCLang
     (HC_Core_Refinement
        ATCDLang
        ATCLang
        TCD_CoreRefinement)
     T
(RefinementLift.compile
        (HorizontalComposition
           AuthenticationOperation
           TransactionCacheOperation)
        (HorizontalComposition
           AuthenticationOperation
           (TransactionalDiskLayer.TDCore
              data_length))
        ATCLang AD
        (HC_Core_Refinement
           ATCLang AD
           Definitions.TDCoreRefinement)
        T
        (Bind (Op
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length))
           (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
         (fun _ => Ret t2))))
  

   (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
ATC_Refinement
(Simulation.Definitions.compile
   FD.refinement
   (| Recover |))))
(refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state)) 
(equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2) 
(ATCD_reboot_list n).
   Proof.
      intros.
      eapply ATCD_TS_compositional.
      intros; apply ATCD_TS_abort.
      intros; apply ATCD_TS_ret.
      simpl; eauto.
      intros; repeat invert_exec; eauto.
      unfold equivalent_for_recovery in *; cleanup; 
      eexists (_, (_, _)), (_, (_, _)); simpl; split. 
      intuition eauto.
      do 2 eexists; split; eauto.
      intros; congruence.
      intuition eauto.
   Qed.


Lemma ATCD_TS_commit_then_ret:
   forall n u T (t1 t2: T) txns1 txns2 hdr1 hdr2 lo s1 s2,
   Termination_Sensitive_explicit u lo s1 s2
   (RefinementLift.compile
      (HorizontalComposition
         AuthenticationOperation
         TCDCore)
      (HorizontalComposition
         AuthenticationOperation
         TransactionCacheOperation)
      ATCDLang ATCLang
      (HC_Core_Refinement
         ATCDLang
         ATCLang
         TCD_CoreRefinement)
      T
      (RefinementLift.compile
         (HorizontalComposition
            AuthenticationOperation
            TransactionCacheOperation)
         (HorizontalComposition
            AuthenticationOperation
            (TransactionalDiskLayer.TDCore
               data_length))
         ATCLang AD
         (HC_Core_Refinement
            ATCLang AD
            Definitions.TDCoreRefinement)
         T
         (Bind (Op
         (HorizontalComposition AuthenticationOperation
            (TransactionalDiskLayer.TDCore data_length))
            (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ 
            TransactionalDiskLayer.Commit))
          (fun _ => Ret t2))))
          (RefinementLift.compile
      (HorizontalComposition
         AuthenticationOperation
         TCDCore)
      (HorizontalComposition
         AuthenticationOperation
         TransactionCacheOperation)
      ATCDLang ATCLang
      (HC_Core_Refinement
         ATCDLang
         ATCLang
         TCD_CoreRefinement)
      T
 (RefinementLift.compile
         (HorizontalComposition
            AuthenticationOperation
            TransactionCacheOperation)
         (HorizontalComposition
            AuthenticationOperation
            (TransactionalDiskLayer.TDCore
               data_length))
         ATCLang AD
         (HC_Core_Refinement
            ATCLang AD
            Definitions.TDCoreRefinement)
         T
         (Bind (Op
         (HorizontalComposition AuthenticationOperation
            (TransactionalDiskLayer.TDCore data_length))
            (@P2 _ (TransactionalDiskLayer.TDCore data_length) 
            _ TransactionalDiskLayer.Commit))
          (fun _ => Ret t2))))
   
    (Simulation.Definitions.compile
    ATCD_Refinement
    (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
 (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state)) 
 (fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
 equivalent_for_commit (seln lo 0 [])
  (dedup_last addr_dec
     (rev (map fst (fst (snd s1)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s1))))
     (rev (map snd (fst (snd s1)))))
  (dedup_last addr_dec
     (rev (map fst (fst (snd s2)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s2))))
     (rev (map snd (fst (snd s2))))) s1 s2 /\
equivalent_for_LogCache_write (dedup_last addr_dec
     (rev (map fst (fst (snd s1)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s1))))
     (rev (map snd (fst (snd s1)))))
  (dedup_last addr_dec
     (rev (map fst (fst (snd s2)))))
  (dedup_by_list addr_dec
     (rev (map fst (fst (snd s2))))
     (rev (map snd (fst (snd s2))))) hdr1 hdr2) 
 (ATCD_reboot_list n).
    Proof.
       Opaque Transaction.commit.
       intros; simpl.
       eapply ATCD_TS_explicit_compositional.
       intros; eapply TS_explicit_eqv_impl; try apply ATCD_TS_commit.
       {
          simpl; intuition eauto.
          setoid_rewrite H in H0.
          unfold equivalent_for_commit in *; simpl in *; cleanup.
          intuition eauto.
       }
       intros; apply TS_explicit_to_TS. 
       apply ATCD_TS_ret.

       simpl; intros.
       (*Equivalent after commit*)
       admit.
    Admitted.
