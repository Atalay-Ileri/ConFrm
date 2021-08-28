Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATCSimulation ATCAOE.
Require Import Not_Init ATC_ORS ATC_TS_Common.

Import FileDiskLayer.
Set Nested Proofs Allowed.

Lemma ATC_TS_TransactionCache_get:
  forall n u V R,
  Termination_Sensitive u
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (Get (prod addr value)))))
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ (@P1 (ListOperation (addr * value)) _ _ (Get (prod addr value)))))
(Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |)))
  V R
(ATC_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATC_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  invert_exec'' H9; repeat invert_exec.
  eexists (RFinished _ _); repeat econstructor.

  invert_exec'' H12;
  repeat invert_exec; simpl in *.
  edestruct ATC_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  Unshelve.
  all: try solve [exact (fun _ _ => True)].
  all: simpl; eauto.
Qed.


Lemma ATC_TS_LoggedDisk_read:
  forall n u V R a1 a2,
  (a1 < data_length <-> a2 < data_length) -> 
  Termination_Sensitive u
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ (LoggedDiskLayer.Read a1))))
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ (LoggedDiskLayer.Read a2))))
(Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |)))
  V R
(ATC_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATC_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  invert_exec'' H10; repeat invert_exec.
  eexists (RFinished _ _); repeat econstructor.
  lia.

  eexists (RFinished _ _); 
  try solve [repeat econstructor; lia].

  invert_exec'' H13;
  repeat invert_exec; simpl in *.
  edestruct ATC_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  Unshelve.
  all: try solve [exact (fun _ _ => True)].
  all: simpl; eauto.
Qed.

Lemma ATC_TS_LoggedDisk_write:
  forall n u V R l_a1 l_a2 l_v1 l_v2,
  (NoDup l_a1 <-> NoDup l_a2) ->
  (length l_a1 = length l_v1 <-> length l_a2 = length l_v2) ->
   (Forall (fun a : nat => a < data_length) l_a1 <-> Forall (fun a : nat => a < data_length) l_a2) ->
   (length (addr_list_to_blocks l_a1) + length l_v1 <= log_length <-> length (addr_list_to_blocks l_a2) + length l_v2 <= log_length ) ->
  Termination_Sensitive u
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ 
     (LoggedDiskLayer.Write l_a1 l_v1))))
  (Op
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (@P2 _ TransactionCacheOperation _ 
     (@P2 _ (LoggedDiskOperation log_length data_length) _ 
     (LoggedDiskLayer.Write l_a2 l_v2))))
(Simulation.Definitions.compile
   ATC_Refinement
   (Simulation.Definitions.compile
      FD.refinement
      (| Recover |)))
  V R
(ATC_reboot_list n).
Proof.
  unfold Termination_Sensitive, ATC_reboot_list; 
  intros; destruct n;
  repeat invert_exec.
  {
   invert_exec'' H13; repeat invert_exec.
   eexists (RFinished _ _); repeat econstructor;
   intuition eauto.

   eexists (RFinished _ _); 
   do 4 econstructor.
   eapply LoggedDiskLayer.ExecWriteFail.
   intuition eauto.
   lia.
  }
  {
     invert_exec'' H16;
  repeat invert_exec; simpl in *.
  edestruct ATC_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  repeat invert_exec; simpl in *.
  edestruct ATC_TS_recovery; eauto.
  all: unfold AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  shelve.
  eexists (Recovered _); repeat econstructor; eauto.
  all: intuition eauto.
  }
  Unshelve.
  all: try solve [exact (fun _ _ => True)].
  all: simpl; eauto.
Qed.


Lemma ATC_TS_Transaction_read:
    forall n u a1 a2,
    (a1 < data_length <-> a2 < data_length) -> 
    Termination_Sensitive u
    (@lift_L2 AuthenticationOperation _ TransactionCacheLang _
        (Transaction.read a1))
    (@lift_L2 AuthenticationOperation _ TransactionCacheLang  _
        (Transaction.read a2))
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATC_Refinement
     AD_valid_state)
  (fun s1 s2 =>
  Transaction.get_first (fst (snd s1)) a1 = None <-> Transaction.get_first (fst (snd s2)) a2 = None)
  (ATC_reboot_list n).
  Proof.
    unfold Transaction.read; intros.
    destruct (Compare_dec.lt_dec a1 data_length);
    destruct (Compare_dec.lt_dec a2 data_length); try lia.
    2: apply ATC_TS_ret.

    intros.
    eapply ATC_TS_compositional; simpl.
    intros; eapply ATC_TS_TransactionCache_get.

    intros.
    cleanup.
    repeat invert_exec.
    destruct_fresh (Transaction.get_first (fst (snd s1)) a1);
    destruct_fresh (Transaction.get_first (fst (snd s2)) a2);
    try solve [intuition congruence].
    setoid_rewrite D;
    setoid_rewrite D0; simpl.
    apply ATC_TS_ret.
    apply H2 in D0; 
    setoid_rewrite D in D0; congruence.
    apply H2 in D; 
    setoid_rewrite D in D0; congruence.

    setoid_rewrite D;
    setoid_rewrite D0; simpl.
    eapply ATC_TS_compositional; simpl; intros.
    eapply ATC_TS_LoggedDisk_read; eauto.
    apply ATC_TS_ret.
    instantiate (1:= fun _ _ => True); simpl; eauto.
    instantiate (1:= fun _ _ => True); simpl; eauto.
  Qed.

  Lemma ATC_TS_auth:
  forall u u1 u2 n V R,
  Termination_Sensitive u 
  (Op
     (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation) 
        (@P1 AuthenticationOperation _ _ (Auth u1)))
  (Op
     (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation) 
        (@P1 AuthenticationOperation _ _ (Auth u2)))
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length))
     ATCLang AD
     (HC_Core_Refinement ATCLang AD
        Definitions.TDCoreRefinement) unit File.recover)
  V R (ATC_reboot_list n).
  Proof.
   unfold Termination_Sensitive, ATC_reboot_list;
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
    simpl in *; edestruct ATC_TS_recovery. 
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
   all: simpl; eauto.
Qed.

  Lemma ATC_TS_abort:
   forall n u R,
  Termination_Sensitive u
  (compile_core
     (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
        Definitions.TDCoreRefinement)
        (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
  (compile_core
     (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
        Definitions.TDCoreRefinement)
        (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
  (Simulation.Definitions.compile ATC_Refinement
     (Simulation.Definitions.compile FDRefinement
        (Op FileToFileDisk.Definitions.abs_core Recover)))
  (refines_valid ATC_Refinement AD_valid_state) R
  (ATC_reboot_list n).
  Proof.
     unfold Termination_Sensitive, ATC_reboot_list;
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
      simpl in *; edestruct ATC_TS_recovery. 
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
     all: simpl; eauto.
  Qed.

  Lemma ATC_TS_commit:
  forall n u,
 Termination_Sensitive u
 (compile_core
    (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
       Definitions.TDCoreRefinement)
       (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit))
 (compile_core
    (HC_Core_Refinement ATCLang AuthenticatedDiskLayer.ADLang
       Definitions.TDCoreRefinement)
       (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit))
 (Simulation.Definitions.compile ATC_Refinement
    (Simulation.Definitions.compile FDRefinement
       (Op FileToFileDisk.Definitions.abs_core Recover)))
 (refines_valid ATC_Refinement AD_valid_state) 
 (fun s1 s2 => (Forall (fun a : nat => a < data_length)
 (dedup_last addr_dec (rev (map fst (fst (snd s1))))) <->
 Forall (fun a : nat => a < data_length)
 (dedup_last addr_dec (rev (map fst (fst (snd s2)))))) /\

 (length
(addr_list_to_blocks
(dedup_last addr_dec (rev (map fst (fst (snd s1)))))) +
length
(dedup_by_list addr_dec (rev (map fst (fst (snd s1))))
(rev (map snd (fst (snd s1))))) <= log_length <->
length
(addr_list_to_blocks
(dedup_last addr_dec (rev (map fst (fst (snd s2)))))) +
length
(dedup_by_list addr_dec (rev (map fst (fst (snd s2))))
(rev (map snd (fst (snd s2))))) <= log_length))
 (ATC_reboot_list n).
 Proof.
    intros; simpl.
    eapply ATC_TS_compositional.
    intros; apply ATC_TS_TransactionCache_get.
    2: intros; shelve.
    intros; repeat invert_exec.
    
    eapply ATC_TS_compositional.
    {
       intros; eapply ATC_TS_LoggedDisk_write;
       intuition eauto. 
       
       eapply Transaction.dedup_last_NoDup.
       eapply Transaction.dedup_last_NoDup.
       
       eapply dedup_last_dedup_by_list_length_le.
       repeat rewrite rev_length, map_length; eauto.
       eapply dedup_last_dedup_by_list_length_le.
       repeat rewrite rev_length, map_length; eauto.
    }
    intros; eapply ATC_TS_abort.
    intros; shelve.
    Unshelve. 
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.
Qed.

  Lemma ATC_TS_abort_then_ret:
  forall n u T (t1 t2: T) R,
  Termination_Sensitive u
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
     (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
     _ (Bind
     (Op
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length))
        (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
     (fun _ : unit => Ret t1)))
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
     (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
     _ (Bind
     (Op
        (HorizontalComposition AuthenticationOperation
           (TransactionalDiskLayer.TDCore data_length))
           (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Abort))
     (fun _ : unit => Ret t2)))
  (RefinementLift.compile
     (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
     (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
     (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) unit
     File.recover) 
     (refines_valid ATC_Refinement
      AD_valid_state) R (ATC_reboot_list n).
   Proof.
      intros.
      eapply ATC_TS_compositional.
      intros; apply ATC_TS_abort.
      intros; apply ATC_TS_ret.
      instantiate (1:= fun _ _ => True); simpl; eauto.
   Qed.

   Lemma ATC_TS_commit_then_ret:
   forall n u T (t1 t2: T),
   Termination_Sensitive u
   (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
         (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
      _ (Bind
      (Op
         (HorizontalComposition AuthenticationOperation
            (TransactionalDiskLayer.TDCore data_length))
         (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit))
      (fun _ : unit => Ret t1)))
   (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
         (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement)
      _ (Bind
      (Op
         (HorizontalComposition AuthenticationOperation
            (TransactionalDiskLayer.TDCore data_length))
            (@P2 _ (TransactionalDiskLayer.TDCore data_length) _ TransactionalDiskLayer.Commit))
      (fun _ : unit => Ret t2)))
   (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
         (TransactionalDiskLayer.TDCore data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD Definitions.TDCoreRefinement) unit
      File.recover) 
      (refines_valid ATC_Refinement
       AD_valid_state) 
       (fun s1 s2 => (Forall (fun a : nat => a < data_length)
 (dedup_last addr_dec (rev (map fst (fst (snd s1))))) <->
 Forall (fun a : nat => a < data_length)
 (dedup_last addr_dec (rev (map fst (fst (snd s2)))))) /\

 (length
(addr_list_to_blocks
(dedup_last addr_dec (rev (map fst (fst (snd s1)))))) +
length
(dedup_by_list addr_dec (rev (map fst (fst (snd s1))))
(rev (map snd (fst (snd s1))))) <= log_length <->
length
(addr_list_to_blocks
(dedup_last addr_dec (rev (map fst (fst (snd s2)))))) +
length
(dedup_by_list addr_dec (rev (map fst (fst (snd s2))))
(rev (map snd (fst (snd s2))))) <= log_length))
       (ATC_reboot_list n).
    Proof.
       intros.
       eapply ATC_TS_compositional.
       intros; apply ATC_TS_commit.
       intros; apply ATC_TS_ret.
       instantiate (1:= fun _ _ => True); simpl; eauto.
    Qed.