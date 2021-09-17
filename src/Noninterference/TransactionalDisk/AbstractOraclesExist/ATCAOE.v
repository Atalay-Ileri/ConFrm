Require Import Lia Framework ATCLayer File FileDiskNoninterference.
Require Import TransactionalDiskRefinement.

Lemma AOE_recover:
forall n u,
abstract_oracles_exist_wrt
(LiftRefinement AD
  (HC_Core_Refinement ATCLang AD
  Definitions.TDCoreRefinement))
(fun s1 s2 => refines_reboot (snd s1) (snd s2))
u
recover
recover (ATC_reboot_list n).
Proof.
    unfold ATC_reboot_list,
    abstract_oracles_exist_wrt;
    induction n; simpl; intros.
    { (* base case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh minimal_oracle_finished_same in H7. *)
      invert_exec'' H7.
      invert_exec'' H6.
      repeat invert_exec; cleanup.
      invert_exec'' H10.
      invert_exec'' H6.
      repeat invert_exec; cleanup.
      eexists [_]; simpl.
      intuition eauto.
      left; intuition eauto.
      do 2 eexists; intuition eauto.
      repeat (rewrite cons_app;
      repeat econstructor; eauto).
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      simpl; eexists; intuition eauto.
      simpl; eexists; intuition eauto.
      left; do 2 eexists; intuition eauto.
      repeat (rewrite cons_app;
      repeat econstructor; eauto).
    }
    { (* Inductive case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh exec_crashed_minimal_oracle in H10; cleanup. *)
      invert_exec'' H10; repeat invert_exec; cleanup.
      {
        invert_exec'' H6; repeat invert_exec; cleanup.
        invert_exec'' H9; repeat invert_exec; cleanup.
        edestruct IHn; only 2: eauto.
        simpl; unfold refines, HC_refines,
        refines_reboot in *; simpl in *;
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_reboot_rep in *; 
        simpl in *; cleanup.
        eexists; eauto.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H0.
      rewrite H0; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      rewrite cons_app.
      repeat econstructor.
      eapply ExecP2Crash with (s:= (fst si, ([], snd (snd si)))).
      repeat econstructor; eauto.
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      simpl.
      do 2 eexists; intuition eauto.
      (*
      rewrite app_nil_r; eauto.
      simpl; intuition eauto.
      do 2 eexists; intuition eauto.
      {
        unfold minimal_oracle; intros.
        intros Hn; simpl in *.
        destruct n0; simpl in *.
        eapply exec_empty_oracle; eauto.
        destruct n0; simpl in *; try lia.
        invert_exec'' Hn.
        apply app_eq_unit in H3;
        split_ors; cleanup; 
        eapply exec_empty_oracle; eauto.
        apply app_eq_unit in H3;
        split_ors; cleanup; 
        try solve [eapply exec_empty_oracle; eauto].
        invert_exec'' H8; repeat invert_exec.
      }
      *)
      right. do 2 eexists.
      unfold Transaction.recover.
      rewrite cons_app;
      econstructor; eauto.
      repeat econstructor; eauto.
      repeat econstructor; eauto.
      intuition eauto.
    }
    {
      (* eapply exec_crashed_minimum_oracle in H5; cleanup. 
      rewrite <- app_assoc. *)
      invert_exec'' H5; repeat invert_exec; cleanup.
      edestruct IHn; only 2: eauto.
      simpl; unfold refines, HC_refines,
      refines_reboot in *; simpl in *;
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_reboot_rep in *; 
      simpl in *; cleanup.
      eexists; eauto.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H0.
      rewrite H0; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      rewrite cons_app;
      eapply ExecBindCrash.
      repeat econstructor; eauto.
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      (*
      do 2 eexists; intuition eauto.
      instantiate (1:= o2).
      rewrite cons_app; eauto.
      simpl; eauto.
      {
        unfold minimal_oracle; intros.
        intros Hn; simpl in *.
        destruct n0; simpl in *; try lia.
        eapply exec_empty_oracle; eauto.
      }
      *)
      right; do 2 eexists; intuition eauto.
      unfold Transaction.recover.
      rewrite cons_app;
      eapply ExecBindCrash; eauto.
      repeat econstructor; eauto.
      destruct si.
      simpl.
      destruct s1.
      repeat econstructor; eauto.
    }
  }
  Unshelve.
  all: exact TransactionCacheLang.
  Qed.


  Lemma compile_lift2_comm:
  forall u T (p: TD.(prog) T) o s ret,
  Language.exec' u o s
  (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore
            FSParameters.data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD
        TDCoreRefinement) T
      (lift_L2 AuthenticationOperation p)) ret ->

      Language.exec' u o s
      (lift_L2 AuthenticationOperation 
        (TDRefinement.(Simulation.Definitions.compile) p)) ret.
  Proof.
    induction p; simpl; intros; eauto.
    invert_exec'' H0.
    eapply IHp in H7.
    eapply H in H10.
    econstructor; eauto.
    eapply IHp in H6.
    eapply ExecBindCrash; eauto.
  Qed.


  Lemma compile_lift2_comm_rev:
  forall u T (p: TD.(prog) T) o s ret,
  Language.exec' u o s
      (lift_L2 AuthenticationOperation 
        (TDRefinement.(Simulation.Definitions.compile) p)) ret ->
  
  Language.exec' u o s
  (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TDCore
            FSParameters.data_length)) ATCLang AD
      (HC_Core_Refinement ATCLang AD
        TDCoreRefinement) T
      (lift_L2 AuthenticationOperation p)) ret.
  Proof.
    induction p; simpl; intros; eauto.
    invert_exec'' H0.
    eapply IHp in H7.
    eapply H in H10.
    econstructor; eauto.
    eapply IHp in H6.
    eapply ExecBindCrash; eauto.
  Qed.



Lemma ATC_AOE:
forall u T (p: TD.(prog) T) n, 

(forall o s s' r, 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec TransactionCacheLang u o (snd s) 
(TDRefinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
exists oa, forall grs, oracle_refines _ _
  ATCLang AD
  ATC_CoreRefinement T u s
  (lift_L2 AuthenticationOperation p)
  grs (map
       (fun o : Language.token' TransactionCacheOperation =>
        match o with
        | OpToken _ o1 =>
            OpToken
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
              (Token2 AuthenticationOperation
                 TransactionCacheOperation o1)
        | Language.Crash _ =>
            Language.Crash
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        | Language.Cont _ =>
            Language.Cont
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        end) o) oa) ->

        (forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
Language.exec' u o s
        (RefinementLift.compile
           (HorizontalComposition AuthenticationOperation
              TransactionCacheOperation)
           (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TDCore
                 FSParameters.data_length)) ATCLang AD
           (HC_Core_Refinement ATCLang AD
              TDCoreRefinement) T
           (lift_L2 AuthenticationOperation p)) (Crashed s') ->
exists oa, oracle_refines _ _
  ATCLang AD
  ATC_CoreRefinement T u s
  (lift_L2 AuthenticationOperation p)
  (fun
     s : HorizontalComposition.state'
           AuthenticationOperation
           TransactionCacheOperation
   => (fst s, ([], snd (snd s)))) o oa) ->

(forall o s s', 
(exists s1, refines s s1) ->
exec TransactionCacheLang u o s 
(TDRefinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists s1', refines_reboot s' s1') ->
abstract_oracles_exist_wrt ATC_Refinement
  (ATC_Refinement.(Simulation.Definitions.refines)) u
  (@lift_L2 AuthenticationOperation _ TD _ p) 
  File.recover (ATC_reboot_list n).
Proof.
    intros; destruct n; simpl; eauto.
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      eapply_fresh compile_lift2_comm in H10.
      eapply lift2_invert_exec in Hx; cleanup.
      edestruct H; eauto.

      eexists [_]; simpl; eauto.
      split; intuition eauto.
      left; do 2 eexists; intuition eauto.
    }
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct AOE_recover; eauto.
      {
        unfold HC_refines in *; 
        simpl in *; cleanup.
        eapply compile_lift2_comm in H13.
        eapply lift2_invert_exec_crashed in H13; cleanup.
        edestruct H1; eauto.
        unfold refines_reboot, Transaction.transaction_reboot_rep in *; 
        simpl in *; eauto.
        exists (fst x, (Empty, (snd (snd x1), snd (snd x1)))); eauto.
      }

      eapply_fresh compile_lift2_comm in H13.
      eapply lift2_invert_exec_crashed in Hx; cleanup.
      edestruct H0; eauto.

      eexists (_ :: _).
      simpl.
      intuition eauto.
      eapply recovery_oracles_refine_to_length in H3; eauto.
    }
    Unshelve.
    all: exact ATCLang.
Qed.


Lemma ATC_AOE_2:
forall u T (p: AD.(prog) T) n, 

(forall o s s' r, 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s 
(ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
exists oa, forall grs, oracle_refines _ _
  ATCLang AD
  ATC_CoreRefinement T u s p grs o oa) ->

(forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s (ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists oa, oracle_refines _ _
  ATCLang AD
  ATC_CoreRefinement T u s p
  (fun
     s : HorizontalComposition.state'
           AuthenticationOperation
           TransactionCacheOperation
   => (fst s, ([], snd (snd s)))) o oa) ->

(forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s 
(ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists s1', refines_reboot (snd s') s1') ->

abstract_oracles_exist_wrt ATC_Refinement 
  (ATC_Refinement.(Simulation.Definitions.refines)) u p 
  File.recover (ATC_reboot_list n).
Proof.
    intros; destruct n; simpl; eauto.
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct H; eauto.

      eexists [_]; simpl; eauto.
      split; intuition eauto.
      left; do 2 eexists; intuition eauto.
    }
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct AOE_recover; eauto.
      {
        unfold HC_refines in *; 
        simpl in *; cleanup.
        edestruct H1; eauto.
        unfold refines_reboot, Transaction.transaction_reboot_rep in *; 
        simpl in *; eauto.
        exists (fst x, (Empty, (snd (snd x0), snd (snd x0)))); eauto.
      }
      
      edestruct H0; eauto.

      eexists (_ :: _).
      simpl.
      intuition eauto.
      eapply recovery_oracles_refine_to_length in H3; eauto.
      }
Qed.
