Require Import Lia Framework ATCDLayer File FileDiskNoninterference.
Require Import LoggedDiskRefinement LogCache.RepImplications Not_Init.
Require Import ATCDSimulation.

Opaque LogCache.recover.
Lemma ATCD_AOE_recover:
forall l_grs u,
abstract_oracles_exist_wrt
ATCD_Refinement
(fun s1 s2 => refines_reboot (snd (snd s1)) (snd (snd s2)) /\
fst s1 = fst s2 /\
fst (snd s1)  = fst (snd s2)) u
(Simulation.Definitions.compile ATC_Refinement File.recover)
(Simulation.Definitions.compile ATC_Refinement File.recover)
(ATCD_reboot_list l_grs).
Proof.
    unfold ATCD_reboot_list,
    abstract_oracles_exist_wrt;
    induction l_grs; simpl; intros.
    { (* base case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh minimal_oracle_finished_same in H7. *)
      invert_exec'' H7.
      invert_exec'' H9.
      repeat invert_exec; cleanup.
      eapply lift2_invert_exec in H12; cleanup.
      eapply lift2_invert_exec in H4; cleanup.
      repeat cleanup_pairs; eauto.
      eexists [_]; simpl.
      intuition eauto.
      left; intuition eauto.
      do 2 eexists; intuition eauto.
      repeat (rewrite cons_app;
      repeat econstructor; eauto).
      eapply lift2_exec_step.
      eapply lift2_exec_step; eauto.
      right; do 7 eexists; intuition eauto.
      3: eapply lift2_exec_step;
      eapply lift2_exec_step; eauto.
      2: simpl; repeat econstructor; eauto.
      eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      simpl; eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply HC_oracle_transformation_same.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply HC_oracle_transformation_same.
      left; eexists; simpl in *; intuition eauto.
      destruct t; eauto.
      eapply LogCache.recover_finished; eauto.
    }
    { (* Inductive case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh exec_crashed_minimal_oracle in H10; cleanup. *)
      invert_exec'' H10; repeat invert_exec; cleanup.
      {
        invert_exec'' H8; repeat invert_exec; cleanup.
        eapply lift2_invert_exec_crashed in H13; cleanup.
        eapply lift2_invert_exec_crashed in H4; cleanup.
        repeat cleanup_pairs; eauto.

        edestruct IHl_grs; only 2: eauto.
        simpl.
        unfold refines,
        refines_reboot in *;
        simpl in *; cleanup.
        eapply LogCache.recover_crashed in H5; eauto.
        simpl in *; cleanup.
        clear H2.
        eexists (_, (_, _)); repeat split.
        repeat split_ors.
        simpl; eapply cached_log_reboot_rep_to_reboot_rep in c; eauto.
        simpl; eapply cached_log_crash_rep_during_recovery_to_reboot_rep in c; eauto.
        simpl; eapply cached_log_crash_rep_after_commit_to_reboot_rep in c; eauto.
        apply select_total_mem_synced.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H0.
      rewrite H0; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      rewrite cons_app.
      econstructor.
      repeat econstructor.
      repeat eapply lift2_exec_step_crashed; eauto.
      right; do 7 eexists; intuition eauto.
      3: repeat eapply lift2_exec_step_crashed; eauto.
      2: simpl; repeat econstructor; eauto.
      eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      simpl; eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply HC_oracle_transformation_same.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply HC_oracle_transformation_same.
      right; eexists; simpl in *; intuition eauto.
      eapply LogCache.recover_crashed; eauto.

      simpl; eauto.
    }
    {
      (* eapply exec_crashed_minimum_oracle in H5; cleanup. 
      rewrite <- app_assoc. *)
      invert_exec'' H7; repeat invert_exec; cleanup.
      edestruct IHl_grs; only 2: eauto.
      simpl; eexists (_, (_, _)); simpl; split. 
      eapply refines_reboot_to_refines_reboot; eauto.
      intuition eauto.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H2.
      rewrite H2; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      repeat cleanup_pairs.
      repeat econstructor; eauto.

      left; do 2 eexists; intuition eauto.
      repeat cleanup_pairs.
      repeat econstructor; eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
    }
  }
  Unshelve.
  all: exact ATCDLang.
  Qed.


  (*
  Lemma compile_lift2_comm:
  forall u T (p: LoggedDiskLang.(prog) T) o s ret,
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
*)


Lemma ATCD_AOE':
forall u T (p: ATCLang.(prog) T) l_grs, 

(forall o s s' r, 
(exists s1, ATCD_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCDLang u o s 
(ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
exists oa, forall grs, 
oracle_refines _ _
  ATCDLang ATCLang
  ATCD_CoreRefinement T u s p grs o oa) ->

(forall o s s', 
(exists s1, ATCD_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCDLang u o s (ATCD_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists oa, 
oracle_refines _ _
  ATCDLang ATCLang
  ATCD_CoreRefinement T u s p
  (ATCD_reboot_f (seln l_grs 0 (fun _ => 0))) o oa) ->

(forall o s s', 
(exists s1, ATCD_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCDLang u o s 
(ATCD_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists s1', 
ATCD_refines_reboot (seln l_grs 0 (fun _ => 0)) s' s1') ->

abstract_oracles_exist_wrt ATCD_Refinement 
  (ATCD_Refinement.(Simulation.Definitions.refines)) u p 
  (ATC_Refinement.(Simulation.Definitions.compile) File.recover) 
  (ATCD_reboot_list l_grs).
Proof.
    intros; destruct l_grs; simpl; eauto.
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
      edestruct ATCD_AOE_recover; eauto.
      {
        unfold HC_refines in *; 
        simpl in *; cleanup.
        edestruct H1; eauto.
      }
      
      edestruct H0; eauto.

      eexists (_ :: _).
      simpl.
      intuition eauto.
      eapply recovery_oracles_refine_to_length in H3; eauto.
      }
Qed.

Lemma ATCD_AOE:
forall T (p: ATCLang.(prog) T) l_selector u,
not_init p ->
abstract_oracles_exist_wrt ATCD_Refinement
(Simulation.Definitions.refines ATCD_Refinement) u p
(Simulation.Definitions.compile ATC_Refinement File.recover)
(ATCD_reboot_list l_selector).
Proof.
intros; eapply ATCD_AOE'.
{
  intros.
  eapply ATCD_oracle_refines_finished; eauto.
}
{
  intros.
  eapply ATCD_oracle_refines_crashed; eauto.
}
{
  intros; edestruct ATCD_simulation_crash; eauto.
}
Qed.
