Require Import Eqdep Lia Framework FSParameters.
Require Import TransactionCacheLayer TransactionalDiskLayer.
Require Import Transaction TransactionToTransactionalDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Lia.


Set Nested Proofs Allowed.

Local Notation "'imp'" := TransactionCacheLang.
Local Notation "'abs'" := (TransactionalDiskLang data_length).
Local Notation "'refinement'" := TransactionalDiskRefinement.

Definition TC_reboot_f := fun s: imp.(state) => (([]: list (addr * value)), snd s).

Definition TD_reboot_f := fun s: abs.(state) => (snd s, snd s).

  Definition transaction_cache_reboot_list n := repeat (fun s: imp.(state) => (([]: list (addr * value)), snd s)) n.

  Definition transactional_disk_reboot_list n := repeat (fun s : abs.(state) => (snd s, snd s)) n.

  Ltac unify_execs :=
    match goal with
    |[H : recovery_exec ?u ?x ?y ?z ?a ?b ?c _,
      H0 : recovery_exec ?u ?x ?y ?z ?a ?b ?c _ |- _ ] =>
     eapply recovery_exec_deterministic_wrt_reboot_state in H; [| apply H0]
    | [ H: exec ?u ?x ?y ?z ?a _,
        H0: exec ?u ?x ?y ?z ?a _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec' ?u ?x ?y ?z _,
        H0: exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec _ ?u ?x ?y ?z _,
        H0: Language.exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    end.
  
  Lemma recovery_oracles_refine_to_length:
    forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (ref: Refinement L_imp L_abs)
      l_o_imp l_o_abs T (u: user) s (p1: L_abs.(prog) T) rec l_rf u, 
      recovery_oracles_refine_to ref u s p1 rec l_rf l_o_imp l_o_abs ->
      length l_o_imp = length l_o_abs.
  Proof.
    induction l_o_imp; simpl; intros; eauto.
    tauto.
    destruct l_o_abs; try tauto; eauto.
  Qed.
  
  Theorem abstract_oracles_exist_wrt_recover:
    forall n u, 
      abstract_oracles_exist_wrt refinement refines_reboot u (|Recover|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; induction n;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
      intuition eauto.
      left; eexists; intuition eauto.
      destruct t.
      
      eexists; intuition eauto.
      eapply_fresh recover_finished in H7; eauto.
      cleanup.
      eexists; intuition eauto.
      left.
      unfold transaction_reboot_rep, transaction_rep in *;
      simpl in *. cleanup.
      repeat cleanup_pairs; eauto.
    }
    { 
      eapply IHn in H11; eauto; cleanup.
      exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
      eapply_fresh recover_crashed in H10; eauto; cleanup.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      right.
      eexists; repeat split; eauto;
      simpl in *.
      cleanup; eauto.

      eapply_fresh recover_crashed in H10; eauto; cleanup.
      eexists; unfold transaction_reboot_rep in *; simpl; intuition eauto.
      eapply_fresh recover_crashed in H10; eauto; cleanup.
      eexists; unfold transaction_reboot_rep in *; simpl; intuition eauto.
      instantiate (1:= x); cleanup; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_recover':
    forall n u, 
      abstract_oracles_exist_wrt refinement refines u (|Recover|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; destruct n;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
      intuition eauto.
      left.
      eexists; intuition eauto.
      destruct t.
      
      eexists; intuition eauto.
      eapply_fresh recover_finished_2 in H7; eauto.
      eexists; intuition eauto.
      left.
      unfold refines, transaction_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs; eauto.
    }
    {        
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
      eapply_fresh recover_crashed in H10; eauto; cleanup.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      right.
      eexists; repeat split; eauto;
      simpl in *.
      eexists; repeat split; eauto;
      simpl in *.
      cleanup; eauto.
      
      unfold refines, refines_reboot,
      transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.

      eapply_fresh recover_crashed in H10; eauto; cleanup.
      eexists; unfold refines, refines_reboot,
               transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.
      
      unfold refines, refines_reboot,
      transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_read:
    forall n a u, 
      abstract_oracles_exist_wrt refinement refines u (|Read a|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; destruct n;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
      intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply_fresh read_finished in H7; eauto.
      eexists; intuition eauto.     
    }
    {        
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
      eapply_fresh read_crashed in H10; eauto; cleanup.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      right.
      eexists; repeat split; eauto;
      simpl in *.
      eexists; repeat split; eauto;
      simpl in *.
      cleanup; eauto.
      

      eapply_fresh read_crashed in H10; eauto; cleanup.
      eexists; unfold refines, refines_reboot,
               transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.
    }
  Qed.
  
  Theorem abstract_oracles_exist_wrt_write:
    forall n l_a l_v u,
      abstract_oracles_exist_wrt refinement refines u (|Write l_a l_v|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; destruct n;
    simpl; intros; cleanup; invert_exec.
    {      
      eapply_fresh write_finished in H7; eauto.
      split_ors; cleanup.
      {
        exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
        intuition eauto.
        left.
        eexists; intuition eauto.
        
        eexists; intuition eauto.
        eexists; split; eauto.
        left.
        do 2 eexists; split; eauto.
        left; intuition eauto.
        unfold refines, transaction_rep in *; simpl in *; cleanup.
        repeat cleanup_pairs; eauto.
        inversion H0; eauto.
      }
      split_ors.
      {
        exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
        intuition eauto.
        left.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        left.
        eexists; intuition eauto.
        eexists; split; eauto.
      }
      {
        exists  [ [OpToken (TransactionalDiskOperation data_length) TxnFull] ]; simpl.
        intuition eauto.
        left.
        eexists; intuition eauto.
        eexists; intuition eauto.
        eexists; intuition eauto.
        left.
        do 2 eexists; intuition eauto.
      }
    }
    {        
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
      eapply_fresh write_crashed in H10; eauto; cleanup.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      right.
      eexists; repeat split; eauto;
      simpl in *.
      eexists; repeat split; eauto;
      simpl in *.
      cleanup; eauto.      

      eapply_fresh write_crashed in H10; eauto; cleanup.
      eexists; unfold refines, refines_reboot,
               transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.
    }
    Qed.

    Theorem abstract_oracles_exist_wrt_abort:
    forall n u, 
      abstract_oracles_exist_wrt refinement refines u (|Abort|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; destruct n;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
      intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.

      eapply_fresh abort_finished in H7; eauto.
      eexists; intuition eauto.
      unfold refines, transaction_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs; eauto.
    }
    {        
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
      eapply_fresh abort_crashed in H10; eauto; cleanup.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      right.
      eexists; repeat split; eauto;
      simpl in *.
      eexists; repeat split; eauto;
      simpl in *.
      cleanup; eauto.
      
      eapply_fresh abort_crashed in H10; eauto; cleanup.
      eexists; unfold refines, refines_reboot,
               transaction_rep, transaction_reboot_rep in *;
      simpl in *; cleanup; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_commit:
    forall n u, 
      abstract_oracles_exist_wrt refinement refines u (|Commit|) (|Recover|) (transaction_cache_reboot_list n).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; destruct n;
    simpl; intros; cleanup; invert_exec.
    
    {
      eapply_fresh commit_finished in H7; eauto.
      exists  [ [OpToken (TransactionalDiskOperation data_length) Cont] ]; simpl.
      intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      unfold refines, transaction_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs; eauto.
    }
    {        
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      eapply_fresh commit_crashed in H10; eauto; cleanup.
      split_ors.
      {
        exists ([OpToken (TransactionalDiskOperation data_length) CrashBefore]::x0); simpl.
        repeat split; eauto; try (unify_execs; cleanup).
        eapply recovery_oracles_refine_to_length in H0; eauto.
        right.
        eexists; repeat split; eauto;
        simpl in *.
        eexists; repeat split; eauto;
        simpl in *.
        cleanup; eauto.
        right; eexists; repeat split; eauto;
        simpl in *.
        unfold refines, transaction_rep in *;
        cleanup; eauto.
      }
      {
        exists ([OpToken (TransactionalDiskOperation data_length) CrashAfter]::x0); simpl.
        repeat split; eauto; try (unify_execs; cleanup).
        eapply recovery_oracles_refine_to_length in H0; eauto.
        right.
        eexists; repeat split; eauto;
        simpl in *.
        eexists; repeat split; eauto;
        simpl in *.
        cleanup; eauto.
        right; eexists; repeat split; eauto;
        simpl in *.
        unfold refines, transaction_rep in *;
        cleanup; eauto.
      }
      {
        eapply_fresh commit_crashed in H10; eauto; cleanup.
        split_ors;
        unfold refines, refines_reboot,
        transaction_rep, transaction_reboot_rep in *;
        simpl in *; cleanup; eauto.
        exists (fst x, fst x); simpl; eauto.
      }
    }
  Qed.
    
  Lemma addrs_match_upd:
    forall A AEQ V1 V2 (m1: @mem A AEQ V1) (m2: @mem A AEQ V2) a v,
      addrs_match m1 m2 ->
      m2 a <> None ->
      addrs_match (upd m1 a v) m2.
  Proof.
    unfold addrs_match; intros; simpl.
    destruct (AEQ a a0); subst;
    [rewrite upd_eq in *
    |rewrite upd_ne in *]; eauto.
  Qed.

  Lemma cons_l_neq:
    forall V (l:list V) v,
      ~ v::l = l.
  Proof.
    induction l; simpl; intros; try congruence.
  Qed.

  Lemma mem_union_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      mem_union m1 m2 a = Some v.
  Proof.
    unfold mem_union; simpl; intros.
    cleanup; eauto.
  Qed.
  
  Lemma mem_union_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      mem_union m1 m2 a = m2 a.
  Proof.
    unfold mem_union; simpl; intros.
    cleanup; eauto.
  Qed.

  Lemma addrs_match_mem_union1 :
    forall A AEQ V (m1 m2: @mem A AEQ V),
      addrs_match m1 (mem_union m1 m2).
  Proof.
    unfold addrs_match; intros.
    destruct_fresh (m1 a); try congruence.
    erewrite mem_union_some_l; eauto.
  Qed.

  Lemma addrs_match_empty_mem:
    forall A AEQ V1 V2 (m: @mem A AEQ V1),
      addrs_match (@empty_mem A AEQ V2) m.
  Proof.
    unfold addrs_match, empty_mem;
    simpl; intros; congruence.
  Qed.
  
  Lemma empty_mem_some_false:
    forall A AEQ V (m: @mem A AEQ V) a v,
      m = empty_mem ->
      m a <> Some v.
  Proof.
    intros.
    rewrite H.
    unfold empty_mem; simpl; congruence.
  Qed.
  
  
Lemma recovery_simulation :
  forall n u,
    SimulationForProgramGeneral _ _ _ _ refinement u _ (|Recover|) (|Recover|)
                         (transaction_cache_reboot_list n)
                         (transactional_disk_reboot_list n)
                         refines_reboot refines.
Proof.
  unfold SimulationForProgramGeneral; induction n; simpl; intros; cleanup.
  {
    destruct l_o_imp; intuition; simpl in *.
    cleanup; intuition.
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; unify_execs; cleanup;
    cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
    
    eexists; intuition eauto.
    unfold transactional_disk_reboot_list in *; simpl.
    simpl in *; try lia.
    instantiate (1:= RFinished (snd s_abs, snd s_abs) tt). 
    repeat econstructor.
    unfold refines, refines_reboot,
    transaction_rep, transaction_reboot_rep in *;
    simpl in *; cleanup; eauto.
    intuition eauto.
    pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.
    simpl; destruct x0; eauto.
    cleanup; intuition.
  }
  {
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; intuition eauto; repeat (unify_execs; cleanup).
    cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
    edestruct IHn.
    eauto.
    instantiate (1:= (snd s_abs, snd s_abs)).
    eauto.
    eauto.
      
    unfold refines_reboot, transaction_reboot_rep in *; simpl in *; cleanup.
    exists (Recovered (extract_state_r x)).
    unfold transactional_disk_reboot_list in *; simpl in *.
    unfold refines_reboot, transaction_reboot_rep in *; cleanup.
    split; eauto.
    repeat econstructor; eauto.
    repeat cleanup_pairs; eauto.
  }
Qed.


Lemma read_simulation :
  forall a n u,
    SimulationForProgram refinement u (|Read a|) (|Recover|)
                         (transaction_cache_reboot_list n)
                         (transactional_disk_reboot_list n).
Proof.
  unfold transaction_cache_reboot_list, SimulationForProgram,
  SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      intuition cleanup; unify_execs; cleanup.
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      eapply_fresh read_finished in H10; cleanup; eauto.
      
      destruct n; simpl in *; try congruence; cleanup.
      split_ors; cleanup.
      {
        exists (RFinished s_abs ((fst s_abs) a));
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
      intuition cleanup; unify_execs; cleanup.
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct n; simpl in *; try congruence; cleanup.
      
      edestruct recovery_simulation; eauto.
      unfold refines, transaction_rep in *; cleanup.
      instantiate (1:=(snd s_abs, snd s_abs)).
      eauto.
      
      exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
      unfold transactional_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Qed.



Lemma write_simulation :
  forall a v n u,
    SimulationForProgram refinement u (|Write a v|) (|Recover|)
                         (transaction_cache_reboot_list n)
                         (transactional_disk_reboot_list n).
Proof.
  unfold transaction_cache_reboot_list, SimulationForProgram,
  SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup;
      destruct n; simpl in *; try congruence; cleanup;
      simpl in *; try lia.

      eapply write_finished in H10; eauto; 
      split_ors; cleanup.
      {
        exists (RFinished (upd (fst s_abs) a v, snd s_abs) (Some tt));
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
      repeat cleanup_pairs.
      exfalso; eapply cons_l_neq; eauto.
      apply H6.
      eapply write_finished in H10; eauto. 
      split_ors; logic_clean; try lia.
      destruct s_imp; simpl in *; inversion H3.
      exfalso; eapply cons_l_neq; eauto.
      symmetry in H7; apply H7.
      split_ors; cleanup; try lia.
      {
        cleanup.
        exists (RFinished s_abs None);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
      eapply write_finished in H10; eauto.
      split_ors; logic_clean; try lia.
      destruct s_imp; simpl in *; inversion H3.
      exfalso; eapply cons_l_neq; eauto.
      symmetry in H8; apply H8.
      split_ors; cleanup; try lia. 
      {
        exists (RFinished s_abs None);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
    }
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct n; simpl in *; try congruence; cleanup.
      
      edestruct recovery_simulation; eauto.
      unfold refines, transaction_rep in *; cleanup.
      instantiate (1:=(snd s_abs, snd s_abs)).
      eauto.
      
      exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
      unfold transactional_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Qed.


Lemma abort_simulation :
  forall n u,
    SimulationForProgram refinement u (|Abort|) (|Recover|)
                         (transaction_cache_reboot_list n)
                         (transactional_disk_reboot_list n).
Proof.
  unfold transaction_cache_reboot_list, SimulationForProgram,
  SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      
      destruct n; simpl in *; try congruence; cleanup.
      {
        exists (RFinished (snd s_abs, snd s_abs) tt);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
        unfold refines, transaction_rep in *; simpl in *; cleanup.
        intuition eauto.
        pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.
        destruct x0; eauto.
      }
    }
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct n; simpl in *; try congruence; cleanup.
      
      edestruct recovery_simulation; eauto.
      unfold refines, transaction_rep in *; cleanup.
      instantiate (1:=(snd s_abs, snd s_abs)).
      eauto.
      
      exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
      unfold transactional_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Qed.


Lemma commit_simulation :
  forall n u,
    SimulationForProgram refinement u (|Commit|) (|Recover|)
                         (transaction_cache_reboot_list n)
                         (transactional_disk_reboot_list n).
Proof.
  unfold transaction_cache_reboot_list, SimulationForProgram,
  SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      
      destruct n; simpl in *; try congruence; cleanup.
      {
        exists (RFinished (fst s_abs, fst s_abs) tt);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
        unfold refines, transaction_rep in *; simpl in *; cleanup.
        intuition eauto.
        pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.
        destruct x0; eauto.
      }
    }
    {
      intuition cleanup; unify_execs; cleanup;
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup;
      destruct n; simpl in *; try congruence; cleanup.
      
      {
        edestruct recovery_simulation; eauto.
        unfold refines, transaction_rep in *; cleanup.
        instantiate (1:=(snd s_abs, snd s_abs)).
        eauto.

        exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
        unfold transactional_disk_reboot_list; simpl.
        eapply ExecRecovered; eauto.
        repeat econstructor.
      }
      {
        edestruct recovery_simulation; eauto.
        unfold refines, transaction_rep in *; cleanup.
        instantiate (1:=(fst s_abs, fst s_abs)).
        eauto.
        
        exists (Recovered (extract_state_r x0)); simpl; intuition eauto.
        unfold transactional_disk_reboot_list; simpl.
        eapply ExecRecovered; eauto.
        repeat econstructor.
            simpl; eauto.
      }
    }
Qed.


    
Lemma TC_to_TD_core_simulation_finished:
forall u (T : Type) (o0 : TransactionalDiskLayer.transactional_disk_prog T)
(s_imp
 s_imp' : HorizontalComposition.state' (ListOperation (addr * value))
            (LoggedDiskOperation log_length data_length))
(s_abs : total_mem * total_mem) (r : T)
(o_imp : oracle' TransactionCacheOperation)
(t_abs : TransactionalDiskLayer.token')
(grs : HorizontalComposition.state' (ListOperation (addr * value))
         (LoggedDiskOperation log_length data_length) ->
       HorizontalComposition.state' (ListOperation (addr * value))
         (LoggedDiskOperation log_length data_length)),
exec Definitions.imp u o_imp s_imp
(TransactionToTransactionalDisk.Definitions.compile T o0)
(Finished s_imp' r) ->
TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
TransactionToTransactionalDisk.Definitions.token_refines T u s_imp o0 grs
o_imp t_abs ->
exists s_abs' : TransactionalDiskLayer.state',
TransactionalDiskLayer.exec' data_length u t_abs s_abs o0
  (Finished s_abs' r) /\
TransactionToTransactionalDisk.Definitions.refines s_imp' s_abs'.
Proof.
  intros.
  destruct o0; simpl in *; split_ors; 
  cleanup; repeat unify_execs; cleanup.
  
  {
    eapply Transaction.read_finished in H1; cleanup; eauto.
    split_ors; cleanup; eexists; split; eauto;
    econstructor; eauto.
  }
  {
    eapply Transaction.write_finished in H1; cleanup; eauto.
    do 2 split_ors; cleanup; 
    try solve [eexists; split; eauto;
    econstructor; eauto].

    split_ors; cleanup; 
    try solve [eexists; split; eauto;
    econstructor; eauto].
    
    destruct s_imp; cleanup.
    exfalso; eapply cons_l_neq; eauto.
    apply H4.

    destruct s_imp; cleanup.
    exfalso; eapply cons_l_neq; eauto.
    apply H5.

    destruct s_imp; cleanup.
    exfalso; eapply cons_l_neq; eauto.
    apply H1.

    do 2 split_ors; cleanup; 
    try solve [eexists; split; eauto;
    econstructor; eauto].
  }
  {
    eapply Transaction.commit_finished in H1; cleanup; eauto.
    cleanup; eexists; split; eauto.
    destruct r; econstructor; eauto.
  }
  {
    eapply Transaction.abort_finished in H1; cleanup; eauto.
    cleanup; eexists; split; eauto.
    destruct r; econstructor; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    intuition eauto.
    pose proof addr_list_to_blocks_length_le.
    specialize (H []); simpl in *; lia.
  }
  {
    eapply Transaction.recover_finished in H1; cleanup; eauto.
    cleanup; eexists; split; eauto.
    destruct r; econstructor; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.
  }
  {
    eapply Transaction.init_finished in H1; cleanup; eauto.
    cleanup; eexists; split; eauto.
    destruct r; econstructor; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    intuition eauto.
    pose proof addr_list_to_blocks_length_le.
    specialize (H []); simpl in *; lia.
  }
Qed.

Lemma TC_to_TD_core_simulation_crashed:
forall u (T : Type) (o0 : operation Definitions.abs_op T)
(s_imp s_imp' : Language.state' TransactionCacheOperation)
(s_abs : total_mem * total_mem) (o_imp : oracle' TransactionCacheOperation)
(t_abs : TransactionalDiskLayer.token'),
exec Definitions.imp u o_imp s_imp
(TransactionToTransactionalDisk.Definitions.compile T o0) 
(Crashed s_imp') ->
TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
TransactionToTransactionalDisk.Definitions.token_refines T u s_imp o0
TC_reboot_f o_imp t_abs ->

(forall l, ~ eq_dep Type (operation Definitions.abs_op) T o0 unit (TransactionalDiskLayer.Init l)) ->
exists
s_abs' : Core.state
         (TransactionalDiskLayer.TransactionalDiskOperation data_length),
Core.exec (TransactionalDiskLayer.TransactionalDiskOperation data_length) u
t_abs s_abs o0 (Crashed s_abs') /\
TransactionToTransactionalDisk.Definitions.refines_reboot
(TC_reboot_f s_imp') (TD_reboot_f s_abs').
Proof.
  intros.
  destruct o0; simpl in *; split_ors; 
  cleanup; repeat unify_execs; cleanup.
  
  {
    eapply Transaction.read_crashed in H1; cleanup; eauto.
    eexists; split; eauto.
    econstructor; eauto.
    unfold TC_reboot_f, TD_reboot_f; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.
  }
  {
    eapply Transaction.write_crashed in H1; cleanup; eauto.
    eexists; split; eauto.
    econstructor; eauto.
    unfold TC_reboot_f, TD_reboot_f; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.
  }
  {
    eapply Transaction.commit_crashed in H1; cleanup; eauto.
    repeat split_ors; cleanup; eexists; split; eauto;
    try solve [econstructor; eauto].
    
    unfold TC_reboot_f, TD_reboot_f; simpl in *;
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup_no_match; eauto.

    unfold TC_reboot_f, TD_reboot_f; simpl in *;
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup_no_match; eauto.

    unfold TC_reboot_f, TD_reboot_f; simpl in *;
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; logic_clean; rewrite H5; eauto.
    
    unfold TC_reboot_f, TD_reboot_f; simpl in *;
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup_no_match; eauto.
  }
  {
    eapply Transaction.abort_crashed in H1; cleanup; eauto.
    eexists; split; eauto.
    econstructor; eauto.
    unfold TC_reboot_f, TD_reboot_f; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.
  }
  {
    eapply Transaction.recover_crashed in H1; cleanup; eauto.
    eexists; split; eauto.
    econstructor; eauto.
    unfold TC_reboot_f, TD_reboot_f; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.

    unfold TransactionToTransactionalDisk.Definitions.refines_reboot , 
    TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep,  Transaction.transaction_reboot_rep in *; 
    simpl in *; cleanup; eauto.
  }
  {
    exfalso; eapply H2; eauto.
  }
Qed.

Lemma TD_token_refines_finished :
      forall u (T : Type) (op : operation Definitions.abs_op T)
      (x : oracle' TransactionCacheOperation) (r0 : T)
      (s0 s'0 : Language.state' TransactionCacheOperation),
    exec Definitions.imp u x s0
      (compile_core Definitions.TransactionalDiskCoreRefinement op)
      (Finished s'0 r0) ->
    (exists s1 : Core.state Definitions.abs_op,
       refines_core Definitions.TransactionalDiskCoreRefinement s0 s1) ->
    exists
      (grs1 : state Definitions.imp -> state Definitions.imp) 
    (t : TransactionalDiskLayer.token'),
      TransactionToTransactionalDisk.Definitions.token_refines T u s0 op grs1 x t.
      Proof.
      intros; cleanup; destruct op; simpl in *; repeat invert_exec.
      
      - do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        eapply Transaction.read_finished; eauto.
        
      - eapply_fresh Transaction.write_finished in H; eauto.
        split_ors; cleanup; intuition eauto;
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        + left; intuition eauto.
          unfold Transaction.transaction_rep in *; simpl in *.
          cleanup.
          inversion H1; eauto.
        
      - eapply_fresh Transaction.commit_finished in H; eauto;
        cleanup; intuition eauto;
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

      - eapply_fresh Transaction.abort_finished in H; eauto;
      cleanup; intuition eauto;
      do 2 eexists; try exact (fst s0); try exact (snd s0);
      left; do 2 eexists; intuition eauto.
      destruct s'0; simpl in *; cleanup; eauto.

      - eapply_fresh Transaction.recover_finished in H; eauto;
        cleanup; intuition eauto.
        2: {
          unfold TransactionToTransactionalDisk.Definitions.refines,
          Transaction.transaction_rep, Transaction.transaction_reboot_rep in *; simpl in *;
          cleanup; eauto.
        }
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

      - eapply_fresh Transaction.init_finished in H; eauto;
        cleanup; intuition eauto.
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup; eauto.
      Qed.

      Lemma TD_token_refines_crashed :
      forall u (T : Type) (op : operation Definitions.abs_op T)
  (x : oracle' TransactionCacheOperation)
  (s0 s'0 : Language.state' TransactionCacheOperation),
exec Definitions.imp u x s0
  (compile_core Definitions.TransactionalDiskCoreRefinement op) 
  (Crashed s'0) ->
(exists s1 : Core.state Definitions.abs_op,
   refines_core Definitions.TransactionalDiskCoreRefinement s0 s1) ->
   (forall l, ~ Logic.EqdepFacts.eq_dep Type (operation Definitions.abs_op)  T op unit (TransactionalDiskLayer.Init l)) ->
   exists
  (grs1 : state Definitions.imp -> state Definitions.imp) 
(t : TransactionalDiskLayer.token'),
  TransactionToTransactionalDisk.Definitions.token_refines T u s0 op grs1 x t.
      Proof.
      intros; cleanup; destruct op; simpl in *; repeat invert_exec.
      
      - do 2 eexists; try exact (fst s0); try exact (snd s0);
        right; eexists; intuition eauto.
        eapply Transaction.read_crashed; eauto.
        
      - eapply_fresh Transaction.write_crashed in H; eauto.
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        right; eexists; intuition eauto.
        
      - eapply_fresh Transaction.commit_crashed in H; eauto;
        cleanup; intuition eauto;
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        right; eexists; intuition eauto.
        left; destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

        right; destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

      - eapply_fresh Transaction.abort_crashed in H; eauto;
      cleanup; intuition eauto;
      do 2 eexists; try exact (fst s0); try exact (snd s0);
      right; eexists; intuition eauto.

      - eapply_fresh Transaction.recover_crashed in H; eauto;
        cleanup; intuition eauto.
        2: {
          unfold TransactionToTransactionalDisk.Definitions.refines,
          Transaction.transaction_rep, Transaction.transaction_reboot_rep in *; simpl in *;
          cleanup; eauto.
        }
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        right; eexists; intuition eauto.

      - exfalso; eapply H1; eauto.
      Qed.


Lemma TD_token_refines :
      forall u (T : Type) (op : operation Definitions.abs_op T)
  (x : oracle' TransactionCacheOperation)
  (s0 : Language.state' TransactionCacheOperation) ret,
exec Definitions.imp u x s0
  (compile_core Definitions.TransactionalDiskCoreRefinement op) 
  ret ->
(exists s1 : Core.state Definitions.abs_op,
   refines_core Definitions.TransactionalDiskCoreRefinement s0 s1) ->
   (forall l, ~ Logic.EqdepFacts.eq_dep Type (operation Definitions.abs_op)  T op unit (TransactionalDiskLayer.Init l)) ->
   exists
  (grs1 : state Definitions.imp -> state Definitions.imp) 
(t : TransactionalDiskLayer.token'),
  TransactionToTransactionalDisk.Definitions.token_refines T u s0 op grs1 x t.
Proof.
  intros.
  destruct ret.
  eapply TD_token_refines_finished; eauto.
  eapply TD_token_refines_crashed; eauto.
Qed.