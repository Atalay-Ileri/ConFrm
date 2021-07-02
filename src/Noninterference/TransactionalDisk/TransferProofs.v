Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer TransferProofs ATCSimulation ATCAOE.

(* Notation "'TransactionalDiskCore'" := (TransactionalDiskOperation data_length). *)

Import FileDiskLayer.
Set Nested Proofs Allowed.

Theorem recovery_exec_termination_sensitive_bind:
  forall O (L: Language O) 
  T (p1 p2: L.(prog) T) 
  T' (p3 p4: T -> L.(prog) T') rec s1 s2 
  lob l_grs u s1',
  (forall s1' lo lgrs, 
  recovery_exec L u lo s1 lgrs p1 rec s1' ->
   exists s2',
   recovery_exec L u lo s2 lgrs p2 rec s2') ->

  (forall s1' s2' s1r t1 t2 lo lo' lgrs, 
  recovery_exec L u lo s1 [] p1 rec (RFinished s1' t1) ->
  recovery_exec L u lo s2 [] p2 rec (RFinished s2' t2) ->
    
  recovery_exec L u lo' s1' lgrs (p3 t1) rec s1r ->
  exists s2r,
  recovery_exec L u lo' s2' lgrs (p4 t2) rec s2r) ->

  recovery_exec L u lob s1 l_grs (Bind p1 p3) rec s1' ->
   exists s2',
   recovery_exec L u lob s2 l_grs (Bind p2 p4) rec s2'.
Proof.
  intros; repeat invert_exec.
  {
      invert_exec'' H10.

      edestruct H.
      econstructor; eauto.
      invert_exec.

      edestruct H0; eauto;
      try solve [econstructor; eauto].
      invert_exec.

      eexists; repeat econstructor; eauto.
  }
  {
    invert_exec'' H9.
    {
      edestruct H.
      econstructor; eauto.
      invert_exec.

      edestruct H0; eauto;
      try solve [econstructor; eauto].
      invert_exec.

      eexists; repeat econstructor; eauto.
    }
    {
      edestruct H.
      eapply ExecRecovered; eauto.
      invert_exec.
      eexists; eapply ExecRecovered; eauto.
      eapply ExecBindCrash; eauto.
    }
  }
Qed.


Lemma not_init_read:
forall inum off,
not_init (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off))).
{
        simpl.
        Transparent Inode.get_owner.
        unfold Inode.get_owner, Inode.get_inode,
        Inode.InodeAllocator.read; simpl.
        intuition eauto.
        destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) inum);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct u0; simpl; intuition eauto.
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number,
         Inode.get_inode, 
         Inode.InodeAllocator.read ; simpl; intuition eauto.
        destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) inum);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        unfold File.DiskAllocator.read; simpl; intuition eauto.
        destruct (Compare_dec.lt_dec a File.DiskAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) a);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        all: inversion H.
      }
Qed.


Lemma abstract_oracles_exist_wrt_compositional:
forall (C_imp C_abs: Core)
 (L_imp: Language C_imp)
 (L_abs: Language C_abs)
 (CoreRefinement : CoreRefinement L_imp C_abs)
u l_grs T (p1: prog L_abs T) T' (p2: T -> prog L_abs T') rec, 
let R := LiftRefinement L_abs CoreRefinement in
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p1 rec [] ->
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p1 rec l_grs ->
(forall t, abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u (p2 t) rec l_grs) ->
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u (Bind p1 p2) rec l_grs.
Proof.
    unfold abstract_oracles_exist_wrt; 
    simpl; intros;
    repeat invert_exec.
    {
        invert_exec'' H12.
        edestruct H; eauto.
        econstructor; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

        edestruct H1; eauto.
        econstructor; eauto.

        simpl in *; cleanup; try intuition; simpl in *; try congruence;
        cleanup; repeat unify_execs; cleanup.
        exists [o0++o].
        simpl; split; eauto.
        repeat left.
        do 2 eexists; econstructor; eauto.
        econstructor; eauto.
        intuition eauto.
        right; do 7 eexists; intuition eauto.
    }
    {
        invert_exec'' H11.
        {
            edestruct H; eauto.
            econstructor; eauto.

            eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

            edestruct H1; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists ((o0++o)::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            econstructor; eauto.
            intuition eauto.
            right; do 7 eexists; intuition eauto.
        }
        {
            edestruct H0; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            eexists (_::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            eapply ExecBindCrash; eauto.
        }
    }
Qed.

Lemma AOE_change_refinement:
  forall O O1 O2 
  (L: Language O)
  (L1: Language O1)
  (L2: Language O2)
  (CR1: CoreRefinement L1 O)
  (CR2: CoreRefinement L2 O)
  u T (p: L.(prog) T) rec l_grs1 l_grs2,
  let R1:= LiftRefinement L CR1 in
  let R2 := LiftRefinement L CR2 in
  ( forall sa si2 l_oi2 si2',  
  Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
recovery_exec L2 u l_oi2 si2 l_grs2
  (Simulation.Definitions.compile (LiftRefinement L CR2) p)
  (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->
  exists si1 l_oi1 si1',
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa /\
  recovery_exec L1 u l_oi1 si1 l_grs1
        (Simulation.Definitions.compile (LiftRefinement L CR1) p)
        (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1') ->

  (forall l_oi1 l_oi2 l_oa si1 si2 sa si1' si2',
    Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa ->
  recovery_exec L2 u l_oi2 si2 l_grs2
          (Simulation.Definitions.compile (LiftRefinement L CR2) p) 
          (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->  
  recovery_exec L1 u l_oi1 si1 l_grs1
    (Simulation.Definitions.compile (LiftRefinement L CR1) p)
    (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1' ->
    recovery_oracles_refine_to (LiftRefinement L CR1) u si1 p rec l_grs1 l_oi1 l_oa ->
    exists l_oa : list (oracle L),
    recovery_oracles_refine_to (LiftRefinement L CR2) u si2 p rec l_grs2 l_oi2 l_oa) ->
  
  abstract_oracles_exist_wrt R1
    R1.(Simulation.Definitions.refines) u
    p rec l_grs1 ->
  abstract_oracles_exist_wrt R2
    R2.(Simulation.Definitions.refines) u
    p rec l_grs2.
Proof.
  unfold abstract_oracles_exist_wrt; intros.
  cleanup.
  eapply_fresh H in H3; eauto; cleanup.
  eapply_fresh H1 in H5; eauto; cleanup.
  eapply H0; eauto.
Qed.

Lemma ATC_simulation_crash:
forall u inum off (o : oracle' ATCCore) (s : state ATCLang)
  (s' : Language.state' ATCCore),
(exists s1 : state AuthenticatedDisk,
   Simulation.Definitions.refines ATC_Refinement s s1) ->
exec ATCLang u o s
  (Simulation.Definitions.compile ATC_Refinement
     (Simulation.Definitions.compile FileDisk.refinement
        (| Read inum off |))) (Crashed s') ->

          
  (forall T o s_imp s_imp' s_abs r o_imp t_abs grs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Finished s_imp' r) ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o grs o_imp t_abs ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TransactionalDiskOperation
data_length) u t_abs s_abs o (Finished s_abs' r) /\
  TransactionToTransactionalDisk.Definitions.refines s_imp' s_abs') ->
  
  (forall T o s_imp s_imp' s_abs o_imp t_abs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Crashed s_imp') ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o TC_reboot_f o_imp t_abs ->
  (forall l, ~ eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TransactionalDiskOperation
data_length) u t_abs s_abs o (Crashed s_abs') /\
  TransactionToTransactionalDisk.Definitions.refines_reboot (TC_reboot_f s_imp') (TD_reboot_f s_abs')) ->

exists s1' : total_mem * total_mem,
  TransactionToTransactionalDisk.Definitions.refines_reboot
    (snd s') s1'.
    Proof.
      intros; cleanup.
      eapply_fresh ATC_oracle_refines_crashed in H0; eauto.
      cleanup.
      eapply ATC_exec_lift_crashed in H0; eauto.
      cleanup; simpl in *.
      unfold TC_reboot_f, TD_reboot_f in *; simpl in *.
      eexists; unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
      Transaction.transaction_reboot_rep  in ; simpl in *; eauto.
      apply not_init_read.
      simpl in *; eauto.
      apply not_init_read.
    Qed.



  Lemma ATC_AOE_read:
  forall n inum off u,
  abstract_oracles_exist_wrt ATC_Refinement
(Simulation.Definitions.refines ATC_Refinement) u
(Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
(Simulation.Definitions.compile FileDisk.refinement (| Recover |))
(ATC_reboot_list n).
Proof.
  intros; eapply ATC_AOE_2.
  {
    intros.
    eapply ATC_oracle_refines_finished; eauto.
  }
  {
    intros.
    eapply ATC_oracle_refines_crashed; eauto.
    apply not_init_read.
  }
  {
    intros;
    eapply ATC_simulation_crash; eauto.
    apply TC_to_TD_core_simulation_finished; eauto.
      eapply TC_to_TD_core_simulation_crashed; eauto.
  }
Qed.

Opaque File.read File.recover.
Lemma ROR_transfer_recovery:
forall l_o_imp l_o_abs n u s1_imp x, 
recovery_oracles_refine_to ATC_Refinement u s1_imp 
File.recover File.recover (ATC_reboot_list n) l_o_imp l_o_abs ->
TransactionToTransactionalDisk.Definitions.refines_reboot (snd s1_imp) (snd x) ->
fst s1_imp = fst x ->
exists l_o_abs',
recovery_oracles_refine_to FileDisk.refinement u x 
(| Recover |) (| Recover |) (authenticated_disk_reboot_list n)
l_o_abs l_o_abs'.
Proof.
  induction l_o_imp; simpl; intros; intuition.
  destruct l_o_abs; intuition.
  {
    simpl in *; cleanup.
    eapply ATC_exec_lift_finished_recovery in H; eauto; cleanup.
    eexists [_].
    simpl; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
    destruct x1; eauto.
    eapply FileSpecs.recover_finished in H; eauto.
  }
  {
    cleanup; intuition.
    unfold ATC_reboot_list in *; 
    destruct n; simpl in *; try congruence.
    cleanup.

    edestruct IHl_o_imp; eauto.
    instantiate (1:= (fst x0, (snd (snd x0), snd(snd x0)))).
    all: simpl; eauto.
    
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep   in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
    Transaction.transaction_reboot_rep; eauto.
    cleanup.
    simpl in *.
    eapply_fresh ATC_exec_lift_crashed_recovery in H; eauto; cleanup.

    eexists (_::_); simpl.
    intuition eauto.
    eapply recovery_oracles_refine_to_length in H5; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    right; eexists; intuition eauto.
    eapply FileSpecs.recover_crashed in H6; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
    Transaction.transaction_reboot_rep  in *; 
    setoid_rewrite <- H8.
    setoid_rewrite H7; eauto.
  }
Qed.

(* Need to figure out oracles instead of exists *)
Lemma ROR_transfer:
forall l_o_imp l_o_abs n u s1_imp x inum off , 
recovery_oracles_refine_to ATC_Refinement u s1_imp 
(File.read inum off) File.recover (ATC_reboot_list n) l_o_imp l_o_abs ->
TransactionToTransactionalDisk.Definitions.refines (snd s1_imp) (snd x) ->
fst s1_imp = fst x ->
exists l_o_abs',
recovery_oracles_refine_to FileDisk.refinement u x 
(| Read inum off |) (| Recover |) (authenticated_disk_reboot_list n)
l_o_abs l_o_abs'.
Proof.
  induction l_o_imp; simpl; intros; intuition.
  
  destruct l_o_abs; intuition.
  {
    simpl in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto.
    2: simpl; unfold HC_refines; eauto.
    cleanup.
    eexists [_].
    simpl; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eapply FileSpecs.read_finished in H; cleanup; eauto.
    simpl.
    
    apply TC_to_TD_core_simulation_finished; eauto.
  }
  {
    cleanup; intuition.
    unfold ATC_reboot_list in *; 
    destruct n; simpl in *; try congruence.
    cleanup.

    eapply ATC_exec_lift_crashed in H; eauto; cleanup.
    eapply ROR_transfer_recovery in H4; eauto.
    cleanup.
    eexists (_::_).
    simpl; intuition eauto.
    eapply recovery_oracles_refine_to_length in H4; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    right; eexists; intuition eauto.
    eapply FileSpecs.read_crashed in H; eauto.
    simpl; unfold HC_refines; eauto.
    apply TC_to_TD_core_simulation_finished; eauto.
    apply TC_to_TD_core_simulation_crashed; eauto.
    apply not_init_read.
  }
Qed.

Opaque Inode.get_owner File.read_inner.
Theorem ss_ATC_read:
  forall n inum off u u',
    SelfSimulation u 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros. 
    eapply SS_transfer.
    - apply ss_AD_read.
    - eapply ATC_simulation.
      apply not_init_read.
    - eapply ATC_simulation.
      apply not_init_read.
    - apply ATC_AOE_read.
    - apply ATC_AOE_read.
    - 

      Set Nested Proofs Allowed.

      Ltac unify_execs_prefix :=
                match goal with 
                | [ H: Language.exec' ?u ?o1 ?s ?p (Finished _ _),
                    H0: Language.exec' ?u ?o2 ?s ?p (Finished _ _),
                    H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
                    eapply exec_finished_deterministic_prefix in H; [|apply H0| apply H1]
                | [ H: exec _ ?u ?o1 ?s ?p (Finished _ _),
                    H0: exec _ ?u ?o2 ?s ?p (Finished _ _),
                    H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
                    eapply exec_finished_deterministic_prefix in H; [|apply H0| apply H1]
                | [ H: Language.exec' ?u ?o1 ?s ?p (Finished _ _),
                    H0: Language.exec' ?u ?o2 ?s ?p (Crashed _),
                    H1: ?o1 ++ _ = ?o2 ++ _ |- _] =>
                    exfalso; eapply finished_not_crashed_oracle_prefix; [apply H| apply H1 | apply H0]
                | [ H: Language.exec' ?u ?o1 ?s ?p (Finished _ _),
                    H0: Language.exec' ?u (?o1 ++ _) ?s ?p (Crashed _) |- _] =>
                    exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
                    try solve [rewrite <- app_assoc; eauto]
                | [ H: Language.exec' ?u ?o1 ?s ?p (Finished _ _),
                    H0: exec _ ?u (?o1 ++ _) ?s ?p (Crashed _) |- _] =>
                    exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
                    try solve [rewrite <- app_assoc; eauto]
                | [ H: Language.exec' ?u ?o1 ?s ?p (Finished _ _),
                    H0: exec _ ?u ?o2 ?s ?p (Crashed _),
                    H1: ?o1 ++ _ = ?o2 |- _] =>
                    exfalso; eapply finished_not_crashed_oracle_prefix in H0; eauto;
                    try solve [rewrite <- app_assoc; setoid_rewrite app_nil_r at 2; eauto]
                end.
      
      Lemma ATC_ORS_read:
      forall n u u' inum off,
      oracle_refines_same_from_related ATC_Refinement u
      (Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
      (Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
      (Simulation.Definitions.compile FileDisk.refinement (| Recover |))
      (ATC_reboot_list n) (AD_related_states u' None).
      Proof.
        unfold oracle_refines_same_from_related; simpl.
        induction l_o_imp; intros; intuition.
        {
          destruct l_o_abs, l_o_abs'; intuition; cleanup;
          simpl in *; try lia.
          cleanup_no_match.
          repeat split_ors; cleanup_no_match; simpl in *; try lia.
          {
            unfold refines_related, AD_related_states, refines_related in *; 
            simpl in *; cleanup.
            (*
            eapply ATC_exec_lift_finished in H2; simpl; eauto; cleanup.
            eapply ATC_exec_lift_finished in H3; simpl; eauto; cleanup.
            *)
            {
              Transparent File.read.
              unfold File.read, File.auth_then_exec in *; simpl in *.
              invert_exec'' H2; invert_exec'' H3.
              repeat split_ors; cleanup_no_match; repeat unify_execs_prefix; cleanup_no_match.

                  eapply exec_finished_deterministic_prefix in H15; eauto; cleanup_no_match;
                  try solve [rewrite H0; eauto].
              eapply exec_finished_deterministic_prefix in H7; eauto; cleanup_no_match.

              eapply ATC_exec_lift_finished in H13; simpl; eauto; cleanup_no_match;
              try solve [apply TC_to_TD_core_simulation_finished; eauto].
              eapply ATC_exec_lift_finished in H14; simpl; eauto; cleanup_no_match;
              try solve [apply TC_to_TD_core_simulation_finished; eauto].
              apply lift2_invert_exec in H7; cleanup_no_match.
              apply lift2_invert_exec in H3; cleanup_no_match.
              
              Search oracle_refines.
              Lemma TD_ORS_:
      forall n u u' inum off,
      oracle_refines_same_from_related ATC_Refinement u
      (Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
      (Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
      (Simulation.Definitions.compile FileDisk.refinement (| Recover |))
      (ATC_reboot_list n) (AD_related_states u' None).
      Proof.

              eapply Inode.get_owner_finished_oracle_eq in H15; eauto. [|eauto; cleanup_no_match].
              destruct x12, x19; try solve [intuition congruence].
            invert_exec.

        erewrite RefinesSame.ORS_read with (l_o_abs' := [o0]). eauto.


        pose proof RefinesSame.ORS_read.
        unfold oracle_refines_same_from_related in *; simpl in *.
        unfold refines_related in H; simpl in *.
        unfold AD_related_states, FD_related_states, 
        HC_refines in *; simpl in *.
        cleanup.
        specialize H2 with (1:= H4).
        eapply ROR_transfer in H0; eauto; cleanup.
        eapply ROR_transfer in H1; eauto; cleanup.
        simpl in *.
        specialize H2 with (1:= H0)(2:= H1). 

       

    

    admit. (*oracle_refines_same_from_related*)
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - admit. (* SelfSimulation_Exists *)
Abort.