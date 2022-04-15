Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATC_ORS ATCDLayer ATC_Simulation HSS ATC_TransferProofs.
Require Import ATCD_Simulation ATCD_AOE.
Require Import Not_Init ATCD_ORS ATCD_TIE. (* ATCD_TS. *)

Import FileDiskLayer.
Set Nested Proofs Allowed.


Lemma AOE_explicit_to_AOE:
forall O1 O2 (L1: Layer O1) (L2: Layer O2) (Ref: Refinement L1 L2) 
R u T (p: prog L2 T) rec l_grs,
(forall l_o s1 s2,
abstract_oracles_exist_wrt_explicit Ref R u p rec l_grs l_o s1 s2) ->
abstract_oracles_exist_wrt Ref R u p rec l_grs.
Proof.
  unfold abstract_oracles_exist_wrt_explicit, 
  abstract_oracles_exist_wrt; eauto.
Qed.


(********** Transfer Theorems ***********)
Opaque File.read File.recover.
Theorem ss_ATCD_read:
  forall n inum off u u' lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Read inum off |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Read inum off |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
  RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Read inum off))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Read inum off))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' None)))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_read.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_read. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_read].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_read; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_read].
    eapply TIE_auth_then_exec; eauto.
    apply TIE_read_inner.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.

Opaque File.write File.recover.
Theorem ss_ATCD_write:
  forall n inum off u u' v lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Write inum off v |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Write inum off v |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
  RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Write inum off v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Write inum off v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' None)))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_write.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.               
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_write. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_write].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_write; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_write].
    eapply TIE_auth_then_exec; eauto.
    intros; eapply TIE_write_inner; eauto.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.


Opaque File.create File.recover.
Theorem ss_ATCD_create:
  forall n u u' v lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Create v |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Create v |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
    RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Create v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Create v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' None)))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_create.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_write. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_create].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_create; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_create].
    intros; eapply TIE_create; eauto.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.

Opaque File.extend File.recover.
Theorem ss_ATCD_extend:
  forall n u u' inum v lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Extend inum v |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Extend inum v |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
    RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Extend inum v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Extend inum v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' None)))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_extend.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_write. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_extend].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_extend; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_extend].
    intros; eapply TIE_auth_then_exec; eauto.
    intros; eapply TIE_extend_inner; eauto.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.

Opaque File.change_owner File.recover.
Theorem ss_ATCD_change_owner:
  forall n u u' inum v lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| ChangeOwner inum v |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| ChangeOwner inum v |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
    RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (ChangeOwner inum v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (ChangeOwner inum v))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' (Some inum))))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_change_owner.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_write. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_change_owner].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_change_owner; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_change_owner].
    intros; eapply TIE_auth_then_exec; eauto.
    intros. eapply TIE_change_owner_inner; eauto.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.


Opaque File.delete File.recover.
Theorem ss_ATCD_delete:
  forall n u u' inum lo s1 s2,
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Delete inum |))))
  (Simulation.Definitions.compile ATCD_Refinement
     (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s1 -> 
  non_colliding_selector_list u
  (Simulation.Definitions.refines ATCD_Refinement)
  (Simulation.Definitions.refines_reboot ATCD_Refinement) n
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement
        (Simulation.Definitions.compile FD.refinement (| Delete inum |))))
  (Simulation.Definitions.compile ATCD_Refinement
    (Simulation.Definitions.compile ATC_Refinement File.recover)) lo s2 -> 
    RDNI_explicit u lo s1 s2
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Delete inum))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) (Delete inum))))) 
    (ATCD_Refinement.(Simulation.Definitions.compile) 
    (ATC_Refinement.(Simulation.Definitions.compile) 
    (FD.refinement.(Simulation.Definitions.compile) 
    (FDOp.(Op) Recover)))) 
    (refines_valid ATCD_Refinement (refines_valid ATC_Refinement AD_valid_state))
    (refines_related ATCD_Refinement
    (refines_related ATC_Refinement (AD_related_states u' None)))
    (eq u') (ATCD_reboot_list n).
Proof.
  intros.
  eapply RDNI_explicit_transfer.
  - apply ss_ATC_delete.
  - eapply ATCD_simulation.
    shelve.
  - eapply ATCD_simulation.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - intros; apply ATCD_AOE; eauto.
    shelve.
  - eapply ATCD_ORS_transfer; simpl.
    all: shelve.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - unfold exec_compiled_preserves_validity, AD_valid_state, 
  refines_valid, FD_valid_state; 
  intros; simpl; eauto.
  - admit. (* apply ATCD_TS_write. *)
  Unshelve.
  all: simpl; try solve [try apply not_init_compile; apply not_init_delete].
  {
    unfold refines_related; simpl; intros.
    cleanup.
    eapply ATC_HRDNI_transfer; simpl; eauto.
    eapply have_same_structure_delete; eauto.
    all: simpl; try solve [try apply not_init_compile; apply not_init_delete].
    intros; eapply TIE_auth_then_exec; eauto.
    intros. eapply TIE_delete_inner; eauto.
    unfold refines_related; simpl; intuition eauto.
  }
Admitted.




Opaque File.recover.
Lemma ATCD_TS_read_inner:
    forall n inum off u u' txns1 txns2 hdr1 hdr2,
    Termination_Sensitive u
    (Simulation.Definitions.compile
    ATCD_Refinement
   (Simulation.Definitions.compile
    ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _
    (File.read_inner off inum))))
   (Simulation.Definitions.compile
    ATCD_Refinement
   (Simulation.Definitions.compile
    ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _
    (File.read_inner off inum))))
    (Simulation.Definitions.compile
    ATCD_Refinement
    (Simulation.Definitions.compile
    ATC_Refinement
    File.recover))
   (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
    AD_valid_state))
  (fun s1 s2 => refines_related ATCD_Refinement (refines_related ATC_Refinement ( (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a /\
  fst (snd s1) = Empty /\ fst (snd s2) = Empty))) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2)
     (ATCD_reboot_list n).
  Proof.
    Transparent File.read_inner.
    intros; unfold File.read_inner.
    eapply ATCD_TS_compositional.
    intros; eapply TS_eqv_impl.
    eapply ATCD_TS_get_block_number.
    simpl; intros; shelve.
    2: intros; shelve.

    intros; unfold refines_related in *; cleanup.
    intros; unfold refines_related in *; cleanup.
    eapply_fresh ATCD_oracle_refines_finished in H; eauto.
    eapply_fresh ATCD_oracle_refines_finished in H0; eauto.
    cleanup.

    eapply_fresh ATCD_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply_fresh ATCD_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    eapply_fresh ATCD_oracle_refines_impl_eq in H11; eauto.
    2: shelve. (* eapply have_same_structure_get_owner; eauto. *)
    2: apply TC_oracle_refines_operation_eq.
    cleanup.

    clear H H0.

    eapply_fresh ATC_oracle_refines_finished in H13; eauto.
    eapply_fresh ATC_oracle_refines_finished in H15; eauto.
    cleanup.
    eapply_fresh ATC_exec_lift_finished in H13; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply_fresh ATC_exec_lift_finished in H15; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    eapply ATC_oracle_refines_impl_eq in H; eauto.
    2: shelve.
    2: apply TD_oracle_refines_operation_eq.
    cleanup.

    clear H13 H15.

    eapply lift2_invert_exec in H17;
    eapply lift2_invert_exec in H19; cleanup.
    apply HC_map_ext_eq in H; subst.

    unfold File.files_inner_rep in *; cleanup.
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H21; eauto; subst.
    cleanup; destruct r1, r2; try solve [intuition congruence].
    2: intros; eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve].
    
    eapply ATCD_TS_compositional.
    2: intros; destruct r1, r2; (eapply TS_eqv_impl; [apply ATCD_TS_ret | shelve]).
    2: shelve.
    simpl; intros; repeat invert_exec; try congruence.
    eapply TS_eqv_impl. 
    eapply ATCD_TS_DiskAllocator_read.
    {
      eapply Inode.get_block_number_finished in H21; eauto.
      eapply Inode.get_block_number_finished in H17; eauto.
      cleanup; repeat split_ors; cleanup; intuition eauto.
      eapply SameRetType.all_block_numbers_in_bound in H.
      3: eauto.
      all: eauto.
      eapply Forall_forall in H; eauto.
      eapply in_seln; eauto.
      
      eapply SameRetType.all_block_numbers_in_bound in H6.
      3: eauto.
      all: eauto.
      eapply Forall_forall in H6; eauto.
      apply in_seln; eauto.
    }
    {
      eapply Inode.get_block_number_finished in H21; eauto.
      eapply Inode.get_block_number_finished in H17; eauto.

      cleanup; repeat split_ors; cleanup; intuition eauto.
      eapply data_block_inbounds; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      eapply data_block_inbounds.
      4: eauto.
      all: eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
    }
    {
      shelve. (*
      instantiate (2:= refines_related ATCD_Refinement
      (fun s1 s2  => 
      exists s1a s2a, 
      (Inode.inode_rep im1 (fst (snd (snd s1))) /\
          (exists file_block_map,
              File.DiskAllocator.block_allocator_rep file_block_map
                (fst (snd (snd s1))) /\
              File.file_map_rep s1a im1 file_block_map)) /\
        (Inode.inode_rep im2 (fst (snd (snd s2))) /\
          (exists file_block_map,
              File.DiskAllocator.block_allocator_rep file_block_map
                (fst (snd (snd s2))) /\
              File.file_map_rep s2a im2 file_block_map)) /\
      FD_related_states u' None s1a s2a /\
      fst (snd s1) = Empty /\
      fst (snd s2) = Empty)).
        
        simpl; intros.
        unfold refines_related in *.
        cleanup.
        split.
        unfold File.files_inner_rep.
        do 2 eexists; intuition eauto.
        do 2 eexists; intuition eauto.

        simpl in *; unfold HC_refines in H12, H21; cleanup.
        simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep  in *; cleanup; 
        repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H34;
      eapply txn_length_0_empty in H38; subst.
      setoid_rewrite H34;
      setoid_rewrite H38.
      simpl; intuition eauto.

      rewrite H38, H34 in *; simpl in *.
      eapply Inode.get_block_number_finished in H20; eauto.
      eapply Inode.get_block_number_finished in H18; eauto.
      cleanup; repeat split_ors; cleanup; intuition eauto.
      repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto.
      *)
    }
    shelve.
    shelve.
    shelve.
    shelve.
    all: unfold Simulation.Definitions.refines in *; simpl in *; eauto.

    Unshelve.
    41: instantiate (5 := fun _ _ => _); simpl; eauto.
    all: eauto.
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      simpl in *.
      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      do 2 eexists; intuition eauto. 

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H14;
      setoid_rewrite H14.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H18;
      setoid_rewrite H18.
      simpl; eauto.
    }
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_block_number_oracle_refines_exists in H; eauto.
      eapply_fresh get_block_number_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H12; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H14;
      eapply lift2_invert_exec in H16; cleanup.
      apply map_ext_eq in H12; cleanup.
      2: intros; cleanup; intuition congruence.
      unfold File.files_inner_rep in *; cleanup.
      eapply Inode.get_block_number_finished in H20; eauto.
      eapply Inode.get_block_number_finished in H18; eauto.
      cleanup.
      clear H12 H20.
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
      
      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      setoid_rewrite H26; eauto.
      setoid_rewrite H22; eauto.

      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
    }
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.
    {
      intros.
      match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold FD_related_states,
       same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold File.file_map_rep in *; cleanup.
       match goal with
       | [H: ?x1 ?inum = Some _,
          H0: ?x2 ?inum = Some _,
          H1: forall (_: Inode.Inum) _ _, 
          ?x1 _ = Some _ ->
          _ _ = Some _ -> _,
          H2: forall (_: Inode.Inum) _ _, 
          ?x2 _ = Some _ ->
          _ _ = Some _ -> _ |- _] =>
          eapply H1 in H; eauto; cleanup;
          eapply H2 in H0; eauto; cleanup
       end.
       unfold File.file_rep in *; cleanup; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.
    Opaque File.read_inner.


Opaque Inode.get_owner.
Lemma ATCD_TS_read:
    forall n inum off u u' txns1 txns2 hdr1 hdr2 lo s1 s2,
    Termination_Sensitive_explicit u lo s1 s2
    (Simulation.Definitions.compile
    ATCD_Refinement
   (Simulation.Definitions.compile
    ATC_Refinement
    (File.read inum off)))
   (Simulation.Definitions.compile
    ATCD_Refinement
   (Simulation.Definitions.compile
    ATC_Refinement
    (File.read inum off)))
    (Simulation.Definitions.compile
    ATCD_Refinement
    (Simulation.Definitions.compile
    ATC_Refinement
    File.recover))
   (refines_valid ATCD_Refinement
     (refines_valid ATC_Refinement
    AD_valid_state))
  (fun s1 s2 => refines_related ATCD_Refinement (refines_related ATC_Refinement (AD_related_states u' None)) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2)
     (ATCD_reboot_list n).
  Proof.
    Opaque File.read_inner Transaction.commit.
    intros; simpl.
    eapply ATCD_TS_explicit_compositional.
    {
      intros; eapply TS_explicit_to_TS; 
      eapply TS_eqv_impl;
      [apply ATCD_TS_get_owner | shelve].
      (*
      unfold refines_related, AD_related_states; 
      simpl. unfold refines_related; simpl.
      unfold refines, File.files_rep; simpl. 
      intros; cleanup; intuition eauto.
      do 2 eexists; intuition eauto.
      rewrite H4, H6;
      do 2 eexists; intuition eauto.
      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H12;
      setoid_rewrite H12.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H16;
      setoid_rewrite H16.
      simpl; eauto.
      *)
    }
    {
      intros; unfold refines_related in *; cleanup.
      eapply_fresh ATCD_oracle_refines_finished in H0; eauto.
      eapply_fresh ATCD_oracle_refines_finished in H1; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H8; eauto.
      2: shelve. (* eapply have_same_structure_get_owner; eauto. *)
      2: apply TC_oracle_refines_operation_eq.
      cleanup.

      eapply_fresh ATC_oracle_refines_finished in H10; eauto.
      eapply_fresh ATC_oracle_refines_finished in H12; eauto.
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H10; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H12; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATC_oracle_refines_impl_eq in H8; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      repeat invert_lift2; cleanup.
      apply HC_map_ext_eq in H8; cleanup.

      eapply_fresh get_owner_related_ret_eq in H21; eauto; subst.
      destruct r1.
      2: intros; eapply TS_explicit_to_TS;
      eapply TS_eqv_impl;
      [ apply ATCD_TS_abort_then_ret| shelve].
      
      eapply ATCD_TS_explicit_compositional.
      intros; eapply TS_explicit_to_TS; 
      eapply TS_eqv_impl; 
      [apply ATCD_TS_Authentication_auth | shelve].
      2: shelve.
      simpl; intros; repeat invert_exec; try congruence.
      2: intros; eapply TS_explicit_to_TS;
      eapply TS_eqv_impl;
      [ apply ATCD_TS_abort_then_ret| shelve].
      eapply ATCD_TS_explicit_compositional.

      (**** This part varies in proofs ****)
      intros; eapply ATCD_TS_read_inner.
      intros.
      {
        instantiate (1:= refines_related ATCD_Refinement
        (fun s3 s4 : state AD =>
         exists s1a s2a : disk File,
           File.files_inner_rep s1a (fst (snd (snd s3))) /\
           File.files_inner_rep s2a (fst (snd (snd s4))) /\
           FD_related_states u' None s1a s2a /\
           fst (snd s3) = Empty /\ fst (snd s4) = Empty)) in H13; simpl in *; cleanup.
           unfold refines_related, FD_related_states in *; simpl in *; cleanup.

          eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
          eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
          cleanup.
          eapply_fresh ATCD_exec_lift_finished in H4; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
          cleanup.
          eapply_fresh ATCD_exec_lift_finished in H6; eauto;
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
          try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
          cleanup.
          simpl in *.

          eapply lift2_invert_exec in H22;
          eapply lift2_invert_exec in H24; cleanup.
          
          eapply ATCD_oracle_refines_impl_eq in H21.
          2: apply H20.
          all: simpl in *; eauto.
          2: apply TD_oracle_refines_operation_eq.
          apply map_ext_eq in H21; cleanup.
          2: intros; cleanup; intuition congruence.
          eapply SameRetType.read_inner_finished_oracle_eq in H27.
          2: apply H29.
          all: eauto.
          cleanup.
          destruct r1, r2; try solve [intuition congruence].
          intros; apply ATCD_TS_commit_then_ret.
          intros; apply ATCD_TS_abort_then_ret.
          eapply have_same_structure_read_inner; eauto.
          do 2 eexists; intuition eauto.
          unfold FD_related_states; 
          apply TSCommon.same_for_user_except_symmetry; eauto.
          apply not_init_read_inner.
          apply not_init_read_inner.
      }
      (**************)
      intros; shelve.
    }
    intros; shelve.
    Unshelve.
    all: try exact u'.
    all: eauto.
    all: try solve [exact (fun _ _ => True)].
    all: try solve [simpl; eauto].
    {
      simpl; intros;
      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      repeat invert_exec; destruct s0, s3; simpl in *; eauto;
        do 2 eexists; intuition eauto;
        do 2 eexists; intuition eauto.
    }
    2:{
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_owner_oracle_refines_exists in H; eauto.
      eapply_fresh get_owner_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H6;
      eapply lift2_invert_exec in H8; cleanup.
      apply map_ext_eq in H4; cleanup.
      2: intros; cleanup; intuition congruence.
      do 2 eexists; intuition eauto.

      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.

      eapply Inode.get_owner_finished in H12; eauto.
      2: rewrite H17; eauto.
      eapply Inode.get_owner_finished in H10; eauto.
      2: rewrite H13; eauto.
      cleanup.

      clear H10 H12. (* clear ors*)
      do 2 eexists; intuition eauto;
      eexists; intuition eauto;
      eexists; intuition eauto.
      all:eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
      intros; FileInnerSpecs.solve_bounds.
    }
    {
      simpl.
      unfold refines_related, FD_related_states in *; simpl in *; cleanup.

      eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
      eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.

      eapply lift2_invert_exec in H29;
      eapply lift2_invert_exec in H31; cleanup.

      eapply FileInnerSpecs.read_inner_finished in H34; eauto.
      eapply FileInnerSpecs.read_inner_finished in H36; eauto.
      cleanup.

      unfold HC_refines in *; cleanup; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; logic_clean.
      
      clear H48 H52.
      repeat split; intros.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H37; eauto.

      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H38; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s2'0)))))
             (l2:= (rev (map snd (fst (snd s2'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s2'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H47.
      apply PeanoNat.Nat.add_le_mono; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s1'0)))))
             (l2:= (rev (map snd (fst (snd s1'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s1'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H51.
      apply PeanoNat.Nat.add_le_mono; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.






Lemma ATCD_TS_DiskAllocator_read:
    forall n a1 a2 u u',
    (a1 < File.DiskAllocatorParams.num_of_blocks <-> a2 < File.DiskAllocatorParams.num_of_blocks) ->
    (File.DiskAllocatorParams.bitmap_addr + S a1 <
    data_length <->
    File.DiskAllocatorParams.bitmap_addr + S a2 <
    data_length) ->
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATCD_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a1)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a2)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATCD_Refinement
     AD_valid_state)
  (fun s1 s2 => refines_related ATCD_Refinement
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a) s1 s2 /\
  (forall a, 
     Transaction.get_first (fst (snd s1)) a = None <-> 
     Transaction.get_first (fst (snd s2)) a = None) /\
  (Transaction.get_first (fst (snd s1)) (File.DiskAllocatorParams.bitmap_addr + S a1) = None <-> 
   Transaction.get_first (fst (snd s2)) (File.DiskAllocatorParams.bitmap_addr + S a2) = None) /\
   nth_error
            (value_to_bits
               (upd_batch (snd (snd s1)) (rev (map fst (fst (snd s1))))
               (rev (map snd (fst (snd s1)))) File.DiskAllocatorParams.bitmap_addr)) a1 =
               nth_error
            (value_to_bits
               (upd_batch (snd (snd s2)) (rev (map fst (fst (snd s2))))
               (rev (map snd (fst (snd s2)))) File.DiskAllocatorParams.bitmap_addr)) a2)
  (ATCD_reboot_list n).
  Proof.
    unfold File.DiskAllocator.read; intros.
    destruct (Compare_dec.lt_dec a1 File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec a2 File.DiskAllocatorParams.num_of_blocks);
    try lia.
    2: intros; apply ATCD_TS_ret.
    simpl.
    eapply ATCD_TS_compositional.

    intros; eapply TS_eqv_impl.
    eapply ATCD_TS_Transaction_read.
    shelve.
    intros; cleanup; eauto.
    2: intros; shelve.
    intros.
    eapply lift2_invert_exec in H1; cleanup.
    eapply lift2_invert_exec in H2; cleanup.
    unfold refines_related in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *.
    eapply Transaction.read_finished in H8; eauto.
    eapply Transaction.read_finished in H9; eauto.
    cleanup; repeat split_ors; cleanup; try lia.
    unfold Transaction.transaction_rep in *; cleanup.
    setoid_rewrite H6.
    destruct_fresh (nth_error
    (value_to_bits
       (upd_batch (snd (snd s2)) (rev (map fst (fst (snd s2))))
          (rev (map snd (fst (snd s2))))
          File.DiskAllocatorParams.bitmap_addr)) a2); setoid_rewrite D.
    2: intros; apply ATCD_TS_ret.
    {
      destruct b.
      2: intros; apply ATCD_TS_ret.
      eapply ATCD_TS_compositional.
      2: intros; apply ATCD_TS_ret.
      intros; simpl; eapply ATCD_TS_Transaction_read; eauto.
      intros; shelve.
    }
    {
      edestruct (block_allocator_empty a1);
      edestruct (block_allocator_empty a2);
      cleanup; apply ATCD_TS_ret.
    }
    Unshelve.
    all: try solve [ exact (fun _ _ => True)].
    all: simpl; eauto.
    all: intuition.
    unfold File.DiskAllocatorParams.bitmap_addr.
    {
      eapply lift2_invert_exec in H1; cleanup.
      eapply lift2_invert_exec in H2; cleanup.
      unfold refines_related in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *.
      eapply Transaction.read_finished in H5; eauto.
      eapply Transaction.read_finished in H12; eauto.
      cleanup; intuition.
    }
    {
      eapply lift2_invert_exec in H1; cleanup.
      eapply lift2_invert_exec in H2; cleanup.
      unfold refines_related in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *.
      eapply Transaction.read_finished in H5; eauto.
      eapply Transaction.read_finished in H12; eauto.
      cleanup; intuition.
    }
  Qed.

  Lemma ATCD_TS_explicit_inode_map:
  forall n u u' inum off, 
  (forall im1 im2,
  Termination_Sensitive u
  (Simulation.Definitions.compile ATCD_Refinement 
  (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Simulation.Definitions.compile ATCD_Refinement
  (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
    (Simulation.Definitions.compile ATCD_Refinement File.recover)
    (refines_valid ATCD_Refinement
     AD_valid_state)
     (refines_related ATCD_Refinement 
     (fun s1 s2  => exists s1a s2a, 
    (Inode.inode_rep im1 (fst (snd (snd s1))) /\
        (exists file_block_map : disk value,
            File.DiskAllocator.block_allocator_rep file_block_map
              (fst (snd (snd s1))) /\
            File.file_map_rep s1a im1 file_block_map)) /\
      (Inode.inode_rep im2 (fst (snd (snd s2))) /\
        (exists file_block_map : disk value,
            File.DiskAllocator.block_allocator_rep file_block_map
              (fst (snd (snd s2))) /\
            File.file_map_rep s2a im2 file_block_map)) /\
    FD_related_states u' None s1a s2a /\
    fst (snd s1) = Empty /\
    fst (snd s2) = Empty))
    (ATCD_reboot_list n)) ->


    Termination_Sensitive u
(Simulation.Definitions.compile ATCD_Refinement 
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
(Simulation.Definitions.compile ATCD_Refinement
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Simulation.Definitions.compile ATCD_Refinement File.recover)
(refines_valid ATCD_Refinement
     AD_valid_state)
(refines_related ATCD_Refinement
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a /\
fst (snd s1) = Empty /\
  fst (snd s2) = Empty))
  (ATCD_reboot_list n) .
Proof.
unfold Termination_Sensitive; intros.
unfold refines_related, File.files_inner_rep in *.
cleanup.
eapply H.
3: eauto.
all: eauto.
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
Qed.

Lemma ATCD_TS_read_inner:
    forall n inum off u u',
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATCD_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.read_inner off inum)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.read_inner off inum)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATCD_Refinement
     AD_valid_state)
  (refines_related ATCD_Refinement
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a /\
  fst (snd s1) = Empty /\ fst (snd s2) = Empty))
  (ATCD_reboot_list n).
  Proof.
    Transparent File.read_inner.
    intros; 
    eapply ATCD_TS_explicit_inode_map.
    intros; unfold File.read_inner.
    eapply ATCD_TS_compositional.
    intros; eapply TS_eqv_impl.
    eapply ATCD_TS_get_block_number.
    simpl; intros; shelve.
    2: intros; shelve.

    intros; unfold refines_related in *; cleanup.
      eapply_fresh get_block_number_oracle_refines_exists in H; eauto.
      eapply_fresh get_block_number_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H12; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H14;
      eapply lift2_invert_exec in H16; cleanup.
      apply map_ext_eq in H12; cleanup.
      2: intros; cleanup; intuition congruence.

      unfold File.files_inner_rep in *; cleanup.
      eapply_fresh Inode.get_block_number_finished_oracle_eq in H20; eauto; subst.
      cleanup; destruct r1, r2; try solve [intuition congruence].
      2: intros; apply ATCD_TS_ret.
      
      eapply ATCD_TS_compositional.
      2: intros; destruct r1, r2; apply ATCD_TS_ret.
      2: intros; shelve.
      simpl; intros; repeat invert_exec; try congruence.
      eapply TS_eqv_impl. 
      eapply ATCD_TS_DiskAllocator_read.
      {
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.
        cleanup; repeat split_ors; cleanup; intuition eauto.
        eapply SameRetType.all_block_numbers_in_bound in H29.
        3: eauto.
        all: eauto.
        eapply Forall_forall in H29; eauto.
        apply in_seln; eauto.

        eapply SameRetType.all_block_numbers_in_bound in H10.
        3: eauto.
        all: eauto.
        eapply Forall_forall in H10; eauto.
        apply in_seln; eauto.
      }
      {
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.

        cleanup; repeat split_ors; cleanup; intuition eauto.
      eapply data_block_inbounds; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      eapply data_block_inbounds.
      4: eauto.
      all: eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
      }
      {
        instantiate (2:= refines_related ATCD_Refinement
        (fun s1 s2  => 
        exists s1a s2a, 
        (Inode.inode_rep im1 (fst (snd (snd s1))) /\
            (exists file_block_map,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s1))) /\
                File.file_map_rep s1a im1 file_block_map)) /\
          (Inode.inode_rep im2 (fst (snd (snd s2))) /\
            (exists file_block_map,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s2))) /\
                File.file_map_rep s2a im2 file_block_map)) /\
        FD_related_states u' None s1a s2a /\
        fst (snd s1) = Empty /\
        fst (snd s2) = Empty)).
         
         simpl; intros.
         unfold refines_related in *.
         cleanup.
         split.
         unfold File.files_inner_rep.
         do 2 eexists; intuition eauto.
         do 2 eexists; intuition eauto.

         simpl in *; unfold HC_refines in H12, H21; cleanup.
         simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
         Transaction.transaction_rep  in *; cleanup; 
         repeat split_ors; cleanup; try congruence.
        eapply txn_length_0_empty in H34;
        eapply txn_length_0_empty in H38; subst.
        setoid_rewrite H34;
        setoid_rewrite H38.
        simpl; intuition eauto.

        rewrite H38, H34 in *; simpl in *.
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.
        cleanup; repeat split_ors; cleanup; intuition eauto.
        repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto.
      }
      shelve.
      {
        unfold File.files_inner_rep in *; cleanup. 
        do 2 eexists; intuition eauto.
      }

    Unshelve.
    all: eauto.
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      simpl in *.
      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      do 2 eexists; intuition eauto. 

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H14;
      setoid_rewrite H14.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H18;
      setoid_rewrite H18.
      simpl; eauto.
    }
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_block_number_oracle_refines_exists in H; eauto.
      eapply_fresh get_block_number_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H12; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H14;
      eapply lift2_invert_exec in H16; cleanup.
      apply map_ext_eq in H12; cleanup.
      2: intros; cleanup; intuition congruence.
      unfold File.files_inner_rep in *; cleanup.
      eapply Inode.get_block_number_finished in H20; eauto.
      eapply Inode.get_block_number_finished in H18; eauto.
      cleanup.
      clear H12 H20.
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
      
      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      setoid_rewrite H26; eauto.
      setoid_rewrite H22; eauto.

      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
    }
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.
    {
      intros.
      match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold FD_related_states,
       same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold File.file_map_rep in *; cleanup.
       match goal with
       | [H: ?x1 ?inum = Some _,
          H0: ?x2 ?inum = Some _,
          H1: forall (_: Inode.Inum) _ _, 
          ?x1 _ = Some _ ->
          _ _ = Some _ -> _,
          H2: forall (_: Inode.Inum) _ _, 
          ?x2 _ = Some _ ->
          _ _ = Some _ -> _ |- _] =>
          eapply H1 in H; eauto; cleanup;
          eapply H2 in H0; eauto; cleanup
       end.
       unfold File.file_rep in *; cleanup; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.
    Opaque File.read_inner.

    Lemma ATCD_TS_read:
    forall n inum off u u',
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Read inum off |)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Read inum off |)))
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATCD_Refinement
     AD_valid_state)
  (refines_related ATCD_Refinement
     (AD_related_states u' None))
  (ATCD_reboot_list n).
  Proof.
    intros; simpl.
    eapply ATCD_TS_compositional.
    {
      intros; eapply TS_eqv_impl.
      eapply ATCD_TS_get_owner.
      unfold refines_related, AD_related_states; 
      simpl. unfold refines_related; simpl.
      unfold refines, File.files_rep; simpl. 
      intros; cleanup; intuition eauto.
      do 2 eexists; intuition eauto.
      rewrite H4, H6;
      do 2 eexists; intuition eauto.
      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H12;
      setoid_rewrite H12.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H16;
      setoid_rewrite H16.
      simpl; eauto.
    }
    {
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_owner_oracle_refines_exists in H; eauto.
      eapply_fresh get_owner_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H6;
      eapply lift2_invert_exec in H8; cleanup.
      apply map_ext_eq in H4; cleanup.
      2: intros; cleanup; intuition congruence.

      eapply_fresh get_owner_related_ret_eq in H10; eauto; subst.
      destruct r2.
      2: intros; apply ATCD_TS_abort_then_ret.
      
      eapply ATCD_TS_compositional.
      intros; apply ATCD_TS_auth.
      2: shelve.
      simpl; intros; repeat invert_exec; try congruence.
      2: intros; apply ATCD_TS_abort_then_ret.
      eapply ATCD_TS_compositional.
      intros; eapply ATCD_TS_read_inner.
      intros.
      {
        instantiate (1:= refines_related ATCD_Refinement
        (fun s3 s4 : state AD =>
         exists s1a s2a : disk File,
           File.files_inner_rep s1a (fst (snd (snd s3))) /\
           File.files_inner_rep s2a (fst (snd (snd s4))) /\
           FD_related_states u' None s1a s2a /\
           fst (snd s3) = Empty /\ fst (snd s4) = Empty)) in H13; simpl in *; cleanup.
        unfold refines_related, FD_related_states in *; simpl in *; cleanup.

      eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
      eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.

      eapply lift2_invert_exec in H22;
      eapply lift2_invert_exec in H24; cleanup.
      
      eapply ATCD_oracle_refines_impl_eq in H21.
      2: apply H20.
      all: simpl in *; eauto.
      2: apply TD_oracle_refines_operation_eq.
      apply map_ext_eq in H21; cleanup.
      2: intros; cleanup; intuition congruence.
      eapply SameRetType.read_inner_finished_oracle_eq in H27.
      2: apply H29.
      all: eauto.
      cleanup.
      destruct r1, r2; try solve [intuition congruence].
      intros; apply ATCD_TS_commit_then_ret.
      intros; apply ATCD_TS_abort_then_ret.
      eapply have_same_structure_read_inner; eauto.
      do 2 eexists; intuition eauto.
      unfold FD_related_states; 
      apply TSCommon.same_for_user_except_symmetry; eauto.
      apply not_init_read_inner.
      apply not_init_read_inner.
      }
      intros; shelve.
    }
    intros; shelve.
    Unshelve.
    all: try exact u'.
    all: eauto.
    all: try solve [exact (fun _ _ => True)].
    all: try solve [simpl; eauto].
    {
      simpl; intros;
      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      repeat invert_exec; destruct s0, s3; simpl in *; eauto;
        do 2 eexists; intuition eauto;
        do 2 eexists; intuition eauto.
    }
    2:{
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_owner_oracle_refines_exists in H; eauto.
      eapply_fresh get_owner_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATCD_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATCD_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H6;
      eapply lift2_invert_exec in H8; cleanup.
      apply map_ext_eq in H4; cleanup.
      2: intros; cleanup; intuition congruence.
      do 2 eexists; intuition eauto.

      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.

      eapply Inode.get_owner_finished in H12; eauto.
      2: rewrite H17; eauto.
      eapply Inode.get_owner_finished in H10; eauto.
      2: rewrite H13; eauto.
      cleanup.

      clear H10 H12. (* clear ors*)
      do 2 eexists; intuition eauto;
      eexists; intuition eauto;
      eexists; intuition eauto.
      all:eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
      intros; FileInnerSpecs.solve_bounds.
    }
    {
      simpl.
      unfold refines_related, FD_related_states in *; simpl in *; cleanup.

      eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
      eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATCD_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.

      eapply lift2_invert_exec in H29;
      eapply lift2_invert_exec in H31; cleanup.

      eapply FileInnerSpecs.read_inner_finished in H34; eauto.
      eapply FileInnerSpecs.read_inner_finished in H36; eauto.
      cleanup.

      unfold HC_refines in *; cleanup; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; logic_clean.
      
      clear H48 H52.
      repeat split; intros.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H37; eauto.

      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H38; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s2'0)))))
             (l2:= (rev (map snd (fst (snd s2'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s2'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H47.
      apply PeanoNat.Nat.add_le_mono; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s1'0)))))
             (l2:= (rev (map snd (fst (snd s1'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s1'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H51.
      apply PeanoNat.Nat.add_le_mono; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.


      