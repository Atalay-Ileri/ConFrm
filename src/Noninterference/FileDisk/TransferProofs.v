Require Import Framework FileDiskLayer FileDiskRefinement FileDisk.RefinesSameOracle.RefinesSame FileDiskNoninterference FileDiskSSE.

Theorem ss_AD_read:
  forall n inum off u u',
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_read.
    - apply read_simulation.
    - apply read_simulation.
    - apply abstract_oracles_exist_wrt_read.
    - apply abstract_oracles_exist_wrt_read.
    - apply ORS_read.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related; apply SelfSimulation_Exists_read.
Qed.

Theorem ss_AD_write:
  forall n inum off u u' v,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Write inum off v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Write inum off v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_write.
    - apply write_simulation.
    - apply write_simulation.
    - apply abstract_oracles_exist_wrt_write.
    - apply abstract_oracles_exist_wrt_write.
    - apply ORS_write.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related; apply SelfSimulation_Exists_write.
Qed.

Theorem ss_AD_extend:
  forall n inum u u' v,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Extend inum v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Extend inum v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_extend.
    - apply extend_simulation.
    - apply extend_simulation.
    - apply abstract_oracles_exist_wrt_extend.
    - apply abstract_oracles_exist_wrt_extend.
    - apply ORS_extend.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related; apply SelfSimulation_Exists_extend.
Qed.

Theorem ss_AD_change_owner:
  forall n inum u u' v,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (ChangeOwner inum v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (ChangeOwner inum v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_change_owner.
    - apply change_owner_simulation.
    - apply change_owner_simulation.
    - apply abstract_oracles_exist_wrt_change_owner.
    - apply abstract_oracles_exist_wrt_change_owner.
    - apply ORS_change_owner.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related;
    apply SelfSimulation_Exists_change_owner.
Qed.

Theorem ss_AD_create:
  forall n u u' v,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Create v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Create v))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_create.
    - apply create_simulation.
    - apply create_simulation.
    - apply abstract_oracles_exist_wrt_create.
    - apply abstract_oracles_exist_wrt_create.
    - apply ORS_create.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related;
    apply SelfSimulation_Exists_create.
Qed.


Theorem ss_AD_delete:
  forall n inum u u',
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Delete inum))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Delete inum))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_delete.
    - apply delete_simulation.
    - apply delete_simulation.
    - apply abstract_oracles_exist_wrt_delete.
    - apply abstract_oracles_exist_wrt_delete.
    - apply ORS_delete.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related;
    apply SelfSimulation_Exists_delete.
Qed.

Theorem ss_AD_write_input:
  forall n inum off u u' v1 v2,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Write inum off v1))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Write inum off v2))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_write_input.
    - apply write_simulation.
    - apply write_simulation.
    - apply abstract_oracles_exist_wrt_write.
    - apply abstract_oracles_exist_wrt_write.
    - apply ORS_write_input.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related; apply SelfSimulation_Exists_write_input.
Qed.

Theorem ss_AD_extend_input:
  forall n inum u u' v1 v2,
    SelfSimulation u 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Extend inum v1))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Extend inum v2))) 
    (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply SS_transfer.
    - apply ss_FD_extend_input.
    - apply extend_simulation.
    - apply extend_simulation.
    - apply abstract_oracles_exist_wrt_extend.
    - apply abstract_oracles_exist_wrt_extend.
    - apply ORS_extend.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold refines_related; apply SelfSimulation_Exists_extend_input.
Qed.