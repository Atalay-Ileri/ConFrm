Require Import Framework FileDiskLayer FileDiskRefinement.
Require Import FD_ORS FileDiskNoninterference. (* FileDiskTS. *)

Theorem ss_AD_read:
  forall n inum off u u',
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_read.
    - apply read_simulation.
    - apply read_simulation.
    - apply abstract_oracles_exist_wrt_read.
    - apply abstract_oracles_exist_wrt_read.
    - apply ORS_read.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_write:
  forall n inum off u u' v,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_write.
    - apply write_simulation.
    - apply write_simulation.
    - apply abstract_oracles_exist_wrt_write.
    - apply abstract_oracles_exist_wrt_write.
    - apply ORS_write.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_extend:
  forall n inum u u' v,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_extend.
    - apply extend_simulation.
    - apply extend_simulation.
    - apply abstract_oracles_exist_wrt_extend.
    - apply abstract_oracles_exist_wrt_extend.
    - apply ORS_extend.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_change_owner:
  forall n inum u u' v,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (ChangeOwner inum v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (ChangeOwner inum v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_change_owner.
    - apply change_owner_simulation.
    - apply change_owner_simulation.
    - apply abstract_oracles_exist_wrt_change_owner.
    - apply abstract_oracles_exist_wrt_change_owner.
    - apply ORS_change_owner.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_create:
  forall n u u' v,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Create v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Create v))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_create.
    - apply create_simulation.
    - apply create_simulation.
    - apply abstract_oracles_exist_wrt_create.
    - apply abstract_oracles_exist_wrt_create.
    - apply ORS_create.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.


Theorem ss_AD_delete:
  forall n inum u u',
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Delete inum))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Delete inum))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' None) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_delete.
    - apply delete_simulation.
    - apply delete_simulation.
    - apply abstract_oracles_exist_wrt_delete.
    - apply abstract_oracles_exist_wrt_delete.
    - apply ORS_delete.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_write_input:
  forall n inum off u u' v1 v2,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v1))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v2))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_write_input.
    - apply write_simulation.
    - apply write_simulation.
    - apply abstract_oracles_exist_wrt_write.
    - apply abstract_oracles_exist_wrt_write.
    - apply ORS_write_input.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.

Theorem ss_AD_extend_input:
  forall n inum u u' v1 v2,
    RDNI_Weak u 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v1))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v2))) 
    (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover)) AD_valid_state 
    (AD_related_states u' (Some inum)) (eq u') (authenticated_disk_reboot_list n).
Proof.
    intros; eapply RDNIW_transfer.
    - apply RDNI_to_RDNIW; apply ss_FD_extend_input.
    - apply extend_simulation.
    - apply extend_simulation.
    - apply abstract_oracles_exist_wrt_extend.
    - apply abstract_oracles_exist_wrt_extend.
    - apply ORS_extend.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
    - unfold exec_compiled_preserves_validity,
    refines_valid, FD_valid_state; intros; eauto.
Qed.