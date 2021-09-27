Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATC_Simulation ATC_AOE.
Require Import Not_Init HSS ATC_ORS ATC_TS_Common ATC_TS_TC ATC_TS_Allocator.

Import FileDiskLayer.
Set Nested Proofs Allowed.


Lemma ATC_TS_get_inode:
forall n inum u u',
Termination_Sensitive u
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_inode inum)))
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_inode inum)))
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state)
(fun s1 s2 => refines_related ATC_Refinement
 (fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 /\
(forall a, 
 Transaction.get_first (fst (snd s1)) a = None <-> 
 Transaction.get_first (fst (snd s2)) a = None))
(ATC_reboot_list n).
Proof.
Transparent Inode.get_inode.
simpl; intros.
eapply ATC_TS_compositional.
intros; apply ATC_TS_InodeAllocator_read.
intros; destruct r1, r2; apply ATC_TS_ret.
intros; instantiate (1:= fun _ _ => True); simpl; eauto.
Opaque Inode.get_inode.
Qed.

Lemma ATC_TS_get_owner:
forall n inum u u',
Termination_Sensitive u
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_owner inum)))
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_owner inum)))
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state)
(fun s1 s2 => refines_related ATC_Refinement
 (fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 /\
(forall a, 
 Transaction.get_first (fst (snd s1)) a = None <-> 
 Transaction.get_first (fst (snd s2)) a = None))
(ATC_reboot_list n).
Proof.
Transparent Inode.get_owner.
simpl; intros.
eapply ATC_TS_compositional.
intros; apply ATC_TS_get_inode.
intros; destruct r1, r2; apply ATC_TS_ret.
intros; instantiate (1:= fun _ _ => True); simpl; eauto.
Opaque Inode.get_owner.
Qed.

Lemma ATC_TS_get_block_number:
forall n inum u u' off,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_block_number inum off)))
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_block_number inum off)))
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state)
(fun s1 s2 => refines_related ATC_Refinement
 (fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a) s1 s2 /\
(forall a, 
 Transaction.get_first (fst (snd s1)) a = None <-> 
 Transaction.get_first (fst (snd s2)) a = None))
(ATC_reboot_list n).
Proof.
Transparent Inode.get_block_number.
simpl; intros.
eapply ATC_TS_compositional.
intros; apply ATC_TS_get_inode.
intros; destruct r1, r2; apply ATC_TS_ret.
intros; instantiate (1:= fun _ _ => True); simpl; eauto.
Opaque Inode.get_block_number.
Qed.