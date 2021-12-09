Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS ATCD_TS_Common ATCD_TS_Allocator ATCD_TS_Recovery.

Import FileDiskLayer.
Set Nested Proofs Allowed.

Opaque File.recover.
Lemma ATCD_TS_InodeAllocator_read:
forall n inum u u' txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 (@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum))))
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 (@lift_L2 AuthenticationOperation _ TD _
    (Inode.InodeAllocator.read inum))))
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
 refines_related ATCD_Refinement 
 (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
     File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
     File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
     FD_related_states u' None s1a s2a) s1 s2 /\
 (forall a, 
  Transaction.get_first (fst (snd s1)) a = None <-> 
  Transaction.get_first (fst (snd s2)) a = None)) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall a, 
  fst (snd (snd s1)) a = None <->
  fst (snd (snd s2)) a = None) /\
  fst (snd (snd s1)) =
  Mem.list_upd_batch empty_mem (map Log.addr_list txns1)
    (map Log.data_blocks txns1) /\
  fst (snd (snd s2)) =
  Mem.list_upd_batch empty_mem (map Log.addr_list txns2)
    (map Log.data_blocks txns2))
(ATCD_reboot_list n).
Proof.
Transparent Inode.InodeAllocator.read.
unfold Inode.InodeAllocator.read; simpl; intros.
destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
2:{
    simpl.
    eapply TS_eqv_impl.
    apply ATCD_TS_ret.
    simpl; intuition eauto.
}

simpl.
Admitted.






Lemma ATCD_TS_get_inode:
forall n inum u u' txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 (@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_inode inum))))
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 (@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_inode inum))))
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
 refines_related ATCD_Refinement 
 (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
     File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
     File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
     FD_related_states u' None s1a s2a) s1 s2 /\
 (forall a, 
  Transaction.get_first (fst (snd s1)) a = None <-> 
  Transaction.get_first (fst (snd s2)) a = None)) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall a, 
  fst (snd (snd s1)) a = None <->
  fst (snd (snd s2)) a = None) /\
  fst (snd (snd s1)) =
  Mem.list_upd_batch empty_mem (map Log.addr_list txns1)
    (map Log.data_blocks txns1) /\
  fst (snd (snd s2)) =
  Mem.list_upd_batch empty_mem (map Log.addr_list txns2)
    (map Log.data_blocks txns2))
(ATCD_reboot_list n).
Proof.
Transparent Inode.get_inode.
simpl; intros.
eapply ATCD_TS_compositional.
intros; apply ATCD_TS_InodeAllocator_read.
intros; destruct r1, r2; eapply TS_eqv_impl;
try apply ATCD_TS_ret.
instantiate (5:= fun _ _ => _); simpl; eauto.
all: simpl; eauto.
intros; intuition eauto.
Opaque Inode.get_inode.
Admitted.

Lemma ATCD_TS_get_owner:
forall n inum u u' txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_owner inum))))
    (Simulation.Definitions.compile
 ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_owner inum))))
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
 refines_related ATCD_Refinement 
 (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
     File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
     File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
     FD_related_states u' None s1a s2a) s1 s2 /\
 (forall a, 
  Transaction.get_first (fst (snd s1)) a = None <-> 
  Transaction.get_first (fst (snd s2)) a = None)) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall a, 
  fst (snd (snd s1)) a = None <->
  fst (snd (snd s2)) a = None))
(ATCD_reboot_list n).
Proof.
Transparent Inode.get_owner.
simpl; intros.
eapply ATCD_TS_compositional.
intros; eapply TS_eqv_impl.
apply ATCD_TS_get_inode.
shelve.
intros; destruct r1, r2; 
intros; eapply TS_eqv_impl;
try apply ATCD_TS_ret.
instantiate (5:= fun _ _ => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2); simpl; eauto.
all: simpl; eauto.
intuition eauto.
Opaque Inode.get_owner.
Admitted.

Lemma ATCD_TS_get_block_number:
forall n inum u u' off txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_block_number inum off))))
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _
    (Inode.get_block_number inum off))))
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
 refines_related ATCD_Refinement 
 (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
     File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
     File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
     FD_related_states u' None s1a s2a) s1 s2 /\
 (forall a, 
  Transaction.get_first (fst (snd s1)) a = None <-> 
  Transaction.get_first (fst (snd s2)) a = None)) s1 s2 /\
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
  (forall a, 
  fst (snd (snd s1)) a = None <->
  fst (snd (snd s2)) a = None))
(ATCD_reboot_list n).
Proof.
Transparent Inode.get_block_number.
simpl; intros.
eapply ATCD_TS_compositional.
intros; eapply TS_eqv_impl; try apply ATCD_TS_get_inode.
shelve.
intros; destruct r1, r2; 
eapply TS_eqv_impl; try apply ATCD_TS_ret.
instantiate (5:= fun _ _ => _); simpl; eauto.
all: simpl; eauto.
shelve.
Opaque Inode.get_block_number.
Admitted.