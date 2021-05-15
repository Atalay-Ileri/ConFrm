Require Import Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import TransactionalDiskRefinement FileDisk.TransferProofs FileDiskNoninterference ATCLayer.

(* Notation "'TransactionalDiskCore'" := (TransactionalDiskOperation data_length). *)

Fixpoint horizontally_compose_valid_prog1 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) {T} (p1: prog L1 T) :=
         match p1 with
         | @Op _ T' p => Op (HorizontalComposition O1 O2) (P1 p)
         | @Ret _ T' t => Ret t
         | @Bind _ T1 T2 p1 p2 =>
           Bind (horizontally_compose_valid_prog1 L1 L2 LL p1)
           (fun r => horizontally_compose_valid_prog1 L1 L2 LL (p2 r))
         end.


Fixpoint horizontally_compose_valid_prog2 {O1 O2} (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2)) {T} (p2: prog L2 T) :=
         match p2 with
         | @Op _ T' p => (Op (HorizontalComposition O1 O2) (P2 p))
         | @Ret _ T' t => (Ret t)
         | @Bind _ T1 T2 p1 p2 =>
         Bind (horizontally_compose_valid_prog2 L1 L2 LL p1)
         (fun r => horizontally_compose_valid_prog2 L1 L2 LL (p2 r))
       end.


Lemma ss_hc_rev_p1:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    u R C V T l_grs1 l_grs2 (p1 p2: L1.(prog) T) rec,
    @SelfSimulation _ LL u _ (horizontally_compose_valid_prog1 L1 L2 LL p1)
    (horizontally_compose_valid_prog1 L1 L2 LL p2)
    (horizontally_compose_valid_prog1 L1 L2 LL rec) R V  C l_grs2 ->
    forall s2,
      SelfSimulation u p1 p2 rec
        (fun s1 => R (s1, s2))
        (fun s1 s1' =>  V (s1, s2) (s1', s2))
        C
        l_grs1.
Proof. Admitted.


Lemma ss_hc_rev_p2:
  forall O1 O2 (L1: Language O1) (L2: Language O2) (LL: Language (HorizontalComposition O1 O2))
    u R C V T l_grs1 l_grs2 (p1 p2: L2.(prog) T) rec,
    @SelfSimulation _ LL u _ (horizontally_compose_valid_prog2 L1 L2 LL p1)
    (horizontally_compose_valid_prog2 L1 L2 LL p2)
    (horizontally_compose_valid_prog2 L1 L2 LL rec) R V  C l_grs2 ->
    forall s1,
      SelfSimulation u p1 p2 rec
        (fun s2 => R (s1, s2))
        (fun s2 s2' =>  V (s1, s2) (s1, s2'))
        C
        l_grs1.
Proof. Admitted.


(*
Theorem ss_TD_read:
  forall n a u u' s,
    @SelfSimulation _ TransactionalDisk u _
    (TransactionalDiskCore.(Op) (Read a))
    (TransactionalDiskCore.(Op) (Read a)) 
    (TransactionalDiskCore.(Op) Recover) (TD_valid_state s) 
    (TD_related_states u' None s) (eq u') (transactional_disk_reboot_list n).
Proof.
    intros.
    eapply ss_hc_rev_p2 with (R:= AD_valid_state) (V:= AD_related_states u' None).
    simpl; 
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
*)

Import FileDiskLayer.

Theorem ss_ATC_read:
  forall n inum off u u',
    SelfSimulation u 
    (compile (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (compile (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (compile (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover))) 
    ATC_valid_state 
    (ATC_related_states u' None) (eq u') (ATC_reboot_list n).
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