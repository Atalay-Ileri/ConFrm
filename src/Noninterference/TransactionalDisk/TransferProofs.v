Require Import Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer TransferProofs ATCSimulation.

(* Notation "'TransactionalDiskCore'" := (TransactionalDiskOperation data_length). *)

Import FileDiskLayer.

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
not_init (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))).
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
        destruct u1; simpl; intuition eauto.
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
    - simpl. eapply ATC_simulation.
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
        destruct u1; simpl; intuition eauto.
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
      - simpl. eapply ATC_simulation.
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
        destruct u1; simpl; intuition eauto.
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
    - simpl. (* Use Lemmas *) admit.
    - (* Use Lemmas *) admit.
    - (* Use Lemmas *)admit.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - (* Use Lemmas *) admit.
Abort.