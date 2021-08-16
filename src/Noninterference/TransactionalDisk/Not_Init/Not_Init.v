Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer ATCSimulation ATCAOE.

Import FileDiskLayer.

Lemma not_init_InodeAllocator_read:
forall inum,
not_init (@lift_L2 AuthenticationOperation _ TD _(Inode.InodeAllocator.read inum)).
Proof.
  unfold Inode.InodeAllocator.read; simpl; intros.
  destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
  simpl; intuition eauto.
  inversion H.
  destruct (nth_error (value_to_bits t) inum); simpl; intuition eauto.
  destruct b; simpl; intuition eauto.
  inversion H.
  simpl; eauto.
Qed.

Lemma not_init_DiskAllocator_read:
forall bn,
not_init (@lift_L2 AuthenticationOperation _ TD _(File.DiskAllocator.read bn)).
Proof.
  unfold File.DiskAllocator.read; simpl; intros.
  destruct (Compare_dec.lt_dec bn File.DiskAllocatorParams.num_of_blocks).
  simpl; intuition eauto.
  inversion H.
  destruct (nth_error (value_to_bits t) bn); simpl; intuition eauto.
  destruct b; simpl; intuition eauto.
  inversion H.
  simpl; eauto.
Qed.

Lemma not_init_get_inode:
forall inum,
not_init (@lift_L2 AuthenticationOperation _ TD _(Inode.get_inode inum)).
Proof.
  Transparent Inode.get_inode.
  unfold Inode.get_inode; simpl; intros.
  simpl; intuition eauto.
  apply not_init_InodeAllocator_read.
  destruct t; simpl; eauto.
  Opaque Inode.get_inode.
Qed.


Lemma not_init_get_owner:
forall inum,
not_init (@lift_L2 AuthenticationOperation _ TD _(Inode.get_owner inum)).
Proof.
  Transparent Inode.get_owner.
  simpl; intros; intuition eauto.
  apply not_init_get_inode.
  destruct t; simpl; eauto.
Qed.

Lemma not_init_get_block_number:
forall inum off,
not_init (@lift_L2 AuthenticationOperation _ TD _(Inode.get_block_number inum off)).
Proof.
  Transparent Inode.get_block_number.
  simpl; intros; intuition eauto.
  apply not_init_get_inode.
  destruct t; simpl; eauto.
Qed.

Lemma not_init_read_inner:
forall inum off,
not_init (@lift_L2 AuthenticationOperation _ TD _(File.read_inner off inum)).
Proof.
  Opaque Inode.get_block_number.
  simpl; intros; intuition eauto.
  apply not_init_get_block_number.
  destruct t; simpl; intuition eauto.
  apply not_init_DiskAllocator_read.
  destruct t; simpl; intuition eauto.
Qed.


Lemma not_init_read:
forall inum off,
not_init (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off))).
Proof.
  Opaque Inode.get_owner File.read_inner.
  simpl; intros; intuition eauto.
  apply not_init_get_owner.
  destruct t; simpl; intuition eauto.
  destruct t; simpl; intuition eauto.
  destruct u0; simpl; intuition eauto.
  apply not_init_read_inner.
  destruct t; simpl; intuition eauto.
  all: inversion H.
Qed.
