Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer ATC_Simulation ATC_AOE.

Import FileDiskLayer.

Ltac not_init_solve:= 
  match goal with
  | [H: eq_dep _ _ _ _ _ _ |- _] =>
  inversion H
  | [|- context [match ?x with | _ => _ end] ] =>
  destruct x; simpl; intuition eauto
  | [|- not_init _] =>
  unfold 
  Inode.set_inode,
  File.DiskAllocator.read, 
  Inode.InodeAllocator.read,
  File.DiskAllocator.write,
  Inode.InodeAllocator.write; simpl; intuition eauto
  end.

(*  
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

Lemma not_init_DiskAllocator_write:
forall bn v,
not_init (@lift_L2 AuthenticationOperation _ TD _(File.DiskAllocator.write bn v)).
Proof.
  unfold File.DiskAllocator.write; simpl; intros.
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
*)

Transparent Inode.get_owner Inode.get_block_number Inode.extend Inode.set_inode.
Lemma not_init_read:
forall inum off,
not_init (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off))).
Proof.
  intros; repeat not_init_solve.
Qed.


Lemma not_init_write:
forall inum off v,
not_init (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v))).
Proof.
  intros; repeat not_init_solve.
Qed.

Lemma not_init_extend:
forall inum v,
not_init (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v))).
Proof.
  intros; repeat not_init_solve.
Qed.
