Require Import Framework Lia.

Axiom block_size: nat.

Definition super_block_num := 0.
Definition hdr_block_num := 1.
Definition log_start := 2.
Axiom log_length : nat.

Lemma hdr_block_num_eq:
  hdr_block_num = 1.
Proof. eauto. Qed.

Lemma log_start_eq:
  log_start = 2.
Proof. eauto. Qed.

Lemma hdr_before_log:
  hdr_block_num < log_start.
Proof. eauto. Qed.
       
Definition data_start := 2 + log_length.
Definition data_length := disk_size - data_start.

Lemma data_start_where_log_ends:
  data_start = log_start + log_length.
Proof. eauto. Qed.

Axiom data_fits_in_disk:
  disk_size = data_start + data_length.

(* Below all reside in data region indexed accordingly *)
(* For simplicity, it will be 1 inode per block *)
Definition inode_blocks_start := 0.
Axiom inode_count: nat.
Axiom inode_count_in_bounds: inode_count <= block_size.

Definition file_blocks_start:= S(inode_count). (* 1 bitmap + inode_count inodes *)
Axiom file_blocks_count : nat.
Axiom file_blocks_count_in_bounds: file_blocks_count <= block_size.

Axiom all_fits_to_data_region : 2 + inode_count + file_blocks_count <= data_length.

Theorem inodes_fit_in_disk:
  inode_blocks_start + inode_count < data_length.
Proof.
  pose proof all_fits_to_data_region.
  unfold inode_blocks_start.
  lia.
Qed.

Theorem file_blocks_fit_in_disk:
  file_blocks_start + file_blocks_count < data_length.
Proof.
  pose proof all_fits_to_data_region.
  unfold file_blocks_start.
  lia.
Qed.

Global Opaque super_block_num hdr_block_num log_start data_start data_length inode_blocks_start file_blocks_start.
