Require Import Framework.

Axiom block_size: nat.
Axiom disk_size: nat.

Definition super_block_num := 0.
Definition hdr_block_num := 1.
Definition log_start := 2.
Axiom log_length : nat.

Definition data_start := 2 + log_length.
Definition data_length := disk_size - data_start.

(* Below all reside in data region *)
(* For simplicity, it will be 1 inode per block *)
Definition inode_blocks_start := data_start.
Axiom inode_count: nat.
Axiom inode_count_in_bounds: inode_count <= block_size.

Definition file_blocks_start:= S(data_start + inode_count). (* 1 bitmap + inode_count inodes *)
Axiom file_blocks_count : nat.
Axiom file_blocks_count_in_bounds: file_blocks_count <= block_size.

Axiom all_fits_to_data_region : 2 + inode_count + file_blocks_count <= data_length.

Axiom addr_list_to_blocks : list addr -> list value.

Global Opaque super_block_num hdr_block_num log_start data_start data_length inode_blocks_start file_blocks_start.
