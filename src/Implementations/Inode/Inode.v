Require Import Transaction. (* Needed for extraction *)
Require Import Framework FSParameters TransactionalDiskLayer BlockAllocator.
Import IfNotations.

Definition Inum := addr.

Record Inode :=
  {
    owner: user;
    block_numbers : list addr;
  }.

Variable encode_inode : Inode -> value.
Variable decode_inode: value -> Inode.
Axiom inode_encode_decode:
  forall i,
    decode_inode (encode_inode i) = i.
Axiom inode_decode_encode:
  forall b,
    encode_inode (decode_inode b) = b.

Module InodeAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := inode_blocks_start.
  Definition num_of_blocks := inode_count.
  Definition num_of_blocks_in_bounds := inode_count_in_bounds.
End InodeAllocatorParams.

Module InodeAllocator := BlockAllocator InodeAllocatorParams.

Import InodeAllocator.

Open Scope pred_scope.

Definition inode_map_rep inode_block_map (inode_map: disk Inode) :=
  forall i, inode_map i = option_map decode_inode (inode_block_map i).

Definition inode_rep (inode_map: disk Inode) : @pred addr addr_dec (set value) :=
  exists* inode_block_map,
    block_allocator_rep inode_block_map *
    [[ forall i, inode_map i = option_map decode_inode (inode_block_map i) ]].

Local Definition get_inode inum :=
  r <- read inum;
  if r is Some i then
    Ret (Some (decode_inode i))
  else
    Ret None.

Local Definition set_inode inum inode:=
  r <- write inum (encode_inode inode);
  Ret r.

Definition alloc user :=
  r <- alloc (encode_inode (Build_Inode user []));
  Ret r.

Definition free inum :=
  r <- free inum;
  Ret r.

Definition extend inum block_num :=
  r <- get_inode inum;
  if r is Some inode then
    r <- set_inode inum (Build_Inode inode.(owner) (inode.(block_numbers)++[block_num]));
      Ret r
  else
    Ret None.

Definition change_owner inum user :=
  r <- get_inode inum;
  if r is Some inode then
    r <- set_inode inum (Build_Inode user inode.(block_numbers));
      Ret r
  else
    Ret None.

Definition get_block_number inum off:=
  r <- get_inode inum;
  if r is Some inode then
    Ret (nth_error inode.(block_numbers) off)
  else
    Ret None.

Definition get_block_numbers inum :=
  r <- get_inode inum;
  if r is Some inode then
    Ret (Some inode.(block_numbers))
  else
    Ret None.

Definition get_owner inum :=
  r <- get_inode inum;
  if r is Some inode then
    Ret (Some inode.(owner))
  else
    Ret None.
