Require Import Framework TransactionalDiskLayer BlockAllocator Inode.
Import IfNotations.

Open Scope pred_scope.

Axiom disk_start_addr: addr.
Axiom disk_block_count: nat.
Axiom disk_block_count_in_bounds: disk_block_count <= block_size.

Module DiskAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := disk_start_addr.
  Definition num_of_blocks := disk_block_count.
  Definition num_of_blocks_in_bounds := disk_block_count_in_bounds.
End DiskAllocatorParams.

Module DiskAllocator := BlockAllocator DiskAllocatorParams.

Record File :=
  {
    owner: user;
    blocks: list value;
  }.

Definition file_rep (file: File) (inode: Inode) (file_block_map: disk value) :=
  file.(owner) = inode.(Inode.Definitions.owner) /\
  length file.(blocks) = length inode.(block_numbers) /\
  (forall i block_number,
       nth_error inode.(block_numbers) i = Some block_number ->
       nth_error file.(blocks) i = file_block_map block_number).

Definition files_inner_rep file_map inode_map file_block_map :=
   addrs_match file_map inode_map /\
   (forall inum inode file,
     inode_map inum  = Some inode ->
     file_map inum = Some file ->
     file_rep file inode file_block_map).

Definition files_rep (file_map: disk File) :=
  exists* inode_map file_block_map,
    inode_rep inode_map *
    DiskAllocator.block_allocator_rep file_block_map *
    [[ files_inner_rep file_map inode_map file_block_map ]].

Definition get_block_number inum off :=
  r <- get_inode inum;
  if r is Some inode then
    Ret (nth_error inode.(block_numbers) off)
  else
    Ret None.
  
Definition read inum off :=
  _ <-| Start;
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
   if r is Some v then
      _ <-| Commit;
     Ret r
    else
      _ <-| Abort;
      Ret r
  else
    _ <-| Abort;
    Ret None.

Definition write inum off v :=
  _ <-| Start;
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.write block_number v;
    if r is Some tt then
      _ <-| Commit;
     Ret r
    else
      _ <-| Abort;
      Ret r
  else
    _ <-| Abort;
    Ret None.

Definition change_owner inum owner :=
  _ <-| Start;
  r <- change_owner inum owner;
  if r is Some tt then
     _ <-| Commit;
     Ret r
  else
    _ <-| Abort;
    Ret r.

Definition create owner :=
  _ <-| Start;
  r <- alloc owner;
  if r is Some inum then
     _ <-| Commit;
     Ret r
  else
    _ <-| Abort;
    Ret r.

Definition delete inum :=
  _ <-| Start;
  r <- free inum;
  if r is Some tt then
     _ <-| Commit;
     Ret r
  else
    _ <-| Abort;
    Ret r.

Definition extend inum v :=
  _ <-| Start;
  r <- extend inum v;
  if r is Some tt then
     _ <-| Commit;
     Ret r
  else
    _ <-| Abort;
    Ret r.
