Require Import Framework FSParameters AuthenticatedDiskLayer BlockAllocator Inode.
Import IfNotations.

Open Scope pred_scope.

Module DiskAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := file_blocks_start.
  Definition num_of_blocks := file_blocks_count.
  Definition num_of_blocks_in_bounds := file_blocks_count_in_bounds.
End DiskAllocatorParams.

Module DiskAllocator := BlockAllocator DiskAllocatorParams.

Record File :=
  {
    owner: user;
    blocks: list value;
  }.

Definition file_rep (file: File) (inode: Inode) (file_block_map: disk value) :=
  file.(owner) = inode.(Inode.owner) /\
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

Local Definition auth_then_exec {T} (inum: Inum) (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) :=
  _ <- |ADDO| Start;
  mo <- |ADDP| get_owner inum;
  if mo is Some owner then
    ok <- |ADAO| Auth owner;
    if ok is Some tt then
      r <- |ADDP| p inum;
      if r is Some v then
        _ <- |ADDO| Commit;
        Ret (Some v)
      else
        _ <- |ADDO| Abort;
        Ret None
    else
      _ <- |ADDO| Abort;
      Ret None
  else
    _ <- |ADDO| Abort;
    Ret None.
        
Local Definition read_inner off inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
    if r is Some v then
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Local Definition write_inner off v inum :=
  r <- get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.write block_number v;
    if r is Some tt then
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.

Local Definition change_owner_inner owner inum :=
  r <- change_owner inum owner;
  if r is Some tt then
     Ret (Some tt)
  else
    Ret None.

Local Fixpoint free_all_blocks block_nums :=
  match block_nums with
  | nil =>
    Ret (Some tt)
  | bn :: block_nums' =>
    ok <- DiskAllocator.free bn;
    if ok is Some tt then
      r <- free_all_blocks block_nums';
      Ret r
    else
      Ret None
end.

Local Definition delete_inner inum :=
  mbl <- get_block_numbers inum;
  if mbl is Some block_numbers then
    ok <- free_all_blocks block_numbers;
    if ok is Some tt then
      r <- free inum;
      if r is Some tt then
        Ret (Some tt)
      else
        Ret None
    else
      Ret None
  else
    Ret None.

Local Definition extend_inner v inum :=
  mbn <- DiskAllocator.alloc v;
  if mbn is Some block_num then
    r <- extend inum block_num;
    if r is Some tt then
      Ret (Some tt)
    else
      Ret None
  else
    Ret None.


Definition read inum off := auth_then_exec inum (read_inner off).
Definition write inum off v := auth_then_exec inum (write_inner off v).
Definition extend inum v := auth_then_exec inum (extend_inner v).
Definition change_owner inum owner := auth_then_exec inum (change_owner_inner owner).
Definition delete inum := auth_then_exec inum delete_inner.

Definition create owner :=
  _ <- |ADDO| Start;
  r <- |ADDP| alloc owner;
  if r is Some inum then
     _ <- |ADDO| Commit;
     Ret (Some inum)
  else
    _ <- |ADDO| Abort;
    Ret None.
