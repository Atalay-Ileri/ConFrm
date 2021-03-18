Require Import Framework FSParameters AuthenticatedDiskLayer.
Require Import BlockAllocator Inode.
Require Import Compare_dec FunctionalExtensionality Lia.
Import IfNotations.




Module DiskAllocatorParams <: BlockAllocatorParameters.
  Definition bitmap_addr := file_blocks_start.
  Definition num_of_blocks := file_blocks_count.
  Definition num_of_blocks_in_bounds := file_blocks_count_in_bounds.
  Definition blocks_fit_in_disk := file_blocks_fit_in_disk.
End DiskAllocatorParams.

Module DiskAllocator := BlockAllocator DiskAllocatorParams.

(*** Rep Invariants ***)
Definition file_rep (file: File) (inode: Inode) (file_block_map: disk value) :=
  file.(BaseTypes.owner) = inode.(Inode.owner) /\
  length file.(blocks) = length inode.(block_numbers) /\
  (forall i block_number,
       nth_error inode.(block_numbers) i = Some block_number ->
       exists block,
         nth_error file.(blocks) i = Some block /\
         file_block_map block_number = Some block).

Definition file_map_rep (file_disk: @mem Inum addr_dec File) inode_map file_block_map :=
   addrs_match_exactly file_disk inode_map /\
   (forall inum inode file,
     inode_map inum  = Some inode ->
     file_disk inum = Some file ->
     file_rep file inode file_block_map).

Definition files_inner_rep (file_disk: disk File) (d: @total_mem addr addr_dec value):=
  exists inode_map,
    inode_rep inode_map d /\
    
  exists file_block_map,
    DiskAllocator.block_allocator_rep file_block_map d /\
    file_map_rep file_disk inode_map file_block_map.

Definition files_rep (file_disk: disk File) (d: AuthenticatedDiskLang.(state)) :=
  fst (snd d) = snd (snd d) /\
  files_inner_rep file_disk (fst (snd d)).

Definition files_crash_rep (file_disk: disk File) (d: AuthenticatedDiskLang.(state)) :=
  files_inner_rep file_disk (snd (snd d)).

Definition files_reboot_rep := files_crash_rep.


(*** Functions ***)
Definition auth_then_exec {T} (inum: Inum) (p: Inum -> prog (TransactionalDiskLang data_length) (option T)) :=
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
        
Definition read_inner off inum :=
  r <- Inode.get_block_number inum off;
  if r is Some block_number then
    r <- DiskAllocator.read block_number;
    if r is Some v then
      Ret (Some v)
    else
      Ret None
  else
    Ret None.

Definition write_inner off v inum :=
  r <- Inode.get_block_number inum off;
  if r is Some block_number then
    DiskAllocator.write block_number v
  else
    Ret None.

Definition change_owner_inner owner inum :=
  Inode.change_owner inum owner.


Fixpoint free_all_blocks block_nums :=
  match block_nums with
  | nil =>
    Ret (Some tt)
  | bn :: block_nums' =>
    ok <- DiskAllocator.free bn;
    if ok is Some tt then
      free_all_blocks block_nums'
    else
      Ret None
end.

Definition delete_inner inum :=
  mbl <- Inode.get_all_block_numbers inum;
  if mbl is Some block_numbers then
    ok <- free_all_blocks block_numbers;
    if ok is Some tt then
      free inum
    else
      Ret None
  else
    Ret None.

Definition extend_inner v inum :=
  mbn <- DiskAllocator.alloc v;
  if mbn is Some block_num then
    Inode.extend inum block_num
  else
    Ret None.


Definition read inum off := auth_then_exec inum (read_inner off).
Definition write inum off v := auth_then_exec inum (write_inner off v).
Definition extend inum v := auth_then_exec inum (extend_inner v).
Definition change_owner inum owner := auth_then_exec inum (change_owner_inner owner).
Definition delete inum := auth_then_exec inum delete_inner.

Definition create owner :=
  r <- |ADDP| Inode.alloc owner;
  if r is Some inum then
     _ <- |ADDO| Commit;
     Ret (Some inum)
  else
    _ <- |ADDO| Abort;
    Ret None.

Definition recover := |ADDO| Recover.

Definition init :=
|ADDO| Init [(Inode.InodeAllocatorParams.bitmap_addr,
              bits_to_value zero_bitlist);
            (DiskAllocatorParams.bitmap_addr,
             bits_to_value zero_bitlist)].

Definition update_file f off v := Build_File f.(BaseTypes.owner) (updN f.(blocks) off v).
Definition extend_file f v := Build_File f.(BaseTypes.owner) (f.(blocks) ++ [v]).
Definition new_file o := Build_File o [].
Definition change_file_owner f o := Build_File o f.(blocks).
