Require Import Framework LoggedDiskLayer Inode.

Open Scope pred_scope.

Record File :=
  {
    owner: user;
    blocks: list value;
  }.

Definition file_rep file (inode: Inode) : @pred addr addr_dec (set value) :=
  exists* fblocks,
  [[ file.(owner) = inode.(Inode.Definitions.owner) ]] *
  inode.(Inode.Definitions.blocks) |L> fblocks *
  [[ file.(blocks) = map fst fblocks ]].

Fixpoint file_list_inner_rep flist ilist :=
  match flist, ilist with
  | file::flist', inode::ilist' =>
    file_rep file inode * file_list_inner_rep flist' ilist'
  | _, _ => emp
  end.

Definition file_list_rep flist :=
  exists* ilist,
    inode_list_rep ilist *
    let valid_ilist := filter (fun inode => inode.(used)) ilist in
    [[ length flist = length valid_ilist ]] *
    file_list_inner_rep flist valid_ilist.


Definition read inum off :=
  inode <- get_inode inum;
  let bn := nth off inode.(Inode.Definitions.blocks) 0 in
  v <-| Read bn;
  Ret v.

Definition write inum off v :=
  inode <- get_inode inum;
  let bn := nth off inode.(Inode.Definitions.blocks) 0 in
  _ <-| Write [bn] [v];
  Ret tt.

Definition set_owner inum owner :=
  inode <- get_inode inum;
  let new_inode := Build_Inode inode.(used) owner inode.(Inode.Definitions.blocks) in
  _ <- set_inode inum new_inode;
  Ret tt.

Definition create owner :=
  minum <- get_last_unused_inum;
  match minum with
  | Some inum =>
    _ <- set_inode inum (Build_Inode true owner []);
    Ret (Some inum)
  | None =>
    Ret None
  end.

Definition delete inum :=
  inode <- get_inode inum;
  let new_inode := Build_Inode false inode.(Inode.Definitions.owner) [] in
  _ <- set_inode inum new_inode;
  Ret tt.
