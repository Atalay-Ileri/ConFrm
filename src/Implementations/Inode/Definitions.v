Require Import Framework LoggedDiskLayer.

(* For simplicity, it will be 1 inode per block *)
Axiom inode_count: nat.

Definition Inum := addr.

Record Inode :=
  {
    used : bool;
    owner: user;
    blocks : list addr;
  }.

Variable encode_inode : Inode -> value.
Variable decode_inode: value -> Inode.
Axiom inode_encode_decode:
  forall i,
    decode_inode (encode_inode i) = i.
Axiom inode_decode_encode:
  forall b,
    encode_inode (decode_inode b) = b.

Open Scope pred_scope.

Definition inode_list_rep ilist : @pred addr addr_dec (set value) :=
  exists* inode_blocks,
  0 |=> inode_blocks *
  [[ length inode_blocks = inode_count ]] *
  [[ ilist = map (fun bs => decode_inode (fst bs)) inode_blocks ]].

Definition get_inode inum :=
  i <-| Read inum;
  Ret (decode_inode i).

Fixpoint get_last_unused_inum_rec n :=
  match n with
  | 0 =>
    Ret None
  | S n' =>
    inode <- get_inode n';
    if inode.(used) then
      un <- get_last_unused_inum_rec n';
      Ret un
    else
      Ret (Some n')
end.

Definition get_last_unused_inum :=
  inum <- get_last_unused_inum_rec inode_count;
  Ret inum.

Definition set_inode inum inode:=
  _ <-| Write [inum] [encode_inode inode];
  Ret tt.

















