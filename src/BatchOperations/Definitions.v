Require Import Primitives DiskLayer.

Fixpoint encrypt_all k vl :=
  match vl with
  | nil => Ret nil
  | v::vl' =>
    ev <- Encrypt k v;
    evl' <- encrypt_all k vl';
    Ret (ev::evl')
  end.

Fixpoint decrypt_all k evl :=
  match evl with
  | nil => Ret nil
  | ev::evl' =>
    v <- Decrypt k ev;
    vl' <- decrypt_all k evl';
    Ret (v::vl')
  end.

Fixpoint write_consecutive a vl :=
  match vl with
  | nil => Ret tt
  | v::vl' =>
    _ <- Write a v;
    _ <- write_consecutive (S a) vl';
    Ret tt
  end.

Fixpoint read_consecutive a count:=
  match count with
  | 0 => Ret nil
  | S count' =>
    v <- Read a;
    vl <- read_consecutive (S a) count';
    Ret (v::vl)
  end.

Fixpoint write_batch al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- Write a v;
    _ <- write_batch al' vl';
    Ret tt            
  | _, _ => Ret tt
  end.

Fixpoint hash_all h vl :=
  match vl with
  | nil => Ret h
  | v::vl' =>
    h' <- Hash h v;
    h'' <- hash_all h' vl';
    Ret h''
  end.

