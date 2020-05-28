Require Import Framework TransactionCacheLayer.
(*
Require Import Datatypes PeanoNat.
Require Import LogParameters.
 *)

Fixpoint get_latest (txn: list (addr * value)) a :=
  match txn  with
  | ad :: txn' =>
    if addr_eq_dec a (fst ad) then
      Some (snd ad)
    else
      get_latest txn' a
  | [] =>
    None
  end.

Definition start :=
  _ <- |TCCO| Put [];
  Ret tt.

Definition commit :=
  txn <- |TCCO| Get _;
  let al := fst (split (rev txn)) in
  let vl := snd (split (rev txn)) in
  _ <- |TCDO| Write al vl;
  _ <- |TCCO| Delete _;
  Ret tt.

Definition abort :=
  _ <- |TCCO| Delete _;
  Ret tt.

Definition read a :=
  txn <- |TCCO| Get _;
  match get_latest txn a with
  | Some v =>
    Ret v
  | None =>
    v <- |TCDO| Read a;
    Ret v
  end.

Definition write a v :=
  txn <- |TCCO| Get _;
  _   <- |TCCO| Put ((a, v)::txn);
  Ret tt.

Definition transaction_cache_rep txn (s: state TransactionCacheLang) :=
  fst s = Some txn.
