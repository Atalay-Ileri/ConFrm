Require Import Compare_dec Framework FSParameters TransactionCacheLayer.

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

(** Reverses before submitting **)
Definition commit :=
  txn <- |TCCO| Get _;
  let al := fst (split (rev txn)) in
  let vl := snd (split (rev txn)) in
  let dedup_al := dedup_last addr_dec al in
  let dedup_vl := dedup_by_list addr_dec al vl in
  _ <- |TCDO| Write dedup_al dedup_vl;
  _ <- |TCCO| Put [];
  Ret tt.

Definition abort :=
  _ <- |TCCO| Put [];
  Ret tt.

(* if you read out of bounds, you get 0 block *)
Definition read a :=
  if lt_dec a data_length then
    txn <- |TCCO| Get _;
    match get_latest txn a with
    | Some v =>
      Ret v
    | None =>
      v <- |TCDO| Read a;
      Ret v
    end
  else
    Ret value0.

(* if you write out of bounds, nothing happens *)
Definition write a v :=
  if lt_dec a data_length then
    txn <- |TCCO| Get _;
    if lt_dec (length txn) log_length then
      _ <- |TCCO| Put ((a, v)::txn);
      Ret tt
    else
      Ret tt
  else
    Ret tt.
