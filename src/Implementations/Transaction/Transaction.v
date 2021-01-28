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
  _ <- |TCCO| Delete _;
  Ret tt.

(** Reverses before submitting **)
Definition commit :=
  txn <- |TCCO| Get _;
  let al := map fst (rev txn) in
  let vl := map snd (rev txn) in
  let dedup_al := dedup_last addr_dec al in
  let dedup_vl := dedup_by_list addr_dec al vl in
  _ <- |TCDO| Write dedup_al dedup_vl;
  _ <- |TCCO| Delete _;
  Ret tt.

Definition abort :=
  _ <- |TCCO| Delete _;
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
      _ <- |TCCO| Put (a, v);
      Ret tt
    else
      Ret tt
  else
    Ret tt.

Definition recover :=
  _ <- |TCDO| Recover;
  Ret tt.

Definition transaction_rep (tcd: TransactionCacheLang.(state)) (td: (@mem addr addr_dec value) * (@total_mem addr addr_dec value)):=
  let al := map fst (fst tcd) in
  let vl := map snd (fst tcd) in
  let dedup_al := dedup_last addr_dec al in
  let dedup_vl := dedup_by_list addr_dec al vl in
  fst td = Mem.upd_batch empty_mem dedup_al dedup_vl /\
  snd td = snd tcd.
  
