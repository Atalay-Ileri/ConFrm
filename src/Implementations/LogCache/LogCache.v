Require Import Datatypes PeanoNat Framework FSParameters Log.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer.

Local Fixpoint write_batch_to_cache al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |CDCO| Write a v;
    _ <- write_batch_to_cache al' vl';
    Ret tt            
  | _, _ => Ret tt
 end.

Definition NoDup_dec {T} {TEQ: EqDec T}: forall (l: list T), {NoDup l}+{~NoDup l}.
  induction l; simpl; intuition.
  left; constructor.
  destruct (in_dec TEQ a l).
  right; intuition eauto.
  inversion H; eauto.
  left; constructor; eauto.
  right; intuition eauto.
  inversion H; eauto.
Defined.  
  
(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
  if (NoDup_dec addr_l) then
    if (Nat.eq_dec (length addr_l) (length data_l)) then
      _ <- write_batch_to_cache addr_l data_l;
      _ <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
      Ret tt
    else
      Ret tt
  else
    Ret tt.


(* Takes a data region_address *)
Definition read a :=
  mv <- |CDCO| Read _ (data_start + a);
  match mv with
  | Some v =>
    Ret v
  | None =>
    v <- |CDDP| |DO| DiskLayer.Read (data_start + a);
    Ret v
  end.


Fixpoint txns_cache (txns: list txn) cache : @mem addr addr_dec value :=
  match txns with
  | txn::txns' =>
    let addr_list := blocks_to_addr_list (addr_blocks txn) in
    let data_blocks := data_blocks txn in
    txns_cache txns' (upd_batch cache addr_list data_blocks)
  | [] => cache
  end.

Definition txn_well_formed txn :=
  let addr_list := blocks_to_addr_list (addr_blocks txn) in
  let data_blocks := data_blocks txn in
  NoDup addr_list /\ length addr_list = length data_blocks.

Definition cached_log_rep disk_frame merged_disk (s: Language.state CachedDiskLang) (log_state: Log_State):=
  exists hdr txns,
    fst s = txns_cache txns empty_mem /\
    addrs_match (fst s) (snd (snd s)) /\
    Forall txn_well_formed txns /\
    (log_rep log_state hdr txns (fst (snd s)) * disk_frame)%predicate (snd (snd s)) /\
    merged_disk = shift (plus data_start) (merge_set (fst s) (snd (snd s))).

