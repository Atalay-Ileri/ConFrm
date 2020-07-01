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

(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
  _ <- write_batch_to_cache addr_l data_l;
  _ <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
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


Definition cached_log_rep disk_frame merged_disk (s: Language.state CachedDiskLang) (log_state: Log_State):=
  exists hdr txns,
    fst s = txns_cache txns empty_mem /\
    addrs_match (fst s) (snd (snd s)) /\
    (log_rep log_state hdr txns (fst (snd s)) * disk_frame)%predicate (snd (snd s)) /\
    merged_disk = shift (plus data_start) (merge_set (fst s) (snd (snd s))).

