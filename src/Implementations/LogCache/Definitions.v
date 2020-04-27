Require Import Datatypes PeanoNat Framework Log.
Require Import DiskLayer CacheLayer CryptoDiskLayer CachedDiskLayer.

Axiom addr_list_to_blocks : list addr -> list value.

Fixpoint write_batch al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |CDCO| Write a v;
    _ <- write_batch al' vl';
    Ret tt            
  | _, _ => Ret tt
  end.

Definition write  addr_l (data_l: list value) :=
  _ <- write_batch addr_l data_l;
  _ <- |CDDP| commit (addr_list_to_blocks addr_l) data_l;
  Ret tt.

Definition read a :=
  mv <- |CDCO| Read a;
  match mv with
  | Some v =>
    Ret v
  | None =>
    v <- |CDDP| |DO| DiskLayer.Definitions.Read a;
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

Definition merge {A AEQ V} (m1: @mem A AEQ V) (m2: @mem A AEQ (V * list V)) : @mem A AEQ (V * list V) :=
  fun a =>
    match m1 a with
    | None => m2 a
    | Some v =>
      match m2 a with
      | None => None
      | Some vs =>
        Some (v, fst vs::snd vs)
      end
    end.

Definition cached_log_rep disk_frame merged_disk (s: Language.state CachedDiskLang) :=
  exists hdr txns,
    fst s = txns_cache txns empty_mem /\
    (log_rep hdr txns (fst (snd s)) * disk_frame)%pred (snd (snd s)) /\
    merged_disk = merge (fst s) (snd (snd s)).

