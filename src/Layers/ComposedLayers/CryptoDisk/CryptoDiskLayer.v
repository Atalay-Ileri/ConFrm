Require Import Framework FSParameters.
Require Export DiskLayer CryptoLayer.
Import ListNotations.

Set Implicit Arguments.

Definition CryptoDiskOperation  :=  HorizontalComposition CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)).
Definition CryptoDiskLang := Build_Language CryptoDiskOperation.  

Notation "'|CP|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) CryptoLang _ p) (at level 59).
Notation "'|DP|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) (DiskLang addr_dec value (fun a => a < disk_size)) _ p) (at level 59).
Notation "'|CO|' p" := (@lift_L1 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) CryptoLang _ (Op CryptoOperation p)) (at level 59).
Notation "'|DO|' p" := (@lift_L2 CryptoOperation (DiskOperation addr_dec value (fun a => a < disk_size)) (DiskLang addr_dec value (fun a => a < disk_size)) _ (Op (DiskOperation addr_dec value (fun a => a < disk_size)) p)) (at level 59). 


(** Selector does not cause a hash collision. **)
Definition non_colliding_selector selector (s: CryptoDiskLang.(state)) :=
  forall old_log_blocksets new_log_blocks,
    length old_log_blocksets = length new_log_blocks ->
    length old_log_blocksets <= log_length ->
    (forall i, i < length old_log_blocksets ->
          (snd s) (log_start + i) = selN old_log_blocksets i (value0, [])) ->
    (forall i, i < length new_log_blocks ->
          (select_total_mem selector (snd s)) (log_start + i) = selN (map (fun v => (v, [])) new_log_blocks) i (value0, [])) ->
    rolling_hash hash0 (map fst old_log_blocksets) = rolling_hash hash0 new_log_blocks ->
    map fst old_log_blocksets = new_log_blocks.
