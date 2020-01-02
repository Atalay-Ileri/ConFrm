Require Import Datatypes PeanoNat Primitives Layer1 BatchOperations.
Require Import LogParameters.

Record txn_record :=
  {
    txn_key : key;
    txn_start : nat; (* Relative to start of the log *)
    addr_count : nat;
    data_count : nat;
  }.

Record header :=
  {
    old_hash : hash;
    old_count : nat;
    old_txn_count: nat;
    cur_hash : hash;
    cur_count : nat;
    txn_records : list txn_record;
  }.

Axiom encode_header : header -> value.
Axiom decode_header : value -> header.
Axiom encode_decode_header : forall hdr, decode_header (encode_header hdr) = hdr.
Axiom decode_encode_header : forall v, encode_header (decode_header v) = v.

Definition header0 := Build_header hash0 0 0 hash0 0 nil.

Definition count_accurate (hdr: header) (txn_count count: nat):=
  let txns := firstn txn_count (txn_records hdr) in
  count = fold_right plus 0 (map addr_count txns) + fold_right plus 0 (map data_count txns).

Definition txns_valid (hdr: header) (log_blocks: list value) (kl: list key) (em: encryptionmap):=
  let txns :=txn_records hdr in
  (forall txr,
    let tk := txn_key txr in
    let ts := txn_start txr in
    let ta := addr_count txr in
    let td := data_count txr in
    In txr txns ->
    In tk kl /\
    ts + ta + td <= length log_blocks /\
    (forall ev, In ev (firstn (ta+td) (skipn ts log_blocks)) ->
           exists v, em ev = Some (tk, v) /\ ev = encrypt tk v))%type.                                                                         
Fixpoint hashes_in_hashmap hm h vl :=
  match vl with
  | nil => True
  | v::vl' =>
    let hv := hash_function h v in
    (hm hv = Some (h, v) /\ hashes_in_hashmap hm (hash_function h v) vl')%type
  end.

Definition hash_valid log_blocks hash :=
  hash = rolling_hash hash0 log_blocks.

Definition log_rep_inner (hdr: header) (log_blocks: list value) (log_blockset: list data) (ax: list key * encryptionmap * hashmap) :=
  let kl := fst (fst ax) in
  let em := snd (fst ax) in
  let hm := snd ax in
  exists* hdr_block,
    (* Header *)
    hdr_block_num |-> hdr_block *
    (* Valid Region *)
    log_start |=> log_blockset *
    (* log length is valid *)
    [[ length log_blockset = log_length ]] *
    (* Hdr is correct representation *)
    [[ hdr = decode_header (fst hdr_block) ]] *
    [[ log_blocks = map fst log_blockset ]] *
    (* Old count is always leq *)
    [[ old_count hdr <= cur_count hdr ]] *
    (* Header hashes is correct *)
    [[ hash_valid (firstn (cur_count hdr) log_blocks) (cur_hash hdr) ]] *
    [[ hash_valid (firstn (old_count hdr) log_blocks) (old_hash hdr) ]] *
    [[ hashes_in_hashmap hm hash0 (firstn (cur_count hdr) log_blocks) ]] *
    (* Header log_count agrees with txn_records *)
    [[ count_accurate hdr (length (txn_records hdr)) (cur_count hdr)]] *
    [[ count_accurate hdr (old_txn_count hdr) (old_count hdr)]] *
    (* Header current txn_records are valid *)
    [[ txns_valid hdr log_blocks kl em ]].


Definition log_rep (hdr: header) (log_blocks: list value) (ax: list key * encryptionmap * hashmap) :=
  exists* (log_blockset: list data), log_rep_inner hdr log_blocks log_blockset ax.

Hint Extern 0 (okToUnify (log_rep_inner _ _ _ _ ?a) (log_rep_inner _ _ ?a)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (log_rep_inner _ ?b _ _ _) (log_rep_inner ?b _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (log_rep _ _ ?a) (log_rep _ ?a)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (log_rep ?hdr _ _) (log_rep ?hdr _ _)) => constructor : okToUnify.

Axiom blocks_to_addr_list : list value -> list addr.

(* Programs *)
Definition read_header :=
  hd <- Read hdr_block_num;
  Ret (decode_header hd).

Definition write_header hdr :=
  _ <- Write hdr_block_num (encode_header hdr);
  Ret tt.


Definition commit (addr_l data_l: list value) :=
  hdr <- read_header;
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  let new_count := cur_count + (length addr_l + length data_l) in
  if (new_count <=? log_length) then
    new_key <- GetKey (addr_l++data_l);
    enc_data <- encrypt_all new_key (addr_l ++ data_l);
    _ <- write_consecutive (log_start + cur_count) enc_data;
    new_hash <- hash_all cur_hash enc_data;
    let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
    let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
    _ <- write_header new_hdr;
    Ret true
  else
    Ret false.

Definition apply_txn txn log_blocks :=
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  plain_blocks <- decrypt_all key txn_blocks;
  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks)in
  _ <- write_batch addr_list data_blocks;
  Ret tt.


Fixpoint apply_txns txns log_blocks :=
  match txns with
  | nil =>
    Ret tt
  | txn::txns' =>
    _ <- apply_txn txn log_blocks;
    _ <- apply_txns txns' log_blocks;
    Ret tt  
  end.

Definition flush_txns txns log_blocks :=
  _ <- apply_txns txns log_blocks;
  _ <- write_header header0;
  Ret tt.

Definition check_and_flush txns log hash :=
  log_hash <- hash_all hash0 log;
  if (hash_dec log_hash hash) then
    _ <- flush_txns txns log;
    Ret true
  else
    Ret false.

Definition apply_log :=
  hdr <- read_header;
  let old_hash := old_hash hdr in
  let old_count := old_count hdr in
  let old_txn_count := old_txn_count hdr in  
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  log <- read_consecutive log_start cur_count;
  success <- check_and_flush txns log cur_hash;
  if success then
    Ret true
  else
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    success <- check_and_flush old_txns old_log old_hash;
    Ret success.