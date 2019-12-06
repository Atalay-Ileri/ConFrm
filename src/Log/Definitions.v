Require Import PeanoNat Primitives Layer1.

Fixpoint arrayN {V} (a : addr) (vs : list V) : @pred addr addr_eq_dec V :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * arrayN (S a) vs'
  end%pred.


Infix "|=>" := arrayN (at level 35) : pred_scope.


Variable hdr_block_num: addr.
Variable log_start : addr.
Variable log_length : nat.

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

Definition cur_count_accurate (hdr: header) :=
  let txns := txn_records hdr in
  cur_count hdr = fold_right plus 0 (map addr_count txns) + fold_right plus 0 (map data_count txns).

Definition old_count_accurate (hdr: header) :=
  let txns := txn_records hdr in
  let otc := old_txn_count hdr in
  let old_txns := firstn otc txns in
  old_count hdr = fold_right plus 0 (map addr_count old_txns) + fold_right plus 0 (map data_count old_txns).

Definition cur_txns_valid (hdr: header) (log_blocks: list value) (kl: list key) (em: encryptionmap):=
  let txns := txn_records hdr in
  (forall txr,
    let tk := txn_key txr in
    let ts := txn_start txr in
    let ta := addr_count txr in
    let td := data_count txr in
    In txr txns ->
    In tk kl /\
    ts >= log_start /\
    ts + ta + td <= log_start + cur_count hdr /\
    (forall ev, In ev (firstn (ta+td) (skipn ts log_blocks)) ->
           exists v, em ev = Some (tk, v) /\ ev = encrypt tk v))%type.

Definition old_txns_valid (hdr: header) (log_blocks: list value) (kl: list key) (em: encryptionmap):=
  let txns := txn_records hdr in
  let otc := old_txn_count hdr in
  let old_txns := firstn otc txns in
  (forall txr,
    let tk := txn_key txr in
    let ts := txn_start txr in
    let ta := addr_count txr in
    let td := data_count txr in
    In txr old_txns ->
    In tk kl /\
    ts >= log_start /\
    ts + ta + td <= log_start + old_count hdr /\
    (forall ev, In ev (firstn (ta+td) (skipn ts log_blocks)) ->
           exists v, em ev = Some (tk, v) /\ ev = encrypt tk v))%type.
                                                                           

Fixpoint rolling_hash h vl :=
  match vl with
  | nil => h
  | v::vl' => rolling_hash (hash_function h v) vl'
  end.

Fixpoint hashes_in_hashmap hm h vl :=
  match vl with
  | nil => True
  | v::vl' =>
    let hv := hash_function h v in
    (hm hv = Some (h, v) /\ hashes_in_hashmap hm (hash_function h v) vl')%type
  end.

Definition cur_hash_valid hdr log_blocks :=
  cur_hash hdr = rolling_hash hash0 log_blocks.

Definition old_hash_valid hdr log_blocks :=
  let old_count := old_count hdr in
  old_hash hdr = rolling_hash hash0 (firstn old_count log_blocks).

Definition log_rep (hdr: header) (kl: list key) (em: encryptionmap) (hm: hashmap) :=
  exists* (log_blocks free: list value),
    (* Header *)
    hdr_block_num |-> (encode_header hdr) *
    (* Valid Region *)
    log_start |=> log_blocks *
    (* Free Region *)
    (log_start + length log_blocks) |=> free *
    (* Header log_count is correct *)
    [[ length log_blocks = cur_count hdr ]] *
    (* Old count is always leq *)
    [[ old_count hdr <= cur_count hdr ]] *
    (* log_length is correct *)            
    [[ length log_blocks + length free = log_length ]] *
    (* Header hashes is correct *)
    [[ cur_hash_valid hdr log_blocks ]] *
    [[ old_hash_valid hdr log_blocks ]] *
    [[ hashes_in_hashmap hm hash0 log_blocks ]] *
    (* Header log_count agrees with txn_records *)
    [[ cur_count_accurate hdr ]] *
    [[ old_count_accurate hdr ]] *
    (* Header current txn_records are valid *)
    [[ cur_txns_valid hdr log_blocks kl em ]] *
    [[ old_txns_valid hdr log_blocks kl em ]].


Axiom encrypt_all : key -> list value -> prog (list value).
Axiom decrypt_all : key -> list value -> prog (list value).
Axiom write_consecutive : addr -> list value -> prog unit.
Axiom write_batch : list addr -> list value -> prog unit.
Axiom read_consecutive : addr -> nat -> prog (list value).
Axiom hash_all : hash -> list value -> prog hash.

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
    new_key <- GetKey;
    enc_data <- encrypt_all new_key (addr_l ++ data_l);
    _ <- write_consecutive (log_start + cur_count) enc_data;
    let new_hash := rolling_hash cur_hash enc_data in
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
  let addr_list := nil (*TODO*) in
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

Definition apply_log :=
  hdr <- read_header;
  let old_hash := old_hash hdr in
  let old_count := old_count hdr in
  let old_txn_count := old_txn_count hdr in  
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  log <- read_consecutive log_start cur_count;
  log_hash <- hash_all hash0 log;
  if (hash_dec log_hash cur_hash) then
    _ <- flush_txns txns log;
    Ret true
  else
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    old_log_hash <- hash_all hash0 old_log;
    if (hash_dec old_log_hash old_hash) then
      _ <- flush_txns old_txns old_log;
      Ret true
    else
      Ret false.