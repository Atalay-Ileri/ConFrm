Require Import Framework CryptoDiskLayer BatchOperations.
Require Import Datatypes PeanoNat.
Require Import FSParameters.

Axiom blocks_to_addr_list : list value -> list addr.

Record txn_record :=
  {
    txn_key : key;   (* Encryption key of the txn *)
    txn_start : nat;  (* Index of txn blocks in the log *)
    addr_count : nat; (* # of addr blocks in txn *)
    data_count : nat; (* # of data blocks in txn *)
  }.

Record txn :=
  {
    record : txn_record;
    addr_blocks : list value; (* UNENCRYPTED blocks. 
                                 Contains disk addresses *)
    data_blocks : list value; (* UNENCRYPTED blocks *)
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

Definition header0 := Build_header hash0 0 0 hash0 0 nil.

Record header_part :=
  {
    hash : hash;
    count : nat;
    records : list txn_record;
  }.

Axiom encode_header : header -> value.
Axiom decode_header : value -> header.
Axiom encode_decode_header : forall hdr, decode_header (encode_header hdr) = hdr.
Axiom decode_encode_header : forall v, encode_header (decode_header v) = v.



(* Programs *)
Local Definition read_header :=
  hd <- |DO| Read hdr_block_num;
  Ret (decode_header hd).

Local Definition write_header hdr :=
  _ <- |DO| Write hdr_block_num (encode_header hdr);
  Ret tt.

Local Definition apply_txn txn log_blocks :=
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

Local Fixpoint apply_txns txns log_blocks :=
  match txns with
  | nil =>
    Ret tt
  | txn::txns' =>
    _ <- apply_txn txn log_blocks;
    _ <- apply_txns txns' log_blocks;
    Ret tt  
  end.

Local Definition flush_txns txns log_blocks :=
  _ <- apply_txns txns log_blocks;
  _ <- write_header header0;
  _ <- |DO| Sync;
  Ret tt.

Local Definition check_and_flush txns log hash :=
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
    Ret tt
  else
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    success <- check_and_flush old_txns old_log old_hash;
    Ret tt.


Local Definition commit_txn (addr_l data_l: list value) :=
  hdr <- read_header;
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  new_key <- |CO| GetKey (addr_l++data_l);
  enc_data <- encrypt_all new_key (addr_l ++ data_l);
  new_hash <- hash_all cur_hash enc_data;

  _ <- write_consecutive (log_start + cur_count) enc_data;

  let new_count := cur_count + (length addr_l + length data_l) in
  let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
  let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
  _ <- write_header new_hdr;
  _ <- |DO| Sync;
  Ret tt.

Definition commit (addr_l data_l: list value) :=
  hdr <- read_header;
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  let new_count := cur_count + (length addr_l + length data_l) in
  _ <-
  if (log_length <? new_count) then
    apply_log 
  else
    Ret tt;
  _ <- commit_txn addr_l data_l;
  Ret tt.


(* Representation Invariants *)

Inductive Log_State :=
| Synced : Log_State
| Not_Synced : Log_State.

Definition get_valid_part (hdr: header) blocks : header_part :=
  if (hash_dec (cur_hash hdr) (rolling_hash hash0 (firstn (cur_count hdr) blocks))) then
    Build_header_part (cur_hash hdr) (cur_count hdr) (txn_records hdr)
  else
    Build_header_part (old_hash hdr) (old_count hdr) (firstn (old_txn_count hdr) (txn_records hdr)).

Fixpoint encryption_present (blocks: list value)(k: key)(em: encryptionmap) :=
  match blocks with
  | b::blocks' =>
    em (encrypt k b) = Some (k,b) /\
    encryption_present blocks' k em
  | [] => True
  end.

Fixpoint txns_valid (txns: list txn) (log_blocks: list value) (kl: list key) (em: encryptionmap):=
  match txns with
    | tx::txns' =>
      let txa := addr_blocks tx in
      let txd := data_blocks tx in
      let txr := record tx in
      let tk := txn_key txr in
      let ts := txn_start txr in
      let ta := addr_count txr in
      let td := data_count txr in
      In tk kl /\
      ta = length txa /\
      td = length txd /\
      ts + ta + td <= length log_blocks /\
      map (encrypt tk) (txa ++ txd) = firstn (ta+td) (skipn ts log_blocks) /\
      encryption_present (txa++txd) tk em
    |[] => True
  end.

Fixpoint hashes_in_hashmap hm h vl :=
  match vl with
  | nil => True
  | v::vl' =>
    let hv := hash_function h v in
    (hm hv = Some (h, v) /\
     hashes_in_hashmap hm (hash_function h v) vl')%type
  end.

Definition hash_valid log_blocks hash :=
  hash = rolling_hash hash0 log_blocks.

Open Scope pred_scope.

Definition log_rep_inner
           (log_state: Log_State)
           (hdr: header) (txns: list txn)
           (hdr_blockset: set value) (log_blocksets: list (set value))
           (ax: list key * encryptionmap * hashmap) :=
  let kl := fst (fst ax) in
  let em := snd (fst ax) in
  let hm := snd ax in
  let log_blocks := map fst log_blocksets in
  let valid_hdr := get_valid_part hdr log_blocks in
  let valid_log_blocks := firstn (count valid_hdr) log_blocks in  
    (* Header *)
    hdr_block_num |-> hdr_blockset *
    (* Log Blocks *)
    log_start |=> log_blocksets *
    [[ hdr = decode_header (fst hdr_blockset)]] *
    [[ match log_state with
       | Synced =>
         snd hdr_blockset = []
       | Not_Synced =>
         exists v, snd hdr_blockset = v :: nil
       end
    ]] *
    (* log length is valid *)
    [[ length log_blocksets = log_length ]] *
    (* txns represents the right thing *)
    [[ map record txns = records valid_hdr ]] *
    (* Header hashes is correct *)
    [[ hash_valid valid_log_blocks (hash valid_hdr) ]] *
    [[ hashes_in_hashmap hm hash0 valid_log_blocks ]] *
    (* Header current txn_records are valid *)
    [[ txns_valid txns valid_log_blocks kl em ]].

Definition log_rep (log_state: Log_State) (hdr: header) (txns: list txn) (ax: list key * encryptionmap * hashmap) :=
  exists* (hdr_blockset: set value) (log_blocksets: list (set value)),
    log_rep_inner log_state hdr txns hdr_blockset log_blocksets ax.

Hint Extern 0 (okToUnify (log_rep_inner _ _ ?b _) (log_rep_inner _ _ ?b  _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (log_rep ?txns _) (log_rep ?txns _)) => constructor : okToUnify.
