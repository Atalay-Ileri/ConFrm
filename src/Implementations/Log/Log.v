Require Import EquivDec Framework TotalMem CryptoDiskLayer BatchOperations.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.


(** A txn is laid out as addr blocks followed by data blocks *)
Record txn_record :=
  {
    key : key;   (* Encryption key of the txn *)
    start : nat;  (* Index of txn blocks in the log *)
    addr_count : nat; (* # of addr blocks in txn *)
    data_count : nat; (* # of data blocks in txn *)
  }.

Record txn :=
  {
    record : txn_record;
    addr_list: list addr; (* List of addresses *)
    addr_blocks : list value; (* UNENCRYPTED blocks. 
                                 Contains disk addresses *)
    data_blocks : list value; (* UNENCRYPTED blocks *)
  }.

Record header_part :=
  {
    hash : hash;
    count : nat;
    records : list txn_record;
  }.

Definition header_part0 := Build_header_part hash0 0 [].

Record header :=
  {
    old_part : header_part;
    current_part : header_part;
  }.

Definition header0 := Build_header header_part0 header_part0.

Definition update_hdr hdr hdr_part := Build_header (current_part hdr) hdr_part.

Axiom encode_header : header -> value.
Axiom decode_header : value -> header.
Axiom encode_decode_header : forall hdr, decode_header (encode_header hdr) = hdr.
Axiom decode_encode_header : forall v, encode_header (decode_header v) = v.


(* Programs *)
Definition read_header : prog CryptoDiskLang header:= 
  hd <- |DO| Read hdr_block_num;
  Ret (decode_header hd).


Definition write_header hdr :=
  |DO| Write hdr_block_num (encode_header hdr).

Definition update_header hdr_part :=
  hdr <- read_header;
  write_header (update_hdr hdr hdr_part).

Definition check_hash log hash :=
  log_hash <- hash_all hash0 log;
  if (hash_dec log_hash hash) then
    Ret true
  else
    Ret false.

(** Specs Done **)      
Definition decrypt_txn txn_record log_blocks :=
  let key := key txn_record in
  let start := start txn_record in
  let addr_count := addr_count txn_record in
  let data_count := data_count txn_record in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  
  plain_blocks <- decrypt_all key txn_blocks;

  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in

  Ret (addr_list, data_blocks).

(** Specs Done **)  
Definition apply_txn txn_record log_blocks :=
  al_db <- decrypt_txn txn_record log_blocks;
  let addr_list := fst al_db in
  let data_blocks := snd al_db in
  write_batch addr_list data_blocks.

(** Specs Done **)  
Fixpoint apply_txns txn_records log_blocks :=
  match txn_records with
  | nil =>
    Ret tt
  | txn_record::txn_records' =>
    _ <- apply_txn txn_record log_blocks;
    apply_txns txn_records' log_blocks
  end.

(** Specs Done **)
Definition flush_txns txn_records log_blocks :=
  _ <- apply_txns txn_records log_blocks;
  (** Crash here: old header, old log blocks **)
  _ <- |DO| Sync;
  _ <- update_header header_part0;
  (** Crash here: empty or old header, old log blocks **)
       |DO| Sync.


(** We don't know if old part or new part is valid.
    Needs to check hashes and return the correct one. **)
(** Specs Done **)
Definition read_encrypted_log :=
  hdr <- read_header;
  let current_part := current_part hdr in
  let old_part := old_part hdr in
  
  log <- read_consecutive log_start (count current_part);
  success <- check_hash log (hash current_part);
  if success then
    Ret (current_part, log)
  else
    log <- read_consecutive log_start (count old_part);
    Ret (old_part, log).

(** Specs Done **)
Definition apply_log :=
  hdr_log <- read_encrypted_log;

  let hdr_part := fst hdr_log in
  let log := snd hdr_log in
  let txn_records := records hdr_part in
  (** Crash here: old header, old log blocks **)
  flush_txns txn_records log
  (** Crash here: empty or old header, old log blocks **).

Definition commit_txn (addr_l data_l: list value) :=
  hdr <- read_header;

  let hash := hash (current_part hdr) in
  let count := count (current_part hdr) in
  let txn_records := records (current_part hdr) in
  
  new_key <- |CO| GetKey;
  enc_data <- encrypt_all new_key (addr_l ++ data_l);
  new_hash <- hash_all hash enc_data;
  
  _ <- write_consecutive (log_start + count) enc_data;
  
  (** Crash here: old header, partially new log blocks **)
  let new_count := count + (length addr_l + length data_l) in
  let new_txn := Build_txn_record new_key count (length addr_l) (length data_l) in
  let new_hdr_part := Build_header_part new_hash new_count (txn_records ++ [new_txn]) in

  _ <- update_header new_hdr_part;
  (** Crash here: new or old header, new log blocks **)
  |DO| Sync.

Definition commit (addr_l data_l: list value) :=
  hdr <- read_header;
  let cur_hash := hash (current_part hdr) in
  let cur_count := count (current_part hdr) in
  let txns := records (current_part hdr) in
  let new_count := cur_count + (length addr_l + length data_l) in
  if (log_length <? new_count) then
    (** Crash here: empty or old header, old log blocks **)
    Ret false
  else
    _ <- commit_txn addr_l data_l;
    Ret true.

(** Recovery **)
(** Specs Done **)
Fixpoint decrypt_txns txn_records log_blocks :=
  match txn_records with
  | nil =>
    Ret nil
  | record::txn_records' =>
    al_db <- decrypt_txn record log_blocks;
    l_al_db <- decrypt_txns txn_records' log_blocks;
    Ret (al_db::l_al_db)  
  end.

(** Specs Done **)
Definition recover :=
  hdr_log <- read_encrypted_log;
  
  let valid_hdr_part := fst hdr_log in
  let log := snd hdr_log in
  let txn_records := records valid_hdr_part in

  _ <- write_header (Build_header valid_hdr_part valid_hdr_part);
  _ <- |DO| Sync;
  decrypt_txns txn_records log.

Definition init l_av :=
  _ <- write_header header0;
  _ <- write_batch (map fst l_av) (map snd l_av);
  |DO| Sync.


(** Representation Invariants **)
Inductive Header_State :=
| Hdr_Synced : Header_State
| Hdr_Not_Synced (old_header_block: value) : Header_State.

Inductive Log_State :=
| Synced : Log_State
| Not_Synced : Log_State.

Inductive Valid_Part :=
| Current_Part : Valid_Part
| Old_Part : Valid_Part.

Inductive Log_Crash_State :=
| During_Apply (old_txns: list txn): Log_Crash_State
| During_Commit_Log_Write (txns: list txn): Log_Crash_State
| During_Commit_Header_Write (old_txns new_txns: list txn): Log_Crash_State
| During_Recovery (txns: list txn): Log_Crash_State
.

Definition record_is_valid key_list count record :=
  In (key record) key_list /\
  (start record) + (addr_count record) + (data_count record) <= count.

Fixpoint hashes_in_hashmap hm h vl :=
  match vl with
  | nil => True
  | v::vl' =>
    let hv := hash_function h v in
    (hm hv = Some (h, v) /\
     hashes_in_hashmap hm (hash_function h v) vl')%type
  end.

Fixpoint records_are_consecutive_starting_from n records :=
  match records with
  | [] => True
  | record :: records' =>
    start record = n /\
    records_are_consecutive_starting_from
      (start record + addr_count record + data_count record)
      records'
  end.

Definition header_part_is_valid log_blocks hash_map header_part :=
  let valid_log_blocks := firstn (count header_part) log_blocks in
  (** Hash validity *)
  hash header_part = rolling_hash hash0 valid_log_blocks /\
  hashes_in_hashmap hash_map hash0 valid_log_blocks /\
  (** Count validity *)
  (count header_part) <= log_length /\
  (count header_part) = fold_left Nat.add (map (fun rec => addr_count rec + data_count rec) (records header_part))0 /\
  (** Record validity **)
  records_are_consecutive_starting_from 0 (records header_part).

Definition txn_well_formed header_part (log_blocks: list value) key_list encryption_map (disk: @total_mem addr _ (set value)) txn :=
  let record := record txn in
  let key := key record in
  let start := start record in
  let addr_count := addr_count record in
  let data_count := data_count record in
  
  record_is_valid key_list (count header_part) record /\
  map (encrypt key) (addr_blocks txn) = firstn addr_count (skipn start log_blocks) /\
  map (encrypt key) (data_blocks txn) = firstn data_count (skipn (addr_count + start) log_blocks) /\
  addr_list txn = firstn (length (data_blocks txn)) (blocks_to_addr_list (addr_blocks txn)) /\
  NoDup (addr_list txn) /\
  Forall (fun a => disk_size > a  /\ a >= data_start) (addr_list txn) /\
  addr_count = length (addr_blocks txn) /\
  data_count = length (data_blocks txn) /\
  data_count <= length (blocks_to_addr_list (addr_blocks txn)) /\
  (forall i, i < addr_count -> encryption_map (encrypt key (seln (addr_blocks txn) i value0)) = Some (key, seln (addr_blocks txn) i value0)) /\
  (forall i, i < data_count -> encryption_map (encrypt key (seln (data_blocks txn) i value0)) = Some (key, seln (data_blocks txn) i value0)).


Definition txns_valid header_part (log_blocks: list value) key_list encryption_map disk (txns: list txn) :=
  (** Records match the header *)
  map record txns = records header_part /\
  Forall (txn_well_formed header_part log_blocks key_list encryption_map disk) txns.

Definition log_header_block_rep
           (header_state: Header_State)
           (hdr_blockset: set value)
           (state: state CryptoDiskLang) :=
  let crypto_maps := fst state in
  let disk := snd state in
    (** Header *)
    disk hdr_block_num = hdr_blockset /\
    (** Sync status **)
    match header_state with
    | Hdr_Synced =>
      snd hdr_blockset = []
    | Hdr_Not_Synced v =>
      snd hdr_blockset = [v]
    end.

Definition log_data_blocks_rep 
    (log_state: Log_State) (log_blocksets: list (set value))
    (state: state CryptoDiskLang) :=
  let crypto_maps := fst state in
  let disk := snd state in
    (** Log Blocks *)
    (forall i, i < length log_blocksets -> disk (log_start + i) = seln log_blocksets i (value0, [])) /\
    (** Sync status **)
    match log_state with
    | Synced =>
      (forall ls, In ls log_blocksets -> snd ls = [])
    | Not_Synced =>
      (forall ls, In ls log_blocksets -> length (snd ls) <= 1)
    end /\
    (** log length is valid *)
    length log_blocksets <= log_length.

Definition log_rep_inner
           (valid_part : Valid_Part)
           (hdr: header) (txns: list txn)
           (log_blocks: list value)
           (state: state CryptoDiskLang) :=
  let crypto_maps := fst state in
  let disk := snd state in
  let key_list := fst (fst crypto_maps) in
  let hash_map := snd (fst crypto_maps) in
  let encryption_map := snd crypto_maps in
  let header_part :=
      match valid_part with
      | Old_Part => old_part hdr
      | Current_Part => current_part hdr
      end in
  header_part_is_valid log_blocks hash_map header_part /\
  txns_valid header_part log_blocks key_list encryption_map disk txns.


Definition log_rep_explicit (header_state: Header_State) (log_state: Log_State) (valid_part: Valid_Part) (hdr: header) (txns: list txn) 
  (hdr_blockset: set value) (log_blocksets: list (set value)) (state: state CryptoDiskLang) :=
    hdr = decode_header (fst hdr_blockset) /\
    log_header_block_rep header_state hdr_blockset state /\
    log_data_blocks_rep log_state log_blocksets state /\
    length log_blocksets = log_length /\
    count (current_part hdr) <= log_length /\
    count (old_part hdr) <= log_length /\
    log_rep_inner valid_part hdr txns (map fst log_blocksets) state.

Definition log_rep_general (header_state: Header_State) (log_state: Log_State) (valid_part: Valid_Part) (hdr: header) (txns: list txn) (state: state CryptoDiskLang) :=
  exists (hdr_blockset: set value) (log_blocksets: list (set value)),
    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets state.

Definition log_rep (txns: list txn) (state: state CryptoDiskLang) :=
  exists hdr, log_rep_general Hdr_Synced Synced Current_Part hdr txns state.

Definition log_header_rep (hdr: header) (txns: list txn) (state: state CryptoDiskLang) :=
  log_rep_general Hdr_Synced Synced Current_Part hdr txns state.


Definition log_crash_rep (log_crash_state: Log_Crash_State) (state: state CryptoDiskLang) :=
  match log_crash_state with
  | During_Apply txns =>

    exists new_hdr_block old_hdr_block (log_blocksets: list (set value)),
       current_part (decode_header old_hdr_block) = old_part (decode_header new_hdr_block) /\
       log_rep_explicit (Hdr_Not_Synced old_hdr_block) Synced Current_Part (decode_header new_hdr_block) []
                       (new_hdr_block, [old_hdr_block]) log_blocksets state /\
       log_rep_inner Current_Part (decode_header old_hdr_block) txns (map fst log_blocksets) state /\
       count (old_part (decode_header old_hdr_block)) <= log_length

  | During_Commit_Log_Write txns =>
    
    exists hdr_blockset (synced_log_blocksets: list (set value)) (unsynced_log_blocksets: list (set value)),
      let hdr := decode_header (fst hdr_blockset) in
      let log_blocksets := synced_log_blocksets ++ unsynced_log_blocksets in

      log_header_block_rep Hdr_Synced hdr_blockset state /\
      log_data_blocks_rep Synced synced_log_blocksets state /\
      log_data_blocks_rep Not_Synced log_blocksets state /\
      length log_blocksets = log_length /\
      count (current_part hdr) <= log_length /\
      count (old_part hdr) <= log_length /\
      length synced_log_blocksets >= count (current_part hdr) /\
      log_rep_inner Current_Part hdr txns (map fst log_blocksets) state

  | During_Commit_Header_Write old_txns new_txns =>
    exists old_hdr_block new_hdr_block
      (synced_log_blocksets: list (set value)) (unsynced_log_blocksets: list (set value)),
      let hdr_blockset := (new_hdr_block, [old_hdr_block]) in
      let hdr := decode_header (fst hdr_blockset) in
      let log_blocksets := synced_log_blocksets ++ unsynced_log_blocksets in

      current_part (decode_header old_hdr_block) = old_part (decode_header new_hdr_block) /\
      log_header_block_rep (Hdr_Not_Synced old_hdr_block) hdr_blockset state /\
      log_data_blocks_rep Synced synced_log_blocksets state /\
      log_data_blocks_rep Not_Synced log_blocksets state /\
      length log_blocksets = log_length /\
      count (current_part hdr) <= log_length /\
      count (old_part hdr) <= log_length /\
      count (old_part (decode_header old_hdr_block)) <= log_length /\
      length synced_log_blocksets >= count (old_part hdr) /\
      
      log_rep_inner Current_Part hdr new_txns (map fst log_blocksets) state /\
      log_rep_inner Old_Part hdr old_txns (map fst log_blocksets) state /\
      (forall i, i >= count (current_part (decode_header old_hdr_block)) ->
      i < count (current_part (decode_header new_hdr_block)) -> 
      length (snd (seln log_blocksets i (value0 ,[]))) = 1) /\
      length synced_log_blocksets = count (current_part (decode_header old_hdr_block))

  | During_Recovery txns =>
    
    exists old_hdr_block new_hdr_block
      (log_blocksets: list (set value)),
      let hdr_blockset := (new_hdr_block, [old_hdr_block]) in
      let hdr := decode_header new_hdr_block in
      let old_hdr := decode_header old_hdr_block in
      
      log_header_block_rep (Hdr_Not_Synced old_hdr_block) hdr_blockset state /\
      log_data_blocks_rep Synced log_blocksets state /\
      length log_blocksets = log_length /\
      count (current_part hdr) <= log_length /\
      count (old_part hdr) <= log_length /\
      count (current_part old_hdr) <= log_length /\
      count (old_part old_hdr) <= log_length /\
      
      log_rep_inner Current_Part hdr txns (map fst log_blocksets) state /\
      (log_rep_inner Current_Part old_hdr txns (map fst log_blocksets) state \/
       (log_rep_inner Old_Part old_hdr txns (map fst log_blocksets) state /\
      hash (current_part old_hdr) <> rolling_hash hash0 (firstn (count (current_part old_hdr)) (map fst log_blocksets))))
  end.

Definition log_reboot_rep  (txns: list txn) (state: state CryptoDiskLang) :=
  exists hdr valid_part
    (hdr_blockset: set value) (log_blocksets: list (set value)),
    log_rep_explicit Hdr_Synced Synced valid_part hdr txns hdr_blockset log_blocksets state /\
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))).

Definition log_reboot_rep_explicit_part hdr (txns: list txn) valid_part (state: state CryptoDiskLang) :=
        exists (hdr_blockset: set value) (log_blocksets: list (set value)),
        log_rep_explicit Hdr_Synced Synced valid_part hdr txns hdr_blockset log_blocksets state /\
        (valid_part = Old_Part ->
         hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))).

