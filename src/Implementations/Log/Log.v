Require Import EquivDec Framework CryptoDiskLayer BatchOperations.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
  
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
Definition read_header :=
  hd <- |DO| Read hdr_block_num;
  Ret (decode_header hd).

Definition write_header hdr :=
  _ <- |DO| Write hdr_block_num (encode_header hdr);
  Ret tt.


Definition decrypt_txn txn log_blocks :=
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  
  plain_blocks <- decrypt_all key txn_blocks;

  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks)in

  Ret (addr_list, data_blocks).

Definition apply_txn txn log_blocks :=
  al_db <- decrypt_txn txn log_blocks;
  let addr_list := fst al_db in
  let data_blocks := snd al_db in
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
  _ <- |DO| Sync;
  Ret tt.

Definition check_hash log hash :=
  log_hash <- hash_all hash0 log;
  if (hash_dec log_hash hash) then
    Ret true
  else
    Ret false.

Definition read_encrypted_log :=
  hdr <- read_header;
  let cur_count := cur_count hdr in
  log <- read_consecutive log_start cur_count;
  Ret (hdr, log).

Definition apply_log :=
  hdr_log <- read_encrypted_log;

  let hdr := fst hdr_log in
  let log := snd hdr_log in
  
  let cur_hash := cur_hash hdr in
  let txns := txn_records hdr in

  success <- check_hash log cur_hash;

  _ <- if success then
    flush_txns txns log
  else
    let old_count := old_count hdr in
    let old_txn_count := old_txn_count hdr in
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    flush_txns old_txns old_log;
  Ret tt.


Definition commit_txn (addr_l data_l: list value) :=
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

Fixpoint decrypt_txns txns log_blocks :=
  match txns with
  | nil =>
    Ret nil
  | txn::txns' =>
    al_db <- decrypt_txn txn log_blocks;
    l_al_db <- decrypt_txns txns' log_blocks;
    Ret (al_db::l_al_db)  
  end.

Definition read_log :=
  hdr_log <- read_encrypted_log;

  let hdr := fst hdr_log in
  let log := snd hdr_log in

  let cur_hash := cur_hash hdr in
  let txns := txn_records hdr in

  success <- check_hash log cur_hash;

  l <- if success then
    decrypt_txns txns log
  else
    let old_count := old_count hdr in
    let old_txn_count := old_txn_count hdr in
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    decrypt_txns old_txns old_log;
  Ret l.

Definition recover := read_log.

(** Representation Invariants **)

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

Definition txn_valid (tx: txn) (log_blocks: list value) (kl: list key) (em: encryptionmap) :=
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
  encryption_present (txa++txd) tk em.

Fixpoint txns_valid (txns: list txn) (log_blocks: list value) (kl: list key) (em: encryptionmap):=
  match txns with
    | tx::txns' =>
      txn_valid tx log_blocks kl em /\ txns_valid txns' log_blocks kl em
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

Open Scope predicate_scope.

Definition log_rep_inner
           (log_state: Log_State)
           (hdr: header) (txns: list txn)
           (hdr_blockset: set value) (log_blocksets: list (set value))
           (state: state CryptoDiskLang) :=
  let crypto_maps := fst state in
  let disk := snd state in
  let key_list := fst (fst crypto_maps) in
  let encryption_map := snd (fst crypto_maps) in
  let hash_map := snd crypto_maps in
  let log_blocks := map fst log_blocksets in
  let valid_hdr := get_valid_part hdr log_blocks in
  let valid_log_blocks := firstn (count valid_hdr) log_blocks in  
    (* Header *)
    disk hdr_block_num = Some hdr_blockset /\
    (* Log Blocks *)
    (forall i, i < length log_blocksets -> disk (log_start + i) = selNopt log_blocksets i) /\
    hdr = decode_header (fst hdr_blockset) /\
    (** Sync status **)
    match log_state with
    | Synced =>
      snd hdr_blockset = [] /\
      (forall ls, In ls log_blocksets -> snd ls = [])
    | Not_Synced =>
      (exists v, snd hdr_blockset = v :: nil) /\
      (forall ls, In ls log_blocksets -> exists v, snd ls = v :: nil)
    end
    /\
    (* log length is valid *)
    length log_blocksets = log_length /\
    (* txns represents the right thing *)
    map record txns = records valid_hdr /\
    (* Header hashes is correct *)
    hash_valid valid_log_blocks (hash valid_hdr) /\
    hashes_in_hashmap hash_map hash0 valid_log_blocks /\
    (* Header current txn_records are valid *)
    txns_valid txns valid_log_blocks key_list encryption_map.

Definition log_rep (log_state: Log_State) (hdr: header) (txns: list txn) (state: state CryptoDiskLang) :=
  exists (hdr_blockset: set value) (log_blocksets: list (set value)),
    log_rep_inner log_state hdr txns hdr_blockset log_blocksets state.

Hint Extern 0 (okToUnify (log_rep_inner _ _ ?b _) (log_rep_inner _ _ ?b  _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (log_rep ?txns _) (log_rep ?txns _)) => constructor : okToUnify.

(*
Theorem sp_read_header:
  forall  log_state hdr txns hdr_blockset log_blocksets F t s',
  strongest_postcondition CryptoDiskLang read_header
      (fun o s => (F * log_rep_inner log_state hdr txns hdr_blockset log_blocksets (fst s)) (snd s)) t s' ->
  t = hdr /\ (F * log_rep_inner log_state hdr txns hdr_blockset log_blocksets (fst s'))%predicate (snd s').
Proof.
  unfold log_rep_inner; simpl; intros.
  cleanup_no_match.
  destruct_lifts; cleanup_no_match.
  apply sep_star_assoc in H.
  apply sep_star_comm in H.
  apply sep_star_assoc in H.
  eapply_fresh ptsto_valid in H; cleanup_no_match.
  repeat split; eauto.
  pred_apply; cancel.
Qed.
 *)

Set Nested Proofs Allowed.
  Lemma map_ext_eq:
    forall A B (l1 l2: list A) (f: A -> B),
      map f l1 = map f l2 ->
      (forall a a', f a = f a' -> a = a') ->
      l1 = l2.
  Proof.
    induction l1; simpl; intros;
    destruct l2; simpl in *; cleanup; try congruence; eauto.
    erewrite (H0 a a0), IHl1; eauto.
  Qed.

Theorem apply_txn_finished:
  forall txn log_blocks plain_blocks t s' s o,
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
  txn_blocks = map (encrypt key) plain_blocks ->
  length addr_list = length data_blocks ->
  exec CryptoDiskLang o s (apply_txn txn log_blocks) (Finished s' t) ->
  fst s' = fst s /\ snd s' = upd_batch_set (snd s) addr_list data_blocks.
Proof.
  unfold apply_txn, decrypt_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.

  eapply decrypt_all_finished in H1; cleanup.
  eapply map_ext_eq in H3; cleanup; eauto.
  eapply write_batch_finished in H2; eauto; cleanup.
  intuition eauto; cleanup.
  intros.
  eapply encrypt_ext; eauto.
Qed.

Definition to_plain_addr_list txn plain_addr_blocks :=
  let data_count := data_count txn in          

  firstn data_count (blocks_to_addr_list plain_addr_blocks).

Definition get_addr_blocks (log_blocks: list value) (txn: txn_record) :=
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in

  firstn addr_count txn_blocks.

Definition get_addr_list txn plain_addr_blocks :=
  firstn (data_count txn) (blocks_to_addr_list plain_addr_blocks).

Definition get_data_blocks (log_blocks: list value) (txn: txn_record) :=
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in

  skipn addr_count txn_blocks.

Definition plain_addr_blocks_valid log_blocks plain_addr_blocks txn :=
  let key := txn_key txn in
  
  get_addr_blocks log_blocks txn = map (encrypt key) plain_addr_blocks.

Definition plain_data_blocks_valid log_blocks plain_data_blocks txn :=
  let key := txn_key txn in
  
  get_data_blocks log_blocks txn = map (encrypt key) plain_data_blocks.


Theorem apply_txns_finished:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t,
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    
    exec CryptoDiskLang o s (apply_txns txns log_blocks) (Finished s' t) ->
    fst s' = fst s /\
    snd s' = list_upd_batch_set (snd s) l_addr_list l_plain_data_blocks.
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0; inversion H1; cleanup.
  
  assume (Al: (length l = addr_count a)).

  eapply apply_txn_finished in H2; cleanup; eauto.
  edestruct IHtxns in H3; eauto; cleanup.
  simpl in *; intuition eauto.
  unfold get_addr_list at 1; simpl.

  2:{
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    rewrite firstn_firstn in H7;
    rewrite min_l in H7 by lia.
    rewrite H7.
    rewrite skipn_firstn_comm in H13.
    rewrite H13, <- map_app; eauto.
  }
  
  rewrite <- Al in H6.
  setoid_rewrite H6.  
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  Unshelve.
  unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
  erewrite <- map_length, <- H7.
  rewrite firstn_length_l; eauto.
  rewrite firstn_length_l; try lia.
  rewrite skipn_length; try lia.
  (** TODO: Make a premise **)
  admit.
Admitted.
    
Global Opaque apply_txns.

Theorem decrypt_txn_finished:
  forall txn log_blocks plain_blocks t s' s o,
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
  txn_blocks = map (encrypt key) plain_blocks ->
  length addr_list = length data_blocks ->
  exec CryptoDiskLang o s (decrypt_txn txn log_blocks) (Finished s' t) ->
  t = (addr_list, data_blocks) /\ s' = s.
Proof.
  unfold decrypt_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.

  eapply decrypt_all_finished in H1; cleanup.
  eapply map_ext_eq in H2; cleanup; eauto.
  eapply encrypt_ext; eauto.
Qed.



Theorem decrypt_txns_finished:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t,
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    
    exec CryptoDiskLang o s (decrypt_txns txns log_blocks) (Finished s' t) ->
    t = combine l_addr_list l_plain_data_blocks /\
    s' = s.
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0; inversion H1; cleanup.
  
  assume (Al: (length l = addr_count a)).

  eapply decrypt_txn_finished in H2; cleanup; eauto.
  edestruct IHtxns in H3; eauto; cleanup.
  simpl in *; intuition eauto.
  unfold get_addr_list at 1; simpl.

  2:{
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    rewrite firstn_firstn in H7;
    rewrite min_l in H7 by lia.
    rewrite H7.
    rewrite skipn_firstn_comm in H13.
    rewrite H13, <- map_app; eauto.
  }
  
  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  Unshelve.
  unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
  erewrite <- map_length, <- H7.
  rewrite firstn_length_l; eauto.
  rewrite firstn_length_l; try lia.
  rewrite skipn_length; try lia.
  (** TODO: Make a premise **)
  admit.
Admitted.

(*
Definition get_addr_list_direct txn :=
  let rec := record txn in
  let addr_list_length := data_count rec in
  firstn addr_list_length (blocks_to_addr_list (addr_blocks txn)).
  
  Lemma sync_upd_comm:
    forall A AEQ V (m: @mem A AEQ (V * list V)) a vs,
      sync (upd m a vs) = upd (sync m) a (fst vs, nil).
  Proof.
    intros.
    extensionality x.
    unfold sync.
    destruct (AEQ a x); subst;
    [repeat rewrite upd_eq
    |repeat rewrite upd_ne]; eauto.
  Qed.

Theorem sp_flush_txns:
  forall txns full_txns log_blocks log_blocksets hdr_blockset F t s' log_state hdr vsl,
    let full_addr_list := flat_map get_addr_list_direct full_txns in
    let dedup_addr_list := dedup_last addr_dec full_addr_list in
    let dedup_plain_data := dedup_by_list addr_dec full_addr_list (flat_map data_blocks full_txns) in
    length vsl = length dedup_addr_list ->
    txns = map record full_txns ->
    log_blocks = map fst log_blocksets ->
  strongest_postcondition CryptoDiskLang (flush_txns txns log_blocks)
    (fun o s =>  (F * log_rep_inner log_state hdr full_txns hdr_blockset log_blocksets (fst s) *
               dedup_addr_list |L> vsl)%predicate (snd s)) t s' ->
  exists header_blockset' log_blocksets',
    (F * log_rep_inner Synced header0 [] header_blockset' log_blocksets' (fst s') *
     dedup_addr_list |L> map (fun v => (v, nil)) dedup_plain_data)%predicate (snd s').

Proof.
  simpl; intros; cleanup.
  eapply sp_impl in H2.
  
  eapply sp_apply_txns
   in H2; simpl in *;
  cleanup.

  do 2 eexists.

  

  rewrite sync_upd_comm; simpl.
  unfold log_rep_inner.
  eapply pimpl_trans.
  3: eapply ptsto_upd.
  eauto.

  (** TODO: Solve this **)
  admit.
  admit.
Admitted.

Global Opaque flush_txns.

Theorem sp_check_and_flush:
  forall txns full_txns log_blocks log_blocksets hdr_blockset F t s' log_state hdr vsl hash,
    let full_addr_list := flat_map get_addr_list_direct full_txns in
    let dedup_addr_list := dedup_last addr_dec full_addr_list in
    let dedup_plain_data := dedup_by_list addr_dec full_addr_list (flat_map data_blocks full_txns) in
    length vsl = length dedup_addr_list ->
    txns = map record full_txns ->
    log_blocks = map fst log_blocksets ->
  strongest_postcondition CryptoDiskLang (check_and_flush txns log_blocks hash)
     (fun o s =>  (F *
      log_rep_inner log_state hdr full_txns hdr_blockset log_blocksets (fst s) *
      dedup_addr_list |L> vsl)%predicate (snd s)) t s' ->
  (t = true /\
   hash = rolling_hash hash0 log_blocks /\
  exists header_blockset' log_blocksets',
    (F * log_rep_inner Synced header0 [] header_blockset' log_blocksets' (fst s') *
     dedup_addr_list |L> map (fun v => (v, nil)) dedup_plain_data)%predicate (snd s')) \/
  (t = false /\
  hash <> rolling_hash hash0 log_blocks /\
   (F * log_rep_inner log_state hdr full_txns hdr_blockset log_blocksets (fst s') *
     dedup_addr_list |L> vsl)%predicate (snd s')
  ).

Proof.

 simpl; intros; cleanup.
 destruct (hash_dec x hash0); simpl in *; cleanup.
 {
   left.
   apply sp_extract_precondition in H0; cleanup.

   eapply sp_impl in H1.
   apply sp_hash_all in H1; eauto.
   cleanup.
   
   eapply sp_impl in H0.
   apply sp_flush_txns in H0; eauto.

   simpl; intros.
   eapply sp_impl in H1.
   apply sp_hash_all in H1; eauto.
   cleanup.
   apply H4.
   simpl; intros.
   split; eauto.

   (** TODO: Need to fix sp_hash_all **)
   admit.
   admit.

   simpl; intros.
   split; eauto.
   
   (** TODO: Need to fix sp_hash_all **)
   admit.
   admit.
 }
 {
   right; repeat split; eauto.
   eapply sp_impl in H0.
   apply sp_hash_all in H0; eauto.
   cleanup; eauto.
   simpl; intros; eauto.

   
   split; eauto.
    (** TODO: Need to fix sp_hash_all **)
   admit.
   admit.

   eapply sp_impl in H0.
   apply sp_hash_all in H0; eauto.
   cleanup; eauto.
   simpl; intros; eauto.

   split; eauto.

   (** TODO: Need to fix sp_hash_all **)
   admit.
   admit.
 }
 Unshelve.
 all: eauto.
 all: exact (fst s').
Admitted.

*)
