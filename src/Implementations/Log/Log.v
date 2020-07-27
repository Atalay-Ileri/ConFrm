Require Import EquivDec Framework CryptoDiskLayer BatchOperations.
Require Import Datatypes PeanoNat.
Require Import Omega Sumbool.
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
  _ <- |DO| Sync;
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
    Ret tt
  else
    let old_txns := firstn old_txn_count txns in
    let old_log := firstn old_count log in
    success <- check_and_flush old_txns old_log old_hash;
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

Theorem sp_apply_txn:
  forall  F t s' txn log_blocks plain_blocks vsl x,
  let key := txn_key txn in
  let start := txn_start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
  let addr_blocks := firstn addr_count plain_blocks in
  let data_blocks := skipn addr_count plain_blocks in
  let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
  txn_blocks = map (encrypt key) plain_blocks ->
  length vsl = length data_blocks ->
  length addr_list = length data_blocks ->
  strongest_postcondition CryptoDiskLang (apply_txn txn log_blocks)
      (fun o s => fst s = x /\ (F * addr_list |L> vsl)%predicate (snd s)) t s' ->
  fst s' = x /\ (F * addr_list |L> write_all_to_set data_blocks vsl)%predicate (snd s').
Proof.
  simpl; intros.
  cleanup.
  eapply sp_impl in H2.
  2:{
    
    simpl; intros.
    cleanup.
    
    eapply sp_impl in H3.
    apply sp_decrypt_all with (F:= fun s => fst s = x /\ (F * firstn (data_count txn0) (blocks_to_addr_list (firstn (addr_count txn0) plain_blocks)) |L> vsl)%predicate
   (snd s)) in H3.
    instantiate (1:= fun o s => exists plain_blocks0 : list value,
                               (F * firstn (data_count txn0) (blocks_to_addr_list (firstn (addr_count txn0) plain_blocks)) |L> vsl)%predicate
         (snd s) /\
  
         x0 = plain_blocks0 /\
         map (encrypt (txn_key txn0)) plain_blocks = map (encrypt (txn_key txn0)) plain_blocks0 /\ fst s = x).
    simpl; cleanup; eauto.
    simpl in *; intros; cleanup; eauto.
  }
  apply sp_exists_extract in H2; cleanup.
  apply sp_extract_precondition in H2; cleanup.
  apply map_ext_eq in H5; eauto; cleanup.

  eapply sp_impl in H2.
  eapply sp_write_batch in H2; eauto.

  simpl; intros; cleanup; intuition eauto.
  apply encrypt_ext.
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

Fixpoint bimap {A B C} (f: A -> B -> C) (la: list A) (lb: list B): list C :=
  match la, lb with
  | a::la, b::lb => (f a b)::(bimap f la lb)
  | _, _ => nil
  end.

Fixpoint flat_bimap {A B C} (f: A -> B -> list C) (la: list A) (lb: list B): list C :=
  match la, lb with
  | a::la, b::lb => (f a b)++(flat_bimap f la lb)
  | _, _ => nil
  end.

Lemma ptsto_list_app_split:
  forall V (l1 l2: list addr) (lv1 lv2: list V),
    length l1 = length lv1 ->
    l1 |L> lv1 * l2 |L> lv2 =*=> (l1++l2) |L> (lv1 ++ lv2).
Proof.
  induction l1; simpl; intros; cleanup; cancel.
  destruct lv1; simpl in *; try omega.
  cancel; eauto.
Qed.


  Lemma write_all_to_set_length:
    forall V (l1: list V) l2,
      length (write_all_to_set l1 l2) = min (length l1) (length l2).
  Proof.
    induction l1; simpl; intros; eauto.
    destruct l2; simpl; eauto.
  Qed.

  Global Opaque apply_txn.
    
Theorem sp_apply_txns:
  forall txns F t s' log_blocks plain_addr_blocks_list plain_data_blocks_list vsl x,
    Forall2 (plain_addr_blocks_valid log_blocks) plain_addr_blocks_list txns ->
    Forall2 (plain_data_blocks_valid log_blocks) plain_data_blocks_list txns ->
    Forall2 (fun txn plain_addr_blocks => length (get_data_blocks log_blocks txn) = length (firstn (data_count txn) (blocks_to_addr_list plain_addr_blocks))) txns plain_addr_blocks_list ->
    let full_addr_list := flat_bimap get_addr_list txns plain_addr_blocks_list in
    let dedup_addr_list := dedup_last addr_dec full_addr_list in
    let dedup_plain_data := dedup_by_list addr_dec full_addr_list (List.concat plain_data_blocks_list) in
    length vsl = length dedup_addr_list ->
  strongest_postcondition CryptoDiskLang (apply_txns txns log_blocks)
    (fun o s => fst s = x /\
        (F * dedup_addr_list |L> vsl)%predicate (snd s)) t s' ->
  fst s' = x /\ (F * dedup_addr_list |L> write_all_to_set dedup_plain_data vsl)%predicate (snd s').
Proof.
  induction txns; simpl; intros; eauto.
  {
    match goal with
    |[H: Forall2 _ _ _ |- _ ] =>
     apply forall2_length in H
    end; simpl in *; cleanup; eauto.
  }
  {
    cleanup;
    try solve[
    match goal with
    |[H: Forall2 _ _ _ |- _ ] =>
     eapply_fresh forall2_length in H;
     simpl in *; omega
    end].
    destruct plain_data_blocks_list;
    try solve[
    match goal with
    |[H: Forall2 _ _ _ |- _ ] =>
     eapply_fresh forall2_length in H;
     simpl in *; omega
    end].
    
    repeat
    match goal with
    |[H: Forall2 _ (_ :: _) (_ :: _) |- _ ] =>
     inversion H; cleanup; clear H
    end.
    specialize IHtxns with (1:=H11)(2:=H10)(3:=H9).   
    rewrite dedup_last_app.
    eapply sp_impl in H3.
    apply IHtxns in H3.

    cleanup; eauto.
    split; eauto.

    erewrite <- firstn_skipn with (n:= length (filter (fun a0 : addr => negb (in_dec_b addr_dec a0 (flat_bimap get_addr_list txns l0)))
      (dedup_last addr_dec (get_addr_list a l))))(l:= write_all_to_set
         (dedup_by_list addr_dec (get_addr_list a l ++ flat_bimap get_addr_list txns l0)
                        (List.concat (l1 :: plain_data_blocks_list))) vsl).

    pred_apply' H0.
    setoid_rewrite <- ptsto_list_app_split with (l2:=  dedup_last addr_dec (flat_bimap get_addr_list txns l0)).

    erewrite <- eq_pimpl with (a:= dedup_last addr_dec (flat_bimap get_addr_list txns l0)
                              |L> _) (b:=  dedup_last addr_dec (flat_bimap get_addr_list txns l0)
   |L> skipn
         (length
            (filter (fun a0 : addr => negb (in_dec_b addr_dec a0 (flat_bimap get_addr_list txns l0)))
               (dedup_last addr_dec (get_addr_list a l))))
         (write_all_to_set
            (dedup_by_list addr_dec (get_addr_list a l ++ flat_bimap get_addr_list txns l0)
                           (List.concat (l1 :: plain_data_blocks_list))) vsl)).

    rewrite <- sep_star_assoc.
    apply pimpl_refl.

    (** TODO: Solve this **)
    admit.

    rewrite firstn_length_l; eauto.
    eapply le_trans.    
    apply filter_length.
          
    rewrite write_all_to_set_length.
    rewrite min_l.
    
    eapply le_trans; [>apply dedup_last_app_length|].
    rewrite dedup_last_app_length_comm.
    rewrite <- dedup_last_dedup_by_list_length_le; eauto.

    (** TODO: Solve this **)
    admit.

    setoid_rewrite H2.
    erewrite dedup_last_dedup_by_list_length_le; eauto.

     (** TODO: Solve this **)
    admit.

    rewrite dedup_last_app, app_length in H2.
    
    instantiate (1:= skipn (length
         (filter (fun a : addr => negb (in_dec_b addr_dec a (flat_bimap get_addr_list txns l0)))
                 (dedup_last addr_dec (get_addr_list a l)))) vsl).
    rewrite skipn_length.
    rewrite H2; omega.

    simpl; intros.

    eapply sp_impl in H.
    apply sp_apply_txn in H.
    cleanup; split; eauto.
    
    (** TODO: Solve this **)
    admit.

    erewrite map_app.
    unfold plain_addr_blocks_valid, plain_data_blocks_valid in *.
    rewrite <- H5.
    rewrite <- H6.
    unfold get_addr_blocks, get_data_blocks.
    rewrite firstn_skipn; eauto.

    (** TODO: Solve this **)
    rewrite skipn_app_eq.
    admit.
    
    unfold plain_addr_blocks_valid in *.
    erewrite <- map_length.
    rewrite <- H5.
    unfold get_addr_blocks.
    apply firstn_length_l.
    rewrite firstn_length_l; try omega.
    rewrite skipn_length.
    (** TODO: Solve this **)
    admit.

    rewrite firstn_app_l.
    rewrite skipn_app_eq.
    rewrite firstn_length_l.
    
    unfold plain_data_blocks_valid in *.
    erewrite <- map_length.
    rewrite <- H6.
    unfold get_data_blocks in *.
    rewrite skipn_length.
    rewrite firstn_length_l; try omega.
    rewrite skipn_length.
    (** TODO: Solve this **)
    admit.
    admit.

    unfold plain_addr_blocks_valid in *.
    erewrite <- map_length.
    rewrite <- H5.
    unfold get_addr_blocks.
    apply firstn_length_l.
    rewrite firstn_length_l; try omega.
    rewrite skipn_length.
    (** TODO: Solve this **)
    admit.

    unfold plain_addr_blocks_valid in *.
    erewrite <- map_length.
    rewrite <- H5.
    unfold get_addr_blocks.
    rewrite firstn_length_l; try omega.
    rewrite firstn_length_l; try omega.
    rewrite skipn_length.
    (** TODO: Solve this **)
    admit.


    simpl; intros; cleanup.
    split; eauto.
    pred_apply.
    rewrite firstn_app_l.
    (** TODO: Solve this **)
    admit.

    unfold plain_addr_blocks_valid in *.
    erewrite <- map_length.
    rewrite <- H5.
    unfold get_addr_blocks.
    rewrite firstn_length_l; try omega.
    rewrite firstn_length_l; try omega.
    rewrite skipn_length.
    (** TODO: Solve this **)
    admit.

    Unshelve.
    all: eauto.
Admitted.

Global Opaque apply_txns.

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

