Require Import EquivDec Framework TotalMem CryptoDiskLayer BatchOperations.
Require Import Log.Log Log.RepImplications.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Nested Proofs Allowed.
(*** Lemmas ***)

Lemma subset_consistent_upd:
  forall A AEQ V l_a l_v (m m' : @mem A AEQ V) ,
    consistent_with_upds m l_a l_v ->
    subset (Mem.upd_batch m l_a l_v) m' ->
    subset m m'.
Proof.
  induction l_a; simpl; intros; cleanup; eauto.
  unfold consistent in *.
  eapply IHl_a in H0; eauto.
  unfold subset in *; intros.
  specialize (H0 a0); cleanup.
  split; intros.

  apply H0 in H3.
  destruct (AEQ a a0); subst.
  rewrite Mem.upd_eq in H3; eauto; congruence.
  rewrite Mem.upd_ne in H3; eauto.
  apply H2.
  destruct (AEQ a a0); subst.
  rewrite Mem.upd_eq; eauto;
  split_ors; congruence.
  rewrite Mem.upd_ne; eauto.
Qed.

Lemma seln_seq:
  forall len start n def,
    n < len ->
    seln (seq start len) n def = (start + n).
Proof.
  induction len; simpl; intuition eauto.
  lia.
  destruct n; eauto.
  rewrite IHlen; lia.
Qed.

Lemma upd_batch_consistent_some:
  forall A AEQ V l_a l_v (m: @mem A AEQ V) a v,
    consistent_with_upds m l_a l_v ->
    m a = Some v ->
    Mem.upd_batch m l_a l_v a = Some v.
Proof.
  induction l_a; simpl; intros; cleanup; eauto.
  unfold consistent in *.
  eapply IHl_a; eauto.
  
  destruct (AEQ a a0); subst.
  rewrite Mem.upd_eq; eauto;
  split_ors; congruence.
  rewrite Mem.upd_ne; eauto.
Qed.

Lemma records_are_consecutive_starting_from_app_one:
forall l1 n r,
records_are_consecutive_starting_from n l1 ->
start r = fold_left Nat.add 
(map (fun rec => addr_count rec + data_count rec) l1) n ->
records_are_consecutive_starting_from n (l1 ++ [r]). 
Proof.
  induction l1; simpl; intros; eauto.
  cleanup; split; eauto.
  eapply IHl1; eauto.
  rewrite <- Nat.add_assoc; eauto.
Qed.

Lemma consistent_with_upds_app:
forall A AEQ V l_a1 l_a2 l_v1 l_v2 (m: @mem A AEQ V),
consistent_with_upds m (l_a1++l_a2) (l_v1++l_v2) ->
length l_a1 = length l_v1 ->
length l_a2 = length l_v2 ->
consistent_with_upds m l_a1 l_v1 /\
consistent_with_upds (Mem.upd_batch m l_a1 l_v1) l_a2 l_v2.
Proof.
induction l_a1; simpl; intros; eauto;
destruct l_v1; simpl in *; try lia; eauto.
cleanup.
apply IHl_a1 in H2; cleanup.
intuition eauto.
all: lia.
Qed.

Lemma consistent_with_upds_upd_batch_swap:
forall A AEQ V l_a1 l_a2 l_v1 l_v2 (m: @mem A AEQ V),
consistent_with_upds m (l_a1++l_a2) (l_v1++l_v2) ->
length l_a1 = length l_v1 ->
length l_a2 = length l_v2 ->
Mem.upd_batch (Mem.upd_batch m l_a1 l_v1) l_a2 l_v2 =
Mem.upd_batch (Mem.upd_batch m l_a2 l_v2) l_a1 l_v1.
Proof.
  induction l_a1; simpl; intros; eauto.
  destruct l_v1; simpl in *; try lia.
  cleanup.
  rewrite IHl_a1; eauto.
  extensionality x.
  destruct (in_dec AEQ x l_a1).
  {
    eapply_fresh (in_split_last AEQ) in i; cleanup.
    edestruct nth_split with (l:= l_v1) (n:= length x0).
    rewrite app_length in *; simpl in *; lia.
    logic_clean.
    rewrite H3 in *.
    repeat rewrite Mem.upd_batch_app; eauto; simpl.
    repeat rewrite Mem.upd_batch_ne; eauto.
    repeat rewrite Mem.upd_eq; eauto.
  }
  {
        
apply consistent_with_upds_app in H2; eauto; logic_clean.
    repeat rewrite Mem.upd_batch_ne with (l_a := l_a1); eauto.
    destruct (in_dec AEQ x l_a2).
    {
      destruct (AEQ x a); subst.
      {
        rewrite Mem.upd_eq; eauto.
        erewrite <- upd_batch_consistent_some.
        2: apply H3.
        2: rewrite Mem.upd_batch_ne; eauto;
        apply Mem.upd_eq; eauto.
        
      eapply_fresh (in_split_last AEQ) in i; cleanup.
      edestruct nth_split with (l:= l_v2) (n:= length x).
    rewrite app_length in *; simpl in *; lia.
    logic_clean.
    rewrite H4 in *.
    repeat rewrite Mem.upd_batch_app; eauto; simpl.
    repeat rewrite Mem.upd_batch_ne; eauto.
    repeat rewrite Mem.upd_eq; eauto.
    }
    {
      rewrite Mem.upd_ne; eauto.
      eapply_fresh (in_split_last AEQ) in i; cleanup.
      edestruct nth_split with (l:= l_v2) (n:= length x0).
    rewrite app_length in *; simpl in *; lia.
    logic_clean.
    rewrite H4 in *.
    repeat rewrite Mem.upd_batch_app; eauto; simpl.
    repeat rewrite Mem.upd_batch_ne; eauto.
    repeat rewrite Mem.upd_eq; eauto.
    }
    }
    {
      repeat rewrite Mem.upd_batch_ne with (l_a := l_a2); eauto.
      destruct (AEQ a x); subst.
      repeat rewrite Mem.upd_eq; eauto.
      repeat rewrite Mem.upd_ne; eauto.
      repeat rewrite Mem.upd_batch_ne with (l_a := l_a2); eauto.
    }
  }  
  Unshelve.
  all: eauto.
Qed.

Lemma hashes_in_hashmap_app:
forall hl1 hl2 hm h,
hashes_in_hashmap hm h hl1 ->
hashes_in_hashmap hm (rolling_hash h hl1) hl2 ->
hashes_in_hashmap hm h (hl1 ++ hl2).
Proof.
  induction hl1; simpl; intros; eauto.
  cleanup; split; eauto.
Qed.

Lemma hashes_in_hashmap_upd:
forall l hm h,
let hash_list := (rolling_hash_list h l) in
consistent_with_upds hm hash_list (combine (h::hash_list) l) ->
hashes_in_hashmap (Mem.upd_batch hm hash_list (combine (h::hash_list) l)) h l.
Proof.
  induction l.
  intros; simpl; eauto.
  intros.
  simpl consistent_with_upds in *.
  cleanup_no_match; simpl in *; eauto.
  split; eauto.
  eapply upd_batch_consistent_some; eauto.
  apply Mem.upd_eq; eauto.
Qed.

(*** Specs **)
Theorem init_finished:
  forall s' s o t u l_av,
    let l_a := map fst l_av in
    let l_v := map snd l_av in
    (forall a, In a l_a -> a >= data_start) ->
    exec CryptoDiskLang u o s (init l_av) (Finished s' t) ->
    log_rep [] s' /\
    snd s' = sync (upd_batch_set (upd_set (snd s) 
    hdr_block_num (encode_header header0)) l_a l_v) /\
    (forall a, snd (snd s' a) = []).
Proof.
  unfold init, write_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  eapply write_batch_finished in H0; simpl in *; eauto; cleanup.
  unfold upd_set; intuition eauto.
  unfold log_rep, log_rep_general, log_rep_explicit.
  do 3 eexists; intuition eauto.
  {
    unfold log_header_block_rep; simpl; eauto.
  }
  {
    unfold log_data_blocks_rep; simpl; intuition eauto.
    instantiate (1:= map (fun a => (fst (snd s a), [])) (seq log_start log_length)).
    rewrite sync_upd_batch_set_comm.
    rewrite upd_batch_ne.
    unfold sync; simpl.
    rewrite upd_ne; eauto.
    erewrite seln_map; eauto.
    erewrite seln_seq; eauto.
    all: try rewrite map_length, seq_length in *; eauto.

    intros Hx.
    apply H in Hx.
    pose proof data_start_where_log_ends.
    lia.
    apply in_map_iff in H3; cleanup; eauto.
  }
  {
    try rewrite map_length, seq_length in *; eauto.
  }
  {
    rewrite sync_upd_batch_set_comm.
    rewrite upd_batch_ne.
    unfold sync; simpl.
    rewrite upd_eq; simpl; eauto.
    rewrite encode_decode_header; simpl; eauto.
    lia.
    intros Hx.
    apply H in Hx.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
  }
  {
    rewrite sync_upd_batch_set_comm.
    rewrite upd_batch_ne.
    unfold sync; simpl.
    rewrite upd_eq; simpl; eauto.
    rewrite encode_decode_header; simpl; eauto.
    lia.
    intros Hx.
    apply H in Hx.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
  }
  {
    rewrite sync_upd_batch_set_comm.
    rewrite upd_batch_ne.
    unfold sync; simpl.
    rewrite upd_eq; simpl; eauto.
    rewrite encode_decode_header; simpl; eauto.
    unfold log_rep_inner; simpl; split.
    apply header_part0_valid.
    apply txns_valid_nil.
    intros Hx.
    apply H in Hx.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
  }
  repeat rewrite map_length; eauto.
  
  Unshelve.
  eauto.
Qed.

Theorem update_header_finished_oracle:
  forall header_part vs s' s o t u,
    (snd s) hdr_block_num = vs ->
    exec CryptoDiskLang u o s (update_header header_part) (Finished s' t) ->
    fst s' = fst s /\
    snd s' = upd (snd s) hdr_block_num (encode_header (update_hdr (decode_header (fst vs)) header_part), fst vs :: snd vs) /\
    o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont);
 LayerImplementation.Cont
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size)));
 OpToken CryptoDiskOperation
   (Token2 CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size))
      DiskLayer.Cont)].
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  cleanup; eauto.
Qed.

Theorem update_header_crashed_oracle:
  forall header_part s' s o u,
    exec CryptoDiskLang u o s (update_header header_part) (Crashed s') ->
    s' = s /\ 
    (o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Crash)] \/
    o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)] ++
 [LayerImplementation.Crash
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))] \/
    o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)] ++
 [LayerImplementation.Cont
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))] ++
[OpToken CryptoDiskOperation
   (Token2 CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size))
      DiskLayer.Crash)]).
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  repeat (split_ors; repeat invert_exec; simpl in *;
          cleanup; simpl in *);
  repeat invert_exec;
  try solve [ destruct s; simpl in *; intuition eauto; lia].
Qed.

Theorem update_header_finished:
  forall header_part vs s' s o t u,
    (snd s) hdr_block_num = vs ->
    exec CryptoDiskLang u o s (update_header header_part) (Finished s' t) ->
    fst s' = fst s /\
    snd s' = upd (snd s) hdr_block_num (encode_header (update_hdr (decode_header (fst vs)) header_part), fst vs :: snd vs).
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  cleanup; eauto.
Qed.

Theorem update_header_crashed:
  forall header_part s' s o u,
    exec CryptoDiskLang u o s (update_header header_part) (Crashed s') ->
    s' = s.
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  repeat (split_ors; repeat invert_exec; simpl in *;
          cleanup; simpl in *);
  repeat invert_exec;
  solve [ destruct s; simpl in *; eauto].
Qed.

Theorem decrypt_txn_finished_oracle:
  forall txn_record log_blocks t s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (decrypt_txn txn_record log_blocks) (Finished s' t) ->
    t = (addr_list, data_blocks) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
    snd s' = snd s /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
    o = rec_oracle_finished_crypto (length txn_blocks) ++
  [LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size)))].
Proof.
  unfold decrypt_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.

  eapply decrypt_all_finished_oracle in H0; cleanup.
  repeat rewrite map_map; eauto.
  simpl; intuition eauto.
  setoid_rewrite H3.
  setoid_rewrite map_ext at 2; eauto.
  rewrite map_id; eauto.
  intros; simpl; apply decrypt_encrypt.
  
  setoid_rewrite map_ext at 1; eauto.
  rewrite map_id; eauto.
  intros; simpl; apply decrypt_encrypt.
Qed.


Theorem decrypt_txn_finished:
  forall txn_record log_blocks t s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (decrypt_txn txn_record log_blocks) (Finished s' t) ->
    t = (addr_list, data_blocks) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
    snd s' = snd s /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks).
Proof.
  intros.
  eapply decrypt_txn_finished_oracle in H0; eauto.
  cleanup; intuition eauto.
Qed.

Theorem decrypt_txn_crashed_oracle:
  forall txn_record log_blocks s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    
    exec CryptoDiskLang u o s (decrypt_txn txn_record log_blocks) (Crashed s') ->
    exists n,
      fst (fst s') = fst (fst s) /\
      snd (fst s') =
      Mem.upd_batch (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))) /\
      snd s' = snd s /\
      consistent_with_upds (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))) /\
      (batch_operations_crypto_crashed_oracle_is o n (length txn_blocks) \/
      o = rec_oracle_finished_crypto (length txn_blocks) ++
    [LayerImplementation.Crash
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]).
Proof.
  unfold decrypt_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  split_ors; cleanup; repeat invert_exec.
  {
    eapply decrypt_all_crashed_oracle in H; cleanup; eauto.
    repeat rewrite map_map; eauto.
    setoid_rewrite map_ext with (g:= fun x => x) at 1; eauto.
    erewrite map_id; eauto.
    setoid_rewrite map_ext with (g:= fun x => x) at 1; eauto.
    rewrite map_id; eauto.
    eexists; intuition eauto.
    intros; simpl; apply decrypt_encrypt.  
    intros; simpl; apply decrypt_encrypt.  
  }
  {
    eapply decrypt_all_finished_oracle in H0; cleanup; eauto.
    repeat rewrite map_map; eauto.
    setoid_rewrite map_ext with (g:= fun x => x) at 1; eauto.
    rewrite map_id; eauto.
    setoid_rewrite map_ext with (g:= fun x => x) at 1; eauto.
    rewrite map_id; eauto.
    exists (addr_count txn_record + data_count txn_record).
    rewrite firstn_oob; try lia.
    setoid_rewrite firstn_oob at 2.
    repeat rewrite app_length; simpl.
    intuition eauto; try lia.
    rewrite firstn_map_comm.
    rewrite firstn_firstn, Nat.min_id; eauto.

    rewrite map_length, firstn_length; lia.
    rewrite firstn_length; lia.
    intros; simpl; apply decrypt_encrypt.
    intros; simpl; apply decrypt_encrypt.
  }
Qed.


Theorem decrypt_txn_crashed:
  forall txn_record log_blocks s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    
    exec CryptoDiskLang u o s (decrypt_txn txn_record log_blocks) (Crashed s') ->
    exists n,
      fst (fst s') = fst (fst s) /\
      snd (fst s') =
      Mem.upd_batch (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))) /\
      snd s' = snd s /\
      consistent_with_upds (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))).
Proof.
  intros.
  eapply decrypt_txn_crashed_oracle in H; eauto.
  cleanup; intuition eauto.
Qed.

Definition apply_txn_finished_oracle_is  length_txn_blocks length_data_blocks := 
  rec_oracle_finished_crypto (length_txn_blocks) ++
[LayerImplementation.Cont
   (HorizontalComposition CryptoOperation 
   (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))] ++
rec_oracle_finished_disk (length_data_blocks).

Theorem apply_txn_finished_oracle:
  forall txn_record log_blocks t s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
   
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (apply_txn txn_record log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
    snd s' = upd_batch_set (snd s) addr_list data_blocks /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks)/\
    o = apply_txn_finished_oracle_is (length txn_blocks) (length data_blocks).
Proof.
  unfold apply_txn, apply_txn_finished_oracle_is; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.
  eapply decrypt_txn_finished_oracle in H0; eauto; cleanup; simpl in *.  
  eapply write_batch_finished_oracle in H1; eauto; cleanup.
  repeat cleanup_pairs.
  intuition eauto; cleanup.
  rewrite <- app_assoc; eauto. 
Qed.

Theorem apply_txn_finished:
  forall txn_record log_blocks t s' s o u,
    let key := key txn_record in
    let start := start txn_record in
    let addr_count := addr_count txn_record in
    let data_count := data_count txn_record in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
   
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (apply_txn txn_record log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
    snd s' = upd_batch_set (snd s) addr_list data_blocks /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks).
Proof.
  intros.
  eapply apply_txn_finished_oracle in H0; eauto.
  cleanup; intuition eauto.
Qed.

Definition apply_txn_crashed_oracle_is o n length_txn_blocks length_data_blocks :=
  (batch_operations_crypto_crashed_oracle_is o n (length_txn_blocks) \/
      o = rec_oracle_finished_crypto (length_txn_blocks) ++
     [LayerImplementation.Crash
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size)))] \/
      o = (rec_oracle_finished_crypto (length_txn_blocks) ++
    [LayerImplementation.Cont
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))]) ++
   rec_oracle_op1_disk n ++
   [OpToken
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
      (Token2 CryptoOperation
         (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size))
         DiskLayer.Crash)] \/
    o = (rec_oracle_finished_crypto (length_txn_blocks)++
  [LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))]) ++
 rec_oracle_op1_disk (length_data_blocks) ++
 [LayerImplementation.Crash CryptoDiskOperation] \/
    (exists k, k < length_data_blocks /\ 
    o = (rec_oracle_finished_crypto (length_txn_blocks) ++
  [LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))]) ++
 rec_oracle_op1_disk (length_data_blocks) ++
 LayerImplementation.Cont CryptoDiskOperation
 :: rec_oracle_op2 k ++
    [LayerImplementation.Crash
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))])).

Theorem apply_txn_crashed_oracle:
  forall txn log_blocks s' s o u,
    let key := key txn in
    let start := start txn in
    let addr_count := addr_count txn in
    let data_count := data_count txn in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
    
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (apply_txn txn log_blocks) (Crashed s') ->
    (exists n,
      ((fst (fst s') = fst (fst s) /\
      snd (fst s') =
      Mem.upd_batch (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))) /\
      snd s' = snd s /\
      consistent_with_upds (snd (fst s))
                           (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks)))) \/
      (fst (fst s') = fst (fst s) /\
       snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
       snd s' = upd_batch_set (snd s) (firstn n addr_list) (firstn n data_blocks) /\
       consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks))) /\
      apply_txn_crashed_oracle_is o n (length txn_blocks) (length data_blocks)).
Proof.
  unfold apply_txn_crashed_oracle_is, 
  apply_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.

  split_ors; cleanup.
  {
    apply decrypt_txn_crashed_oracle in H0; eauto; cleanup;
    intuition eauto; exists x; simpl; intuition eauto.
  }
  {
    eapply decrypt_txn_finished_oracle in H1; eauto; cleanup; simpl in *.
    eapply write_batch_crashed_oracle in H2; eauto; cleanup; subst.
    unfold batch_operations_disk_crashed_oracle_is  in *.
    repeat cleanup_pairs.
    repeat rewrite app_length; simpl.
    exists x0; simpl; intuition eauto; 
    subst; intuition eauto.
    cleanup; intuition eauto.
  }
Qed.

Theorem apply_txn_crashed:
  forall txn log_blocks s' s o u,
    let key := key txn in
    let start := start txn in
    let addr_count := addr_count txn in
    let data_count := data_count txn in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_blocks := map (decrypt key) txn_blocks in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
    
    length addr_list = length data_blocks ->
    exec CryptoDiskLang u o s (apply_txn txn log_blocks) (Crashed s') ->
    exists n,
      (fst (fst s') = fst (fst s) /\
      snd (fst s') =
      Mem.upd_batch (snd (fst s)) (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks))) /\
      snd s' = snd s /\
      consistent_with_upds (snd (fst s))
                           (firstn n (map (encrypt key) plain_blocks))
                     (firstn n ((map (fun v => (key, v)) plain_blocks)))) \/
      (fst (fst s') = fst (fst s) /\
       snd (fst s') =
       Mem.upd_batch (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks) /\
       snd s' = upd_batch_set (snd s) (firstn n addr_list) (firstn n data_blocks) /\
       consistent_with_upds (snd (fst s)) (map (encrypt key) plain_blocks)
                     (map (fun v => (key, v)) plain_blocks)).
Proof.
  intros; eapply apply_txn_crashed_oracle in H0; eauto.
  cleanup; eexists; intuition eauto.
Qed.

Lemma fold_left_add_remove_start:
forall l a,
fold_left Nat.add l a = a + fold_left Nat.add l 0.
Proof.
  induction l; simpl; intros; try lia.
  rewrite IHl.
  setoid_rewrite IHl at 2.
  lia.
Qed.

Definition apply_txns_finished_oracle_is txn_records :=
  fold_right (@app _) [] (map (fun txn => apply_txn_finished_oracle_is (addr_count txn + data_count txn) (data_count txn)) txn_records) ++
  [LayerImplementation.Cont CryptoDiskOperation].



Theorem apply_txns_finished_oracle:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    
    exec CryptoDiskLang u o s (apply_txns txn_records log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
    Mem.list_upd_batch (snd (fst s))
        (bimap (fun key lv => map (encrypt key) lv) (map key txn_records) l_plain_blocks)
        (bimap (fun key lv => map (fun v => (key, v)) lv) (map key txn_records) l_plain_blocks) /\
    snd s' = list_upd_batch_set (snd s) l_addr_list l_plain_data_blocks /\
    subset (snd (fst s)) (snd (fst s')) /\
    o = apply_txns_finished_oracle_is txn_records.
Proof.
  induction txn_records; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  
  assert (Al: length l = addr_count a). {        
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H8.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }

  eapply apply_txn_finished_oracle in H3; cleanup; eauto.
  edestruct IHtxn_records in H4; eauto; cleanup.
  repeat cleanup_pairs.
  simpl in *; intuition eauto.

  {
    rewrite map_map.
    erewrite map_ext, map_id.

    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
    setoid_rewrite map_map at 2.
    setoid_rewrite map_ext at 3.
    rewrite map_id; eauto.
    intros; simpl; apply encrypt_decrypt.
    intros; simpl; apply decrypt_encrypt.
  }

  {
    unfold get_addr_list at 2.
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
    repeat rewrite map_map.
    erewrite map_ext.
    rewrite map_id.
    rewrite <- Al. 
    rewrite skipn_app.
    rewrite firstn_app2; eauto.
    intros; simpl; apply encrypt_decrypt.
  }
  {
    eapply subset_consistent_upd; eauto.
  }
  {
    rewrite firstn_length_l.
    rewrite skipn_length, map_length, firstn_length_l.
    rewrite Minus.minus_plus; eauto.
    unfold apply_txns_finished_oracle_is; simpl; eauto.
    rewrite <- app_assoc; eauto.
    all: rewrite skipn_length; lia.
  }
  {
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_map_comm, skipn_map_comm.
    cleanup.
    unfold get_addr_list in *.
    rewrite map_map.
    erewrite map_ext.
    rewrite map_id.
    repeat rewrite map_length; eauto.
    intros; simpl; apply encrypt_decrypt.
  }
Qed.

Theorem apply_txns_finished:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    
    exec CryptoDiskLang u o s (apply_txns txn_records log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
    Mem.list_upd_batch (snd (fst s))
        (bimap (fun key lv => map (encrypt key) lv) (map key txn_records) l_plain_blocks)
        (bimap (fun key lv => map (fun v => (key, v)) lv) (map key txn_records) l_plain_blocks) /\
    snd s' = list_upd_batch_set (snd s) l_addr_list l_plain_data_blocks /\
    subset (snd (fst s)) (snd (fst s')).
Proof.
  intros. eapply apply_txns_finished_oracle in H3; eauto.
  cleanup; intuition eauto.
Qed.

Definition apply_txns_crashed_oracle_is o txn_records a b m :=
  (let crashed_record := seln txn_records a {|key:= key0; start:=0; addr_count:=0; data_count:=0 |} in
        exists o1 o2,
        o = o1 ++ o2 /\
        o1 = fold_right (@app _) [] (map (fun rec => apply_txn_finished_oracle_is (addr_count rec + data_count rec) (data_count rec)) (firstn a txn_records)) /\
        (apply_txn_crashed_oracle_is o2 b (addr_count crashed_record + data_count crashed_record) (data_count crashed_record) \/
        apply_txn_crashed_oracle_is o2 m (addr_count crashed_record + data_count crashed_record) (data_count crashed_record))).

Theorem apply_txns_crashed_oracle:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    
    exec CryptoDiskLang u o s (apply_txns txn_records log_blocks) (Crashed s') ->
    
    exists n m a b,
      fst (fst s') = fst (fst s) /\
      snd (fst s') = Mem.upd_batch (Mem.list_upd_batch (snd (fst s))
          (firstn a (bimap (fun key lv => map (encrypt key) lv)
                    (map key txn_records) l_plain_blocks))
          (firstn a (bimap (fun key lv => map (fun v => (key, v)) lv)
                    (map key txn_records) l_plain_blocks)))
          (firstn b (seln (bimap (fun key lv => map (encrypt key) lv)
                          (map key txn_records) l_plain_blocks) a []))
          (firstn b (seln (bimap (fun key lv => map (fun v => (key, v)) lv)
                          (map key txn_records) l_plain_blocks) a [])) /\
      snd s' = upd_batch_set (list_upd_batch_set (snd s)
                   (firstn n l_addr_list) (firstn n l_plain_data_blocks))
                   (firstn m (seln l_addr_list n []))
                   (firstn m (seln l_plain_data_blocks n [])) /\
      n <= a /\ a <= S a /\
      subset (snd (fst s)) (snd (fst s')) /\
      apply_txns_crashed_oracle_is o txn_records a b m.
Proof.
  unfold apply_txns_crashed_oracle_is;
  induction txn_records; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  {
    intuition eauto.
    exists 0, 0, 0 ,0; simpl; eauto.
    intuition eauto.
    do 2 eexists; intuition eauto.
    simpl; eauto.
    unfold apply_txn_crashed_oracle_is, batch_operations_crypto_crashed_oracle_is; simpl.
    intuition eauto.
  }
  
  assert (Al: length l = addr_count a). {
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H7.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }
  
  split_ors; cleanup; repeat invert_exec.
  {
    eapply apply_txn_crashed_oracle in H3; eauto; cleanup.
    {
      intuition eauto.
      {
        exists 0, 0, 0, x; simpl.
        unfold plain_addr_blocks_valid, get_addr_blocks,
        plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
        cleanup; eauto.
        repeat cleanup_pairs; intuition eauto.
        
        rewrite firstn_sum_split.
        rewrite firstn_firstn in H7;
        rewrite min_l in H7 by lia.
        rewrite H7.
        rewrite skipn_firstn_comm in H13.
        rewrite H13, <- map_app; eauto.
        setoid_rewrite map_map at 2.
        setoid_rewrite map_ext at 2.
        rewrite map_id.
        setoid_rewrite map_map at 2.
        setoid_rewrite map_ext at 3.
        rewrite map_id; eauto.

        intros; simpl; apply encrypt_decrypt.
        intros; simpl; apply encrypt_decrypt.
        eapply upd_batch_consistent_subset; eauto.
        do 2 eexists; intuition eauto.
        simpl; eauto.
        rewrite firstn_length_l in H4.
        rewrite skipn_length, map_length, firstn_length_l in H4.
        rewrite Minus.minus_plus in H4; eauto.
        all: rewrite skipn_length; lia.
      }
      {
        exists 0, x, 0, (length (l++x0)); simpl.
        unfold plain_addr_blocks_valid, get_addr_blocks,
        plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
        cleanup; eauto.
        repeat cleanup_pairs.
        
        rewrite firstn_sum_split.
        rewrite firstn_firstn in H7;
        rewrite min_l in H7 by lia.
        rewrite H7.
        rewrite skipn_firstn_comm in H13.
        rewrite H13, <- map_app; eauto.
        intuition eauto.

        {
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 2.
          rewrite map_id.
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 3.
          rewrite map_id; eauto.
          repeat rewrite firstn_oob; eauto.
          rewrite map_length; eauto.
          rewrite map_length; eauto.
          
          intros; simpl; apply encrypt_decrypt.
          intros; simpl; apply encrypt_decrypt.
        }
        {
          repeat rewrite map_map.
          repeat erewrite map_ext, map_id.          
          rewrite <- Al. 
          rewrite skipn_app.
          rewrite firstn_app2; eauto.
          
          intros; simpl; apply encrypt_decrypt.
        }
        {
          eapply upd_batch_consistent_subset; eauto.
           unfold plain_addr_blocks_valid, get_addr_blocks,
           plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
           cleanup; eauto.
           repeat cleanup_pairs.
        
           rewrite firstn_sum_split in H10.
           rewrite H7 in H10.
           rewrite H13, <- map_app in H10; eauto.
        }
        {
          do 2 eexists; intuition eauto.
        simpl; eauto.
        rewrite firstn_length_l in H4.
        rewrite skipn_length, map_length, firstn_length_l in H4.
        rewrite Minus.minus_plus in H4; eauto.
        all: rewrite skipn_length; lia.
        }
      }
    }
    {
      unfold plain_addr_blocks_valid, plain_data_blocks_valid,
      get_addr_blocks, get_data_blocks in *; simpl in *.
      rewrite firstn_sum_split.
      
      rewrite firstn_firstn in H7;
      rewrite min_l in H7 by lia.
      rewrite H7.
      rewrite skipn_firstn_comm in H13.
      rewrite H13, <- map_app; eauto.
      repeat rewrite map_map.
      repeat erewrite map_ext, map_id.
      rewrite <- Al. 
      rewrite skipn_app.
      rewrite firstn_app2; eauto.
      intros; simpl; apply encrypt_decrypt.
    }
  }
  {
    eapply apply_txn_finished_oracle in H4; cleanup; eauto.
    edestruct IHtxn_records in H5; eauto; cleanup.
    
    unfold get_addr_list at 1; simpl.
    {
        exists (S x2), x4, (S x5), x6; simpl.
        unfold plain_addr_blocks_valid, get_addr_blocks,
        plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
        cleanup; eauto.
        repeat cleanup_pairs.
        
        rewrite firstn_sum_split.
        rewrite firstn_firstn in H7;
        rewrite min_l in H7 by lia.
        rewrite H7.
        rewrite skipn_firstn_comm in H13.
        rewrite H13, <- map_app; eauto.
        split; eauto.
        split; eauto.
        {
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 2.
          rewrite map_id.
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 3.
          rewrite map_id; eauto.
          intros; simpl; apply encrypt_decrypt.
          intros; simpl; apply encrypt_decrypt.
        }
        split; eauto.
        {
          repeat rewrite map_map.
          repeat erewrite map_ext, map_id.          
          rewrite <- Al. 
          rewrite skipn_app.
          rewrite firstn_app2; eauto.          
          intros; simpl; apply encrypt_decrypt.
        }
        split; eauto.
        lia.
        split; eauto.
        split; eauto.
        {          
          eapply subset_consistent_upd; eauto.
          unfold plain_addr_blocks_valid, get_addr_blocks,
          plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
          cleanup; eauto.
          repeat cleanup_pairs.
          
          rewrite firstn_sum_split in H18.
          rewrite H7 in H18.
          rewrite H13, <- map_app in H18; eauto.

          rewrite firstn_sum_split.
          rewrite H7.
          rewrite H13, <- map_app; eauto.
        }
        {
          do 2 eexists; split.
          2: split; eauto.
          {
            rewrite skipn_length;
            repeat rewrite map_length.
            repeat rewrite app_length; cleanup.
            erewrite <- map_length, <- H13.
            repeat rewrite firstn_length_l.
            rewrite Minus.minus_plus; eauto.
            rewrite <- app_assoc; eauto.
            repeat rewrite skipn_length; lia.
          }
        }        
    }
    {
      unfold plain_addr_blocks_valid, plain_data_blocks_valid,
      get_addr_blocks, get_data_blocks in *; simpl in *.
      rewrite firstn_sum_split.
      
      rewrite firstn_firstn in H7;
      rewrite min_l in H7 by lia.
      rewrite H7.
      rewrite skipn_firstn_comm in H13.
      rewrite H13, <- map_app; eauto.
      repeat rewrite map_map.
      repeat erewrite map_ext, map_id.
      rewrite <- Al. 
      rewrite skipn_app.
      rewrite firstn_app2; eauto.
      intros; simpl; apply encrypt_decrypt.
    }
  }
Qed.




Theorem apply_txns_crashed:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    
    exec CryptoDiskLang u o s (apply_txns txn_records log_blocks) (Crashed s') ->
    
    exists n m a b,
      fst (fst s') = fst (fst s) /\
      snd (fst s') = Mem.upd_batch (Mem.list_upd_batch (snd (fst s))
          (firstn a (bimap (fun key lv => map (encrypt key) lv)
                    (map key txn_records) l_plain_blocks))
          (firstn a (bimap (fun key lv => map (fun v => (key, v)) lv)
                    (map key txn_records) l_plain_blocks)))
          (firstn b (seln (bimap (fun key lv => map (encrypt key) lv)
                          (map key txn_records) l_plain_blocks) a []))
          (firstn b (seln (bimap (fun key lv => map (fun v => (key, v)) lv)
                          (map key txn_records) l_plain_blocks) a [])) /\
      snd s' = upd_batch_set (list_upd_batch_set (snd s)
                   (firstn n l_addr_list) (firstn n l_plain_data_blocks))
                   (firstn m (seln l_addr_list n []))
                   (firstn m (seln l_plain_data_blocks n [])) /\
      n <= a /\ a <= S a /\
      subset (snd (fst s)) (snd (fst s')).
Proof.
  intros.
  eapply apply_txns_crashed_oracle in H3; eauto.
  cleanup; do 4 eexists; intuition eauto.
Qed.

Global Opaque apply_txns.


Theorem decrypt_txns_finished:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    
    exec CryptoDiskLang u o s (decrypt_txns txn_records log_blocks) (Finished s' t) ->
    t = combine l_addr_list l_plain_data_blocks /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') =
    Mem.list_upd_batch (snd (fst s))
        (bimap (fun key lv => map (encrypt key) lv) (map key txn_records) l_plain_blocks)
        (bimap (fun key lv => map (fun v => (key, v)) lv) (map key txn_records) l_plain_blocks) /\
    snd s' = snd s /\
    subset (snd (fst s)) (snd (fst s')).
Proof.
  induction txn_records; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  
  assert (Al: length l = addr_count a). {
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H8.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }

  eapply decrypt_txn_finished in H3; cleanup; eauto.
  edestruct IHtxn_records in H4; eauto; cleanup.
  repeat cleanup_pairs.
  simpl in *; intuition eauto.

  {
    unfold get_addr_list at 2; simpl.

    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
    setoid_rewrite map_map.
    setoid_rewrite map_ext.
    repeat rewrite map_id; eauto.
    rewrite firstn_app2; eauto.
    rewrite <- Al, skipn_app; eauto.
    intros; simpl; apply encrypt_decrypt.
    intros; simpl; apply encrypt_decrypt.
  }

  {
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
    setoid_rewrite map_map at 2.
    setoid_rewrite map_ext at 2.
    rewrite map_id.
    setoid_rewrite map_map at 2.
    setoid_rewrite map_ext at 3.
    rewrite map_id; eauto.
    intros; simpl; apply encrypt_decrypt.
    intros; simpl; apply encrypt_decrypt.
  }
  {
    eapply subset_consistent_upd; eauto.
  }

  {
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_map_comm, skipn_map_comm.
    cleanup.
    unfold get_addr_list in *.
    rewrite map_map.
    erewrite map_ext.
    rewrite map_id.
    repeat rewrite map_length; eauto.
    intros; simpl; apply encrypt_decrypt.
  }
Qed.

Theorem decrypt_txns_crashed:
  forall txn_records log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' u,
    let l_addr_list := bimap get_addr_list txn_records l_plain_addr_blocks in
    let l_plain_blocks := bimap (@app value)l_plain_addr_blocks l_plain_data_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txn_records ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txn_records ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txn_records ->
    exec CryptoDiskLang u o s (decrypt_txns txn_records log_blocks) (Crashed s') ->
    
    exists a b,
      fst (fst s') = fst (fst s) /\
      snd (fst s') = Mem.upd_batch (Mem.list_upd_batch (snd (fst s))
          (firstn a (bimap (fun key lv => map (encrypt key) lv)
                    (map key txn_records) l_plain_blocks))
          (firstn a (bimap (fun key lv => map (fun v => (key, v)) lv)
                    (map key txn_records) l_plain_blocks)))
          (firstn b (seln (bimap (fun key lv => map (encrypt key) lv)
                          (map key txn_records) l_plain_blocks) a []))
          (firstn b (seln (bimap (fun key lv => map (fun v => (key, v)) lv)
                          (map key txn_records) l_plain_blocks) a [])) /\
      snd s' = snd s /\
      subset (snd (fst s)) (snd (fst s')).
Proof.
  induction txn_records; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  {
    intuition eauto.
    exists 0, 0; simpl; eauto.
  }
  
  assert (Al: length l = addr_count a). {
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H7.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }
  
  split_ors; cleanup; repeat invert_exec.
  {
    eapply decrypt_txn_crashed in H3; eauto; cleanup.
    
    exists 0, x; simpl.
    unfold plain_addr_blocks_valid, get_addr_blocks,
    plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
    cleanup; eauto.
    repeat cleanup_pairs; intuition eauto.
    
    rewrite firstn_sum_split.
    rewrite firstn_firstn in H7;
    rewrite min_l in H7 by lia.
    rewrite H7.
    rewrite skipn_firstn_comm in H13.
    rewrite H13, <- map_app; eauto.
    setoid_rewrite map_map at 2.
    setoid_rewrite map_ext at 2.
    rewrite map_id.
    setoid_rewrite map_map at 2.
    setoid_rewrite map_ext at 3.
    rewrite map_id; eauto.    
    intros; simpl; apply encrypt_decrypt.
    intros; simpl; apply encrypt_decrypt.
    eapply upd_batch_consistent_subset; eauto.
  }
  {
    eapply decrypt_txn_finished in H4; cleanup; eauto.
    repeat cleanup_pairs.
    {
      split_ors; cleanup.
      {
        edestruct IHtxn_records in H3; eauto; cleanup.
        repeat cleanup_pairs.
        simpl in *.
    
        exists (S x), x1; simpl.
        unfold plain_addr_blocks_valid, get_addr_blocks,
        plain_data_blocks_valid, get_data_blocks, get_addr_list in *;
        cleanup; eauto.
        repeat cleanup_pairs.
        
        rewrite firstn_sum_split.
        rewrite firstn_firstn in H7;
        rewrite min_l in H7 by lia.
        rewrite H7.
        rewrite skipn_firstn_comm in H13.
        rewrite H13, <- map_app; eauto.
        intuition eauto.

        {
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 2.
          rewrite map_id.
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 3.
          rewrite map_id; eauto.
          intros; simpl; apply encrypt_decrypt.
          intros; simpl; apply encrypt_decrypt.
        }
        {
          eapply subset_consistent_upd; eauto.
          rewrite firstn_sum_split.
          rewrite H7.
          rewrite H13, <- map_app; eauto.
          
          rewrite firstn_sum_split in H8.
          rewrite H7, H13, <- map_app in H8; eauto.
        }
      }
      {
         eapply decrypt_txns_finished in H4; cleanup; eauto.
         invert_exec. repeat cleanup_pairs.
         simpl in *.

         exists (S (length txn_records)), 0; simpl.
        unfold plain_addr_blocks_valid, plain_data_blocks_valid,
        get_addr_blocks, get_data_blocks in *; simpl in *.
        rewrite firstn_sum_split.
        
        rewrite firstn_firstn in H7;
        rewrite min_l in H7 by lia.
        rewrite H7.
        rewrite skipn_firstn_comm in H13.
        rewrite H13, <- map_app; eauto.
        intuition eauto.
        {
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 2.
          rewrite map_id.
          setoid_rewrite map_map at 2.
          setoid_rewrite map_ext at 3.
          rewrite map_id; eauto.
          repeat rewrite firstn_oob; simpl; eauto.
          repeat rewrite bimap_length, map_length ; try lia.
          repeat rewrite bimap_length, map_length ; try lia.
          intros; simpl; apply encrypt_decrypt.
          intros; simpl; apply encrypt_decrypt.
        }
        {
          eapply subset_consistent_upd; eauto.
          rewrite firstn_sum_split.
          rewrite H7.
          rewrite H13, <- map_app; eauto.
          
          rewrite firstn_sum_split in H11.
          rewrite H7, H13, <- map_app in H11; eauto.
        }
      }
    }
    {
      unfold plain_addr_blocks_valid, plain_data_blocks_valid,
      get_addr_blocks, get_data_blocks in *; simpl in *.
      rewrite firstn_map_comm, skipn_map_comm.
      cleanup.
      unfold get_addr_list in *.
      rewrite map_map.
      erewrite map_ext.
      rewrite map_id.
      repeat rewrite map_length; eauto.
      intros; simpl; apply encrypt_decrypt.
    }
  }
Qed.

Definition read_encrypted_log_finished_oracle_is hdr valid_part :=
  match valid_part with
    | Old_Part => OpToken CryptoDiskOperation
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)
  :: LayerImplementation.Cont CryptoDiskOperation
     :: rec_oracle_finished_disk
          (count (current_part hdr)) ++
        (rec_oracle_finished_crypto
           (count (current_part hdr)) ++
         [LayerImplementation.Cont
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
        rec_oracle_finished_disk
          (fold_left Nat.add
             (map (fun rec : txn_record => addr_count rec + data_count rec)
                (records (old_part hdr)))
             0) ++
        [LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))]

    | Current_Part => OpToken CryptoDiskOperation
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)
  :: LayerImplementation.Cont CryptoDiskOperation
     :: rec_oracle_finished_disk
          (count (current_part hdr)) ++
        (rec_oracle_finished_crypto
           (count (current_part hdr)) ++
         [LayerImplementation.Cont
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
        [LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]
    end.

Theorem read_encrypted_log_finished_oracle :
  forall o s txns hdr r s' header_state log_state valid_part hdr_blockset log_blocksets u,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang u o s read_encrypted_log (Finished s' r) ->
    r =  (valid_header_part, valid_log_blocks) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd s' = snd s /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    snd (fst s') = snd (fst s) /\
    o = read_encrypted_log_finished_oracle_is hdr valid_part.
Proof.
  unfold read_encrypted_log_finished_oracle_is, 
  read_encrypted_log, read_header, check_hash.
  intros; destruct valid_part.
  {(** Current part **)
    invert_exec.
    invert_exec'' H1.    
    invert_exec'' H9.
    invert_exec'' H12.
    invert_exec'' H8.
    invert_exec'' H9.
    invert_exec.
    eapply read_consecutive_finished_oracle in H1; cleanup.
    assert (x3 = firstn (count (current_part hdr)) (map fst log_blocksets)).
    {
      eapply list_seln_ext.
      rewrite firstn_length_l; eauto.
      unfold log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match; eauto.
      rewrite map_length;
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *;
      cleanup_no_match; eauto.      
      setoid_rewrite H6; lia.
      intros.
      edestruct H3.
      rewrite <- H1; eauto.
      cleanup_no_match.
      rewrite <- H6.
      rewrite seln_firstn; eauto.
      erewrite seln_map.
      unfold log_rep_explicit, log_data_blocks_rep in *;
      cleanup_no_match; eauto.
      destruct s; simpl in *.
      erewrite e1 in H6.
      rewrite <- H6; eauto.
      all: unfold log_rep_explicit, log_header_block_rep,
           log_rep_inner,
           header_part_is_valid in *; simpl in *; cleanup_no_match;
      try setoid_rewrite H9; try lia.
    }
    cleanup.
    repeat invert_exec.
    all: try congruence.
    {
      apply hash_all_finished_oracle in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep in *; cleanup_no_match.
      intuition eauto.
      eapply upd_batch_consistent_subset; eauto.
    }
    {
      apply hash_all_finished_oracle in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; cleanup_no_match.
      exfalso; apply n.
      setoid_rewrite H15.
      rewrite <- H19; eauto.
    }
  }

  {(** Old Part **)
    invert_exec.
    invert_exec'' H1.    
    invert_exec'' H9.
    invert_exec'' H12.
    invert_exec'' H8.
    invert_exec'' H9.
    invert_exec.
    eapply read_consecutive_finished_oracle in H1; cleanup.
    assert (x3 = firstn (count (current_part hdr)) (map fst log_blocksets)).
    {
      eapply list_seln_ext.
      rewrite firstn_length_l; eauto.
      unfold log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match; eauto.
      rewrite map_length;
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *;
      cleanup_no_match; eauto.      
      setoid_rewrite H6; lia.
      intros.
      edestruct H3.
      rewrite <- H1; eauto.
      cleanup_no_match.
      rewrite <- H6.
      rewrite seln_firstn; eauto.
      erewrite seln_map.
      unfold log_rep_explicit, log_data_blocks_rep in *;
      cleanup_no_match; eauto.
      destruct s; simpl in *.
      erewrite e1 in H6.
      rewrite <- H6; eauto.
      all: unfold log_rep_explicit, log_header_block_rep,
           log_rep_inner,
           header_part_is_valid in *; simpl in *; cleanup_no_match;
      try setoid_rewrite H9; try lia.
    }
    cleanup.
    repeat invert_exec.
    all: try congruence.
    {
      apply hash_all_finished_oracle in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; cleanup_no_match.
      exfalso; apply H0; eauto.      
    }
    {       
      apply hash_all_finished_oracle in H2; cleanup.
      apply read_consecutive_finished_oracle in H4; cleanup.
      assert (x5= firstn (count (old_part hdr)) (map fst log_blocksets)).
      {
        eapply list_seln_ext.
        rewrite firstn_length_l; eauto.
        unfold log_rep_explicit, log_header_block_rep in *;
        cleanup_no_match; eauto.
        rewrite map_length;
        unfold log_rep_explicit, log_header_block_rep,
        log_rep_inner, header_part_is_valid in *;
        cleanup_no_match; eauto.      
        setoid_rewrite H13; lia.
        intros.
        edestruct H4.
        rewrite <- H2; eauto.
        cleanup_no_match.
        rewrite <- H13.
        rewrite seln_firstn; eauto.
        erewrite seln_map.
        unfold log_rep_explicit, log_data_blocks_rep in *;
        cleanup_no_match; eauto.
        destruct s; simpl in *.
        erewrite e1 in H13.
        rewrite <- H13; eauto.
        all: unfold log_rep_explicit, log_header_block_rep,
             log_rep_inner,
             header_part_is_valid in *; simpl in *; cleanup_no_match;
        try setoid_rewrite H15; try lia.
      }
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; simpl in *; cleanup_no_match.
      intuition eauto.
      eapply upd_batch_consistent_subset; eauto.
    }
  }
Qed.


Theorem read_encrypted_log_finished :
  forall o s txns hdr r s' header_state log_state valid_part hdr_blockset log_blocksets u,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang u o s read_encrypted_log (Finished s' r) ->
    r =  (valid_header_part, valid_log_blocks) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd s' = snd s /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    snd (fst s') = snd (fst s).
Proof.
  intros.
  eapply read_encrypted_log_finished_oracle in H1; eauto.
  intuition eauto.
Qed.

Definition read_encrypted_log_crashed_oracle_is o hdr valid_part:=
(o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Crash)] \/
       o = [OpToken
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
       (Token2 CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size))
          DiskLayer.Cont);
        LayerImplementation.Crash
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size)))] \/
    (exists n o',
    o = OpToken
      (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
      (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)) DiskLayer.Cont)
      :: LayerImplementation.Cont
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value
             (fun a : addr => a < disk_size))) :: o' /\
      batch_operations_disk_crashed_oracle_is o' n
             (count (current_part hdr))) \/
    (exists n o',
    o = OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)
  :: LayerImplementation.Cont
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
     :: rec_oracle_finished_disk
          (count (current_part hdr)) ++ o' /\ 
          batch_operations_crypto_crashed_oracle_is o' n
       (count (current_part hdr))) \/ 
    (o = OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont)
  :: LayerImplementation.Cont
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
     :: rec_oracle_finished_disk
          (count (current_part hdr)) ++
        rec_oracle_finished_crypto
          (count (current_part hdr)) ++
        [LayerImplementation.Crash
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) \/ 
      (o = OpToken
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
      (Token2 CryptoOperation
         (DiskOperation addr_dec value (fun a : addr => a < disk_size))
         DiskLayer.Cont)
    :: LayerImplementation.Cont
         (HorizontalComposition CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
       :: rec_oracle_finished_disk
            (count (current_part hdr)) ++
          (rec_oracle_finished_crypto
             (count (current_part hdr)) ++
           [LayerImplementation.Cont
              (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
          [LayerImplementation.Crash
             (HorizontalComposition CryptoOperation
                (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) \/ 
      (exists n o', 
      valid_part = Old_Part /\
      o = OpToken
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
      (Token2 CryptoOperation
         (DiskOperation addr_dec value (fun a : addr => a < disk_size))
         DiskLayer.Cont)
    :: LayerImplementation.Cont
         (HorizontalComposition CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
       :: rec_oracle_finished_disk
            (count (current_part hdr)) ++
          (rec_oracle_finished_crypto
             (count (current_part hdr)) ++
           [LayerImplementation.Cont
              (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
          o' /\
      batch_operations_disk_crashed_oracle_is o' n
          (count (old_part hdr))) \/
          (valid_part = Old_Part /\
          o = OpToken
          (HorizontalComposition CryptoOperation
             (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
          (Token2 CryptoOperation
             (DiskOperation addr_dec value (fun a : addr => a < disk_size))
             DiskLayer.Cont)
        :: LayerImplementation.Cont
             (HorizontalComposition CryptoOperation
                (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
           :: rec_oracle_finished_disk
                (count (current_part hdr)) ++
              (rec_oracle_finished_crypto
                 (count (current_part hdr)) ++
               [LayerImplementation.Cont
                  (HorizontalComposition CryptoOperation
                     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
              rec_oracle_finished_disk
                (count (old_part hdr)) ++
              [LayerImplementation.Crash
                 (HorizontalComposition CryptoOperation
                    (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))])).

Theorem read_encrypted_log_crashed_oracle :
  forall o s txns hdr s' header_state log_state valid_part hdr_blockset log_blocksets u,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang u o s read_encrypted_log (Crashed s') ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd s' = snd s /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    snd (fst s') = snd (fst s) /\
    read_encrypted_log_crashed_oracle_is o hdr valid_part.
Proof.
  unfold read_encrypted_log_crashed_oracle_is, 
  read_encrypted_log, read_header, check_hash; simpl; intros.
  repeat (try split_ors; cleanup_no_match; invert_exec; repeat cleanup);
  try solve[ destruct s; simpl; intuition eauto; destruct valid_part; eauto ].

  eapply read_consecutive_crashed_oracle in H1;
  cleanup_no_match; eauto;
  simpl in *; intuition eauto.
  cleanup.
  unfold log_rep_explicit, log_header_block_rep in *; 
    cleanup_no_match; simpl; intuition eauto. 

  all: try congruence.
  all: try solve [
    eapply read_consecutive_finished_oracle in H3;
  cleanup; eauto;
  destruct s; simpl; eauto;
  try eapply hash_all_finished_oracle in H4;
  try eapply hash_all_finished_oracle in H1;
  cleanup; eauto;
  destruct s; simpl in *; eauto;
  eapply upd_batch_consistent_subset in H4;
  cleanup_no_match; intuition eauto; try lia;
  unfold log_rep_explicit, log_header_block_rep in *; 
  cleanup_no_match; simpl; intuition eauto]. 

  - eapply read_consecutive_finished_oracle in H3;
    cleanup; eauto;
    destruct s; simpl; eauto.
    eapply hash_all_crashed_oracle in H1;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply upd_batch_consistent_subset in H4.
    cleanup_no_match; intuition eauto; try lia.
    unfold log_rep_explicit, log_header_block_rep in *; 
    cleanup_no_match; simpl; intuition eauto. 

  - eapply read_consecutive_finished_oracle in H3;
  cleanup; eauto;
  destruct s; simpl; eauto;
  eapply hash_all_finished_oracle in H1;
  cleanup; eauto;
  destruct s; simpl in *; eauto.
  eapply read_consecutive_crashed_oracle in H4;
    cleanup_no_match; eauto.      
    eapply upd_batch_consistent_subset in H5.
  cleanup_no_match; intuition eauto; try lia.
  unfold log_rep_explicit, log_header_block_rep in *; 
    cleanup_no_match; simpl; intuition eauto.
  simpl in *. 

    assert (x4 = firstn (count (current_part (decode_header (fst (snd x2 hdr_block_num))))) (map fst log_blocksets)).
    {
      eapply list_seln_ext.
      rewrite firstn_length_l; eauto.
      unfold log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match; eauto.
      rewrite map_length;
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *;
      cleanup_no_match; eauto.      
      setoid_rewrite H9; eauto.
      intros.
      edestruct H3.
      rewrite <- H2; eauto.
      cleanup_no_match.
      rewrite <- H15.
      rewrite seln_firstn; eauto.
      erewrite seln_map.
      unfold log_rep_explicit, log_data_blocks_rep in *;
      cleanup_no_match; eauto.
      destruct x2; simpl in *.
      erewrite e in H15.
      rewrite <- H15; eauto.
      all: unfold log_rep_explicit, log_header_block_rep,
           log_rep_inner,
           header_part_is_valid in *; simpl in *; cleanup_no_match;
      try setoid_rewrite H9; try lia.
    }
    subst.
    unfold log_rep_explicit, log_header_block_rep in *; 
    cleanup_no_match.
    destruct valid_part; simpl in *. 
    exfalso; apply n; eauto.
    unfold log_rep_inner, header_part_is_valid  in *; cleanup_no_match; eauto.
    unfold log_rep_explicit, log_header_block_rep in *; 
    cleanup_no_match; simpl; intuition eauto.
    
  - eapply read_consecutive_finished_oracle in H3;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished_oracle in H1;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply read_consecutive_finished_oracle in H5;
      cleanup_no_match; eauto.      
      eapply upd_batch_consistent_subset in H4.
    cleanup_no_match; intuition eauto; try lia.
  assert (x4 = firstn (count (current_part (decode_header (fst (snd x2 hdr_block_num))))) (map fst log_blocksets)).
  {
    eapply list_seln_ext.
    rewrite firstn_length_l; eauto.
    unfold log_rep_explicit, log_header_block_rep in *;
    cleanup_no_match; eauto.
    rewrite map_length;
    unfold log_rep_explicit, log_header_block_rep,
    log_rep_inner, header_part_is_valid in *;
    cleanup_no_match; eauto.      
    setoid_rewrite H10; eauto.
    intros.
    edestruct H3.
    rewrite <- H2; eauto.
    cleanup_no_match.
    rewrite <- H10.
    rewrite seln_firstn; eauto.
    erewrite seln_map.
    unfold log_rep_explicit, log_data_blocks_rep in *;
    cleanup_no_match; eauto.
    destruct x2; simpl in *.
    erewrite e1 in H10.
    rewrite <- H10; eauto.
    all: unfold log_rep_explicit, log_header_block_rep,
         log_rep_inner,
         header_part_is_valid in *; simpl in *; cleanup_no_match;
    try setoid_rewrite H13; try lia.
  }
  subst.
  unfold log_rep_explicit, log_header_block_rep in *; 
  cleanup_no_match.
  destruct valid_part; simpl in *. 
  exfalso; apply n; eauto.
  unfold log_rep_inner, header_part_is_valid  in *; cleanup_no_match; eauto.
  unfold log_rep_explicit, log_header_block_rep in *; 
  cleanup_no_match; simpl; intuition eauto.
Qed.


Theorem read_encrypted_log_crashed :
  forall o s txns hdr s' header_state log_state valid_part hdr_blockset log_blocksets u,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang u o s read_encrypted_log (Crashed s') ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd s' = snd s /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    snd (fst s') = snd (fst s).
Proof.
  intros.
  eapply read_encrypted_log_crashed_oracle in H1; eauto.
  cleanup; intuition eauto.
Qed.

Definition flush_txns_finished_oracle_is txn_records :=
  apply_txns_finished_oracle_is txn_records ++
  [OpToken
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
   (Token2 CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size))
      DiskLayer.Cont);
OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont);
LayerImplementation.Cont
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)));
OpToken CryptoDiskOperation
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont);
OpToken CryptoDiskOperation
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont)].

Theorem flush_txns_finished_oracle:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s' t u,
    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang u o s (flush_txns txn_records log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) 
    (map addr_list txns) (map data_blocks txns)) 
    hdr_block_num (encode_header (update_hdr hdr header_part0))) /\
    o = flush_txns_finished_oracle_is txn_records.
Proof.
  unfold flush_txns_finished_oracle_is, 
  flush_txns, update_header, read_header, write_header; simpl; intros.
  repeat invert_exec; simpl in *; cleanup.
  eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; eauto; cleanup.  
  eapply apply_txns_finished_oracle in H2; eauto; cleanup.
  repeat cleanup_pairs; simpl in *.
  rewrite sync_upd_comm; simpl.
  rewrite sync_upd_set_comm.
  rewrite sync_idempotent.
  repeat rewrite sync_list_upd_batch_set; simpl.
  rewrite map_map; simpl.
  cleanup; intuition eauto.
  {
    unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
    do 2 eexists;
    exists (map (fun vs => (fst vs, [])) log_blocksets); split; eauto.
    intuition.
    {
      unfold log_header_block_rep in *; cleanup; simpl in *.
      rewrite upd_eq; eauto.
    }
    {
      unfold log_data_blocks_rep in *; cleanup; simpl in *.
      rewrite map_length.
      intuition.
      rewrite upd_ne; eauto.
      unfold log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H14 in *.
      erewrite bimap_get_addr_list; eauto.
      rewrite list_upd_batch_not_in.
      unfold sync.
      rewrite H.
      erewrite seln_map; eauto.
      rewrite <- H6; eauto.
      {
        intros.
        apply in_map_iff in H16; cleanup.
        eapply Forall_forall in H15; eauto.
        unfold txn_well_formed in H15; cleanup.
        intuition.
        eapply Forall_forall in H21; eauto.
        pose proof data_start_where_log_ends.
        setoid_rewrite H6 in H13.
        lia.
      }
      {
        rewrite map_length; eauto.
      }
      {
        apply in_map_iff in H13; cleanup; eauto.
      }
      {
        setoid_rewrite H6; eauto.
      }
    }
    {
      rewrite map_length; eauto.
    }
    {
      simpl in *.
      rewrite encode_decode_header; simpl; lia.
    }
    {
      simpl in *.
      rewrite encode_decode_header; simpl.
      rewrite list_upd_batch_set_not_in.
      unfold log_header_block_rep in *; cleanup; simpl in *.
      cleanup; simpl; eauto.
      {
        intros.
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; cleanup.
        rewrite <- H12 in *.
        setoid_rewrite <- H12 in H.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; cleanup.
        eapply Forall_forall in H13; eauto.
        unfold txn_well_formed in H13; cleanup.
        intuition.
        eapply Forall_forall in H18; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
      }
    }
    {
      simpl.
      rewrite map_map; simpl.
      rewrite encode_decode_header; simpl.
      unfold log_rep_inner in *; cleanup; simpl in *; intuition eauto.
      {
        apply header_part0_valid.
      }
      {
        apply txns_valid_nil.
      }
    }
  }
  {
    rewrite list_upd_batch_set_not_in.
    
    unfold log_rep_explicit, log_header_block_rep in *; cleanup; simpl in *; eauto.
    cleanup; simpl in *; eauto.
    unfold log_rep_inner, txns_valid in *; cleanup.
    rewrite <- H2 in *.
    erewrite bimap_get_addr_list; [| | | eauto]; eauto.
    
    rewrite map_length; eauto.
    unfold header_part_is_valid in *; cleanup; eauto.
    {
      intros.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H13 in *.
      erewrite bimap_get_addr_list in H2; [ | | | eauto]; eauto.
      apply in_map_iff in H2; cleanup.
      eapply Forall_forall in H14; eauto.
      unfold txn_well_formed in H14; cleanup.
      intuition.
      eapply Forall_forall in H18; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.      
      rewrite map_length; eauto.
    }
  }
Qed.

Theorem flush_txns_finished:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s' t u,

    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang u o s (flush_txns txn_records log_blocks) (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns)) hdr_block_num (encode_header (update_hdr hdr header_part0))).
Proof.
  intros.
  eapply flush_txns_finished_oracle in H2; eauto.
  cleanup; intuition eauto.
Qed.

Definition flush_txns_crashed_oracle_is_1 o txn_records m :=
  (o = (apply_txns_finished_oracle_is txn_records ++
        [OpToken (HorizontalComposition CryptoOperation (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
           (Token2 CryptoOperation (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)) DiskLayer.Crash)]) \/
          exists a b, apply_txns_crashed_oracle_is o txn_records a b m).


Definition flush_txns_crashed_oracle_is_2 o txn_records :=
  (o = apply_txns_finished_oracle_is txn_records ++
      [OpToken
         (HorizontalComposition CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
         (Token2 CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size))
            DiskLayer.Cont);
      OpToken
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
        (Token2 CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size))
           DiskLayer.Crash)]  \/
      o = apply_txns_finished_oracle_is txn_records ++
      [OpToken
         (HorizontalComposition CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
         (Token2 CryptoOperation
            (DiskOperation addr_dec value (fun a : addr => a < disk_size))
            DiskLayer.Cont);
      OpToken
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
        (Token2 CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size))
           DiskLayer.Cont);
      LayerImplementation.Crash
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size)))] \/
    o = apply_txns_finished_oracle_is txn_records ++
         [OpToken
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
            (Token2 CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size))
               DiskLayer.Cont);
         OpToken
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
           (Token2 CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size))
              DiskLayer.Cont);
         LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)));
         OpToken
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
           (Token2 CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size))
              DiskLayer.Crash)]).

Definition flush_txns_crashed_oracle_is_3 o txn_records :=
  (o = apply_txns_finished_oracle_is txn_records ++
[OpToken
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
   (Token2 CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size))
      DiskLayer.Cont);
OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont);
LayerImplementation.Cont
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)));
OpToken CryptoDiskOperation
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont);
OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Crash)]).

Theorem flush_txns_crashed_oracle:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s' u,
    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang u o s (flush_txns txn_records log_blocks) (Crashed s') ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    ((log_rep txns s' /\ 
    (exists n m : nat,
      snd s' =
      upd_batch_set
        (list_upd_batch_set (snd s)
                            (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                            (firstn n (map data_blocks txns)))
        (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
        (firstn m (seln (map data_blocks txns) n [])) /\
        flush_txns_crashed_oracle_is_1 o txn_records m)) \/
     (log_rep txns s' /\ 
      snd s' =
      sync (list_upd_batch_set (snd s)
        (bimap get_addr_list 
        (records (current_part hdr)) (map addr_blocks txns))
        (map data_blocks txns)) /\
        flush_txns_crashed_oracle_is_2 o txn_records) \/
     (log_crash_rep (During_Apply txns) s' /\
      snd s' = 
      upd_set (sync
        (list_upd_batch_set (snd s)
          (bimap get_addr_list 
          (records (current_part hdr)) (map addr_blocks txns))
          (map data_blocks txns))) hdr_block_num
      (encode_header (update_hdr hdr header_part0)) /\
      flush_txns_crashed_oracle_is_3 o txn_records)).
Proof.
  unfold flush_txns_crashed_oracle_is_1,
  flush_txns_crashed_oracle_is_2,
  flush_txns_crashed_oracle_is_3, flush_txns; intros.
  repeat (invert_exec; split_ors; cleanup).
  { (** apply txns crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; eauto; cleanup.
    eapply apply_txns_crashed_oracle in H0; eauto.
    clear H1 H2 H3 H4.
    cleanup.
    intuition.
    left.
    split; eauto.
    eapply log_rep_update_disk_subset; eauto.
    unfold log_header_rep, log_rep_general; eauto.
    repeat cleanup_pairs; eauto.
    intuition eauto.
    do 2 eexists; intuition eauto.
  }
  { (** Sync crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished_oracle in H1; eauto; cleanup.
    clear H2 H3 H4 H5.
    invert_exec'' H1; repeat invert_exec.
    simpl in *.
    intuition.
    {
      repeat cleanup_pairs; eauto.
    }
    repeat cleanup_pairs; eauto.
    left.
    split; eauto.
    eapply log_rep_update_disk_subset with (n:= length txns)(m:= 0); simpl. 
    unfold log_header_rep, log_rep_general, log_rep_explicit; eauto.
    repeat cleanup_pairs; eauto.
    repeat cleanup_pairs; eauto.
    repeat cleanup_pairs; eauto.
    repeat rewrite firstn_oob; eauto.
    rewrite map_length; eauto.
    rewrite bimap_length, map_length; eauto.
    rewrite min_r; eauto.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
    rewrite <- H6, map_length; eauto.

    intuition eauto.

    exists (length txns), 0; simpl.
    repeat cleanup_pairs; eauto.
    split.
    repeat rewrite firstn_oob; eauto.
    rewrite map_length; eauto.
    rewrite bimap_length, min_r, map_length; eauto.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H6; repeat rewrite map_length; eauto.
    intuition eauto.
  }
  { (** update_header crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished_oracle in H1; eauto; cleanup.
    clear H3 H4 H5 H6.
    invert_exec'' H1; repeat invert_exec.
    eapply_fresh (log_rep_update_disk_subset txns hdr (length txns) 0) in H4; simpl; eauto.    
    2: unfold log_header_rep, log_rep_general; eauto.
    2: repeat cleanup_pairs; eauto.
    2: {
      repeat rewrite firstn_oob; eauto.
      rewrite map_length; eauto.
      rewrite bimap_length, map_length; eauto.
      rewrite min_r; eauto.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H13, map_length; eauto.
    }
    
    unfold update_header in *; repeat invert_exec.
    split_ors; cleanup; try invert_exec.
    { (** read_header crashed **)
      unfold read_header in *.
      repeat invert_exec.
      repeat rewrite app_length; simpl.
      split_ors; cleanup; repeat invert_exec; simpl in *;
      repeat cleanup_pairs; repeat (split; eauto); try lia;
      right; left.
      all: split; [eapply log_rep_sync_preserves in Hx|]; eauto;
      cleanup; simpl; eauto.
      all: intuition eauto.
      all: setoid_rewrite H9; simpl; lia.
    }
    { (** write_header crashed **)
      unfold read_header in *; repeat invert_exec.
      simpl in *.
      eapply log_rep_sync_preserves in Hx.
      unfold write_header in *; invert_exec'' H2;
      repeat invert_exec.
      repeat cleanup_pairs.
      repeat rewrite app_length; simpl; intuition eauto.
    }
  }
  { (** Sync crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished_oracle in H1; eauto; cleanup.
    clear H0 H5 H6 H7.
    repeat rewrite app_length; simpl.
    invert_exec'' H2; repeat invert_exec.
    eapply_fresh (log_rep_update_disk_subset txns hdr (length txns) 0) in H1; simpl; eauto.    
    apply log_rep_sync_preserves in Hx.
    unfold log_rep, log_rep_general in Hx; logic_clean; eauto.    
    eapply update_header_finished_oracle in H3; simpl in *; eauto.
    simpl in *; cleanup.
    intuition.
    right; right.
    split. 
    exists (encode_header (update_hdr (decode_header (fst x1)) header_part0)),
    (fst x1),
    (x3). 
    unfold update_hdr; rewrite encode_decode_header; simpl.
    {      
      rewrite sync_list_upd_batch_set in *.
      repeat cleanup_pairs; simpl in *.
      unfold update_hdr; simpl.
       unfold log_rep_explicit in *; logic_clean; simpl in *;
      repeat rewrite encode_decode_header in *;
      repeat rewrite map_map in *; simpl.
       
      intuition eauto.
      {
        unfold log_header_block_rep in *; simpl in *.
        rewrite upd_eq; simpl in *; intuition eauto.
        
        rewrite list_upd_batch_set_not_in in D; simpl; eauto.
        rewrite list_upd_batch_not_in in H7; unfold sync in *.
        rewrite D in *; simpl in *; cleanup; eauto.
        {
          intros.
          unfold log_header_block_rep, log_rep_inner,
          txns_valid in *; logic_clean.
          rewrite <- H19 in *.
          erewrite bimap_get_addr_list in H1; [| | | eauto]; eauto.
          apply in_map_iff in H1; logic_clean; subst.
          eapply Forall_forall in H20; eauto.
          unfold txn_well_formed in H20; logic_clean.
          intuition.
          eapply Forall_forall in H20; eauto.
          pose proof data_start_where_log_ends.
          pose proof hdr_before_log.
          lia.        
          rewrite map_length; eauto.
        }
        {
          intros.
          unfold log_header_block_rep, log_rep_inner,
          txns_valid in *; logic_clean.
          rewrite <- H19 in *.
          erewrite bimap_get_addr_list in H1; [| | | eauto]; eauto.
          apply in_map_iff in H1; logic_clean; subst.
          eapply Forall_forall in H20; eauto.
          unfold txn_well_formed in H20; logic_clean.
          intuition.
          eapply Forall_forall in H20; eauto.
          pose proof data_start_where_log_ends.
          pose proof hdr_before_log.
          lia.        
          rewrite map_length; eauto.
        }        
        
      }
      {
        unfold log_data_blocks_rep in *; cleanup; simpl in *.
        intuition.
        
        rewrite upd_ne; eauto.
      }
      lia.
      {
        unfold log_header_block_rep in *; simpl in *; cleanup; simpl; eauto.
      }
      {
        unfold log_rep_inner in *; simpl in *; cleanup.
        split.
        apply header_part0_valid.
        apply txns_valid_nil.
      }
      {
        rewrite <- H0;
        unfold log_rep_inner in *; simpl in *; logic_clean.
        intuition eauto.
      }
      {
        unfold log_header_block_rep in *; simpl in *; cleanup; simpl; eauto.
      }
    }
    {
      repeat cleanup_pairs.
      unfold log_rep_explicit, log_header_block_rep in *; simpl in *; cleanup.
      erewrite upd_set_upd_some; simpl; eauto.
      simpl; eauto.
      rewrite list_upd_batch_set_not_in in D; simpl; eauto.
      rewrite list_upd_batch_set_not_in.
      rewrite D; simpl; eauto.
      {
        intros.
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H14 in *.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; logic_clean; subst.
        eapply Forall_forall in H6; eauto.
        unfold txn_well_formed in H6; logic_clean.
        intuition.
        eapply Forall_forall in H21; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
      }
      {
        intros.
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H14 in *.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; logic_clean; subst.
        eapply Forall_forall in H6; eauto.
        unfold txn_well_formed in H6; logic_clean.
        intuition.
        eapply Forall_forall in H21; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
      }
    }
    {
      unfold log_header_rep, log_rep_general; eauto.
    }
    {
      repeat cleanup_pairs; eauto.
    }
    {
      repeat rewrite firstn_oob; eauto.
      rewrite map_length; eauto.
      rewrite bimap_length, map_length, min_r; eauto.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
      rewrite <- H13, map_length; eauto.
    }
  }
Qed.


Theorem flush_txns_crashed:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s' u,

    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang u o s (flush_txns txn_records log_blocks) (Crashed s') ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    ((log_rep txns s' /\ (exists n m : nat,
                           snd s' =
                           upd_batch_set
                             (list_upd_batch_set (snd s)
                                                 (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                                                 (firstn n (map data_blocks txns)))
                             (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
                             (firstn m (seln (map data_blocks txns) n [])))) \/
     (log_rep txns s' /\ 
      snd s' =
      sync (list_upd_batch_set (snd s)
                               (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
                               (map data_blocks txns))) \/
     (log_crash_rep (During_Apply txns) s' /\
      snd s' = upd_set (sync
                          (list_upd_batch_set (snd s)
                                              (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
                                              (map data_blocks txns))) hdr_block_num
                       (encode_header (update_hdr hdr header_part0)))).
Proof.
  intros.
  eapply flush_txns_crashed_oracle in H2; eauto.
  cleanup; intuition eauto.
  cleanup; intuition eauto.
Qed.

Definition apply_log_finished_oracle_is hdr :=
  OpToken CryptoDiskOperation
  (Token2 CryptoOperation (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont)
:: LayerImplementation.Cont CryptoDiskOperation
   :: (rec_oracle_finished_disk (count (current_part hdr)) ++
       (rec_oracle_finished_crypto (count (current_part hdr)) ++
        [LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
       [LayerImplementation.Cont
          (HorizontalComposition CryptoOperation
             (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
      flush_txns_finished_oracle_is (records (current_part hdr)).

Theorem apply_log_finished_oracle:
  forall txns hdr o s s' t u,
    log_header_rep hdr txns s ->
    exec CryptoDiskLang u o s apply_log (Finished s' t) ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    subset (snd (fst s)) (snd (fst s')) /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) 
    (map addr_list txns) (map data_blocks txns)) 
    hdr_block_num (encode_header (update_hdr hdr header_part0))) /\
    o = apply_log_finished_oracle_is hdr.
Proof.
  unfold apply_log_finished_oracle_is, apply_log; intros; invert_exec.
  unfold log_header_rep, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished_oracle in H0; eauto;
  intros; try congruence.
  simpl in *; cleanup; simpl in *.
  eapply log_rep_explicit_hash_map_subset in H; eauto.
  eapply flush_txns_finished_oracle in H1; eauto.
  cleanup.
  repeat cleanup_pairs; simpl in *; intuition eauto.
Qed.


Theorem apply_log_finished:
  forall txns hdr o s s' t u,

    log_header_rep hdr txns s ->
    exec CryptoDiskLang u o s apply_log (Finished s' t) ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    subset (snd (fst s)) (snd (fst s')) /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns)) hdr_block_num (encode_header (update_hdr hdr header_part0))).
Proof.
  intros.
  eapply apply_log_finished_oracle in H0; eauto.
  cleanup; intuition eauto.
Qed.

Definition apply_log_crashed_oracle_is_1 o hdr m :=
  (exists o', 
        o = OpToken CryptoDiskOperation
        (Token2 CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size))
           DiskLayer.Cont)
      :: LayerImplementation.Cont CryptoDiskOperation
         :: (rec_oracle_finished_disk (count (current_part hdr)) ++
             (rec_oracle_finished_crypto (count (current_part hdr)) ++
              [LayerImplementation.Cont
                 (HorizontalComposition CryptoOperation
                    (DiskOperation addr_dec value
                       (fun a : addr => a < disk_size)))]) ++
             [LayerImplementation.Cont
                (HorizontalComposition CryptoOperation
                   (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
            o' /\
            flush_txns_crashed_oracle_is_1 o' (records (current_part hdr)) m).

Definition apply_log_crashed_oracle_is_2 o hdr :=
            (exists o', 
            o = OpToken CryptoDiskOperation
            (Token2 CryptoOperation
               (DiskOperation addr_dec value (fun a : addr => a < disk_size))
               DiskLayer.Cont)
          :: LayerImplementation.Cont CryptoDiskOperation
             :: (rec_oracle_finished_disk (count (current_part hdr)) ++
                 (rec_oracle_finished_crypto (count (current_part hdr)) ++
                  [LayerImplementation.Cont
                     (HorizontalComposition CryptoOperation
                        (DiskOperation addr_dec value
                           (fun a : addr => a < disk_size)))]) ++
                 [LayerImplementation.Cont
                    (HorizontalComposition CryptoOperation
                       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++ o' /\
                flush_txns_crashed_oracle_is_2 o' (records (current_part hdr))).

Definition apply_log_crashed_oracle_is_3 o hdr :=
                (exists o', 
                o = OpToken CryptoDiskOperation
                (Token2 CryptoOperation
                   (DiskOperation addr_dec value (fun a : addr => a < disk_size))
                   DiskLayer.Cont)
              :: LayerImplementation.Cont CryptoDiskOperation
                 :: (rec_oracle_finished_disk (count (current_part hdr)) ++
                     (rec_oracle_finished_crypto (count (current_part hdr)) ++
                      [LayerImplementation.Cont
                         (HorizontalComposition CryptoOperation
                            (DiskOperation addr_dec value
                               (fun a : addr => a < disk_size)))]) ++
                     [LayerImplementation.Cont
                        (HorizontalComposition CryptoOperation
                           (DiskOperation addr_dec value (fun a : addr => a < disk_size)))]) ++
                    o' /\
                    flush_txns_crashed_oracle_is_3 o' (records (current_part hdr))).                

Theorem apply_log_crashed_oracle:
  forall txns hdr o s s' u,

    log_header_rep hdr txns s ->
    exec CryptoDiskLang u o s apply_log (Crashed s') ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    subset (snd (fst s)) (snd (fst s')) /\
    ((log_rep txns s' /\ snd s' = snd s /\
    read_encrypted_log_crashed_oracle_is o hdr Current_Part) \/
     (log_rep txns s' /\
      (exists n m : nat,
         snd s' =
         upd_batch_set
           (list_upd_batch_set (snd s)
            (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
            (firstn n (map data_blocks txns)))
           (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
           (firstn m (seln (map data_blocks txns) n [])) /\
        apply_log_crashed_oracle_is_1 o hdr m)) \/
     (log_rep txns s' /\ 
      snd s' =
      sync (list_upd_batch_set (snd s)
           (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
           (map data_blocks txns)) /\
           apply_log_crashed_oracle_is_2 o hdr) \/
     (log_crash_rep (During_Apply txns) s' /\
      snd s' = upd_set (sync
            (list_upd_batch_set (snd s)
            (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
            (map data_blocks txns))) hdr_block_num
                       (encode_header (update_hdr hdr header_part0)) /\
      apply_log_crashed_oracle_is_3 o hdr)).
Proof.
  unfold apply_log_crashed_oracle_is_1,
  apply_log_crashed_oracle_is_2,
  apply_log_crashed_oracle_is_3,
  apply_log, log_header_rep, log_rep_general; intros; cleanup.
  invert_exec; split_ors; cleanup.
  {
    eapply read_encrypted_log_crashed_oracle in H0; eauto.
    cleanup.
    intuition eauto.
    left; intuition eauto.
    
    eapply log_rep_explicit_hash_map_subset in H; eauto.
    unfold log_rep, log_rep_general; eauto.
    congruence.
  }
  {
    eapply read_encrypted_log_finished_oracle in H1; eauto; simpl in *; cleanup.
    eapply log_rep_explicit_hash_map_subset in H; eauto.
    eapply flush_txns_crashed_oracle in H2; eauto.
    repeat rewrite app_length.
    cleanup; repeat cleanup_pairs; intuition eauto; try lia.
    cleanup; right; left; intuition eauto.
    do 2 eexists; intuition eauto.
    intros; congruence.
  }
Qed.

Theorem apply_log_crashed:
  forall txns hdr o s s' u,
    log_header_rep hdr txns s ->
    exec CryptoDiskLang u o s apply_log (Crashed s') ->
    fst (fst (fst s')) = fst (fst (fst s)) /\
    subset (snd (fst (fst s))) (snd (fst (fst s'))) /\
    subset (snd (fst s)) (snd (fst s')) /\
    ((log_rep txns s' /\ snd s' = snd s) \/
     (log_rep txns s' /\
      (exists n m : nat,
         snd s' =
         upd_batch_set
           (list_upd_batch_set (snd s)
            (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
            (firstn n (map data_blocks txns)))
           (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
           (firstn m (seln (map data_blocks txns) n [])))) \/
     (log_rep txns s' /\ 
      snd s' =
      sync (list_upd_batch_set (snd s)
           (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
           (map data_blocks txns))) \/ 
     (log_crash_rep (During_Apply txns) s' /\
      snd s' = upd_set (sync
            (list_upd_batch_set (snd s)
            (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns))
            (map data_blocks txns))) hdr_block_num
                       (encode_header (update_hdr hdr header_part0)))).
Proof.
  intros.
  eapply apply_log_crashed_oracle in H0; eauto.
  cleanup; intuition eauto.
  cleanup; intuition eauto.
Qed.

Definition commit_txn_finished_oracle_is len k :=
OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value
        (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value
        (fun a : addr => a < disk_size))
     DiskLayer.Cont)
:: LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value
           (fun a : addr => a < disk_size)))
   :: OpToken
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value
              (fun a : addr => a < disk_size)))
        (Token1 CryptoOperation
           (DiskOperation addr_dec value
              (fun a : addr => a < disk_size))
           (Key k))
      :: rec_oracle_finished_crypto len ++
         rec_oracle_finished_crypto len ++
         rec_oracle_finished_disk len ++
         [OpToken
            (HorizontalComposition
               CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr =>
                   a < disk_size)))
            (Token2 CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr =>
                   a < disk_size))
               DiskLayer.Cont);
         LayerImplementation.Cont
           (HorizontalComposition
              CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr =>
                  a < disk_size)));
         OpToken
           (HorizontalComposition
              CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr =>
                  a < disk_size)))
           (Token2 CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr =>
                  a < disk_size))
              DiskLayer.Cont);
         OpToken
           (HorizontalComposition
              CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr =>
                  a < disk_size)))
           (Token2 CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr =>
                  a < disk_size))
              DiskLayer.Cont)].

Theorem commit_txn_finished_oracle:
  forall txns hdr l_addr l_data o s s' t u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit_txn l_addr l_data) (Finished s' t) ->
    exists txn,
      addr_blocks txn = l_addr /\
      data_blocks txn = l_data /\
      log_rep (txns ++ [txn]) s' /\
      (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a) /\
      exists k, o = commit_txn_finished_oracle_is (length (l_addr++l_data)) k.
Proof.
  unfold commit_txn_finished_oracle_is, 
  commit_txn, update_header, read_header, write_header;
  intros; repeat invert_exec.
  apply encrypt_all_finished_oracle in H8.
  apply hash_all_finished_oracle in H10.
  apply write_consecutive_finished_oracle in H11.
  2: rewrite seq_length; eauto.
  repeat cleanup_pairs.
  unfold log_header_rep in *; cleanup_no_match.
  
  exists (Build_txn (Build_txn_record x6 (count (current_part hdr)) (length l_addr) (length l_data))
               (firstn (length l_data) (blocks_to_addr_list l_addr))
               l_addr
               l_data).
  
  intuition eauto.

  {
    eexists; unfold log_rep_general, log_rep_explicit in *; cleanup_no_match; simpl in *.
    do 2 eexists; split; eauto.
    repeat rewrite sync_upd_comm; simpl.
    intuition.
    {
      unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
      rewrite upd_eq; eauto.
    }
    {
      unfold log_data_blocks_rep in *; cleanup_no_match; simpl in *.
      intuition.
      rewrite upd_ne.
      rewrite sync_upd_batch_set_comm; simpl.
      
      instantiate (1:= firstn (count (current_part (decode_header v0)))
                       (map (fun vs => (fst vs, [])) x0) ++ 
                       (map (fun v => (v, []))
                            (map (encrypt x6) (l_addr ++ l_data))) ++
                       skipn (length (l_addr++l_data) +
                              (count (current_part (decode_header v0))))
                              (map (fun vs => (fst vs, [])) x0)).
      repeat rewrite app_length in H.
      rewrite firstn_length_l, skipn_length in H.
      repeat rewrite map_length in *.
      
      repeat rewrite Nat.add_assoc in H.
      assume (A: (count (current_part (decode_header v0)) + length (l_addr ++ l_data) +
                  (length x0 - (length l_addr + length l_data + count (current_part (decode_header v0)))) = length x0)).
      setoid_rewrite A in H.
      clear A.
      destruct (lt_dec i (count (current_part (decode_header v0)))).
      {
        rewrite seln_app; eauto.
        rewrite upd_batch_ne.
        rewrite seln_firstn; eauto.
        unfold sync; rewrite e0.
        erewrite seln_map; eauto.
        lia.
        intros Hx; apply in_seq in Hx.
        simpl in *.
        rewrite log_start_eq in Hx; simpl in *; lia.
        rewrite firstn_length_l; eauto.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
      }
      destruct (lt_dec i (count (current_part (decode_header v0)) + length (l_addr++l_data))).
      {
        rewrite seln_app2.
        rewrite firstn_length_l.
        rewrite seln_app1.
        erewrite upd_batch_eq; eauto.
        
        rewrite seln_seq.
        rewrite log_start_eq; simpl.
        lia.
        lia.

        rewrite skipn_seq.
        
        intros Hx; apply in_seq in Hx.
        simpl in *.
        rewrite log_start_eq in Hx; simpl in *.
        inversion Hx. lia.

        repeat rewrite map_length, seq_length; eauto.
        rewrite map_length; eauto.
        rewrite seq_length; lia.
        repeat rewrite map_length; lia.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
        rewrite firstn_length_l; eauto.
        lia.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
      }
      {
        repeat rewrite seln_app2.
        rewrite firstn_length_l.
        repeat rewrite map_length.
        rewrite upd_batch_ne.
        rewrite skipn_seln.
        unfold sync.
        replace (length (l_addr ++ l_data) + count (current_part (decode_header v0)) +
                 (i - count (current_part (decode_header v0)) - length (l_addr ++ l_data))) with i by lia; eauto.
        erewrite e0, seln_map; eauto.
        lia.

        intros Hx; apply in_seq in Hx.
        rewrite log_start_eq in Hx; simpl in *.
        inversion Hx. lia.
        
        repeat rewrite map_length, seq_length; eauto.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
        rewrite firstn_length_l;
        repeat rewrite map_length; eauto.
        lia.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.

        rewrite firstn_length_l;
        repeat rewrite map_length; eauto.
        lia.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
      }
      {
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
      }
      {
        pose proof hdr_before_log.
        lia.
      }
      {
        rewrite firstn_map_comm, skipn_map_comm in H.
        apply in_app_iff in H.
        split_ors.
        apply in_map_iff in H; cleanup; eauto.
        apply in_app_iff in H.
        split_ors;
        apply in_map_iff in H; cleanup; eauto.
      }
      {
        repeat rewrite app_length.
        rewrite firstn_length_l, skipn_length.
        repeat rewrite map_length.
        
        unfold log_header_block_rep in *; simpl in *;
        cleanup_no_match; simpl in *.
        repeat rewrite app_length in *.
        setoid_rewrite e1.
        lia.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e1; eauto.
      }
    }
    {
      repeat rewrite app_length.
      rewrite firstn_length_l, skipn_length.
      repeat rewrite map_length.
      unfold log_header_block_rep in *; simpl in *;
      cleanup_no_match; simpl in *.
      repeat rewrite app_length in *.
      setoid_rewrite e1.
      lia.
      rewrite map_length; eauto.
      unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
      setoid_rewrite e1; eauto.
    }
    {
      simpl.
      rewrite encode_decode_header; simpl.
      unfold log_header_block_rep in *; simpl in *;
      cleanup_no_match; simpl in *.
      repeat rewrite app_length in *.      
      lia.
    }
    {
      simpl.
      rewrite encode_decode_header; simpl.
      rewrite upd_batch_set_ne in D.      
      unfold log_header_block_rep in *; simpl in *; cleanup_no_match; eauto.
      intros Hx; apply in_seq in Hx.
      rewrite hdr_block_num_eq, log_start_eq in Hx; 
      lia.
    }
    {
      simpl.
      rewrite encode_decode_header.
      unfold log_header_block_rep in *; simpl in *; cleanup_no_match; eauto; simpl in *.
      unfold log_rep_inner in *; simpl in *; cleanup_no_match.
      split.
      {
        unfold header_part_is_valid in *;  simpl in *; logic_clean.
        intuition eauto.
        {
          repeat rewrite map_app.
          rewrite <- firstn_map_comm.
          rewrite firstn_app.
          rewrite firstn_firstn, min_r.
          rewrite map_map; simpl.
          setoid_rewrite rolling_hash_app at 2.
          setoid_rewrite <- H.
          rewrite firstn_app2.
          repeat rewrite map_map; simpl; eauto.
          rewrite app_length, firstn_length_l;
          repeat rewrite map_length.
          lia.
          setoid_rewrite e1; eauto.
          lia.
        }
        {
          repeat rewrite map_app in *;
          repeat rewrite map_map in *; simpl in *.
          rewrite <- firstn_map_comm, map_map; 
          simpl.
          rewrite firstn_app.
          rewrite firstn_length_l.
          rewrite firstn_app2.
          rewrite firstn_oob.

          remember (match
            map (encrypt x6) l_addr ++
            map (encrypt x6) l_data
          with
          | [] => []
          | y :: tl' =>
              (hash (current_part (decode_header v0)), y)
              :: combine
                   (rolling_hash_list
                      (hash (current_part (decode_header v0)))
                      (map (encrypt x6) l_addr ++
                       map (encrypt x6) l_data)) tl'
          end).

          
          eapply hashes_in_hashmap_app.
          eapply hashes_in_hashmap_subset; eauto.
          eapply upd_batch_consistent_subset; eauto.
          setoid_rewrite <- H.
          subst; eapply hashes_in_hashmap_upd; eauto.

          all: try rewrite firstn_length_l; repeat rewrite app_length;
          repeat rewrite map_length; try lia.
          all: setoid_rewrite e1; lia.
        }
        {
          repeat rewrite app_length in *; eauto.
        }
        {
          rewrite map_app, fold_left_app; simpl.
          lia.
        }
        {
          apply records_are_consecutive_starting_from_app_one; eauto.          
        }
      }
      {
        unfold txns_valid in *; simpl in *; cleanup_no_match.
        intuition eauto.
        repeat rewrite map_app; simpl;
        rewrite H7; eauto.

        apply Forall_app; eauto.
        {
          eapply Forall_impl; [|eauto]. 
          unfold txn_well_formed, record_is_valid; intros; logic_clean.
          intuition eauto.
          {
            right; eauto.
          }
          {
            simpl; lia.
          }            
          {
            rewrite H10.
            repeat rewrite map_app.
            repeat rewrite skipn_app_l.
            rewrite firstn_app_l.
            rewrite firstn_map_comm, map_map; simpl.
            rewrite <- firstn_map_comm.
            setoid_rewrite firstn_skipn_comm at 2.
            rewrite firstn_firstn, min_l.
            setoid_rewrite <- firstn_skipn_comm; eauto.
            lia.
            rewrite skipn_length, map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e1; lia.
            rewrite map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e1; lia.
          }
          {
            rewrite H11.
            repeat rewrite map_app.
            repeat rewrite skipn_app_l.
            rewrite firstn_app_l.
            rewrite firstn_map_comm, map_map; simpl.
            rewrite <- firstn_map_comm.
            setoid_rewrite firstn_skipn_comm at 2.
            rewrite firstn_firstn, min_l.
            setoid_rewrite <- firstn_skipn_comm; eauto.
            lia.
            rewrite skipn_length, map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e1; lia.
            rewrite map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e1; lia.
          }
          {
            eapply upd_batch_consistent_some; eauto.
          }
          {
            eapply upd_batch_consistent_some; eauto.
          }
        }
        {
          unfold txn_well_formed; simpl.
          repeat rewrite map_app.
          repeat rewrite map_map; simpl.
          intuition.
          {
            unfold record_is_valid; simpl; intuition eauto.
            lia.
          }
          {
            rewrite skipn_app_eq.
            rewrite firstn_app_l.
            rewrite firstn_app_l.
            rewrite firstn_oob; eauto.
            rewrite map_length; eauto.
            rewrite map_length; eauto.
            rewrite app_length, map_length; lia.
            rewrite map_length, firstn_length_l; eauto.
            rewrite map_length;
            setoid_rewrite e1; lia.
          }
          {
            rewrite skipn_app_r_ge.
            rewrite map_length, firstn_length_l.
            rewrite skipn_app_l.
            rewrite skipn_app_r_ge.
            rewrite map_length.
            replace (length l_addr + 
            count (current_part (decode_header v0)) 
            - count (current_part (decode_header v0)) 
            - length l_addr) with 0 by lia; simpl.
            rewrite firstn_app_l.
            rewrite firstn_oob; eauto.
            rewrite map_length; eauto.
            rewrite map_length; eauto.
            rewrite map_length; lia.
            rewrite app_length, map_length; lia.
            rewrite map_length;
            setoid_rewrite e1; lia.
            rewrite map_length, firstn_length_l; eauto.
            lia.
            rewrite map_length;
            setoid_rewrite e1; lia.
          }
          {
            rewrite Mem.upd_batch_app.
            rewrite consistent_with_upds_upd_batch_swap.
            {
              eapply in_seln in H9.
              eapply (in_split_last value_dec) in H9; logic_clean.
              rewrite H9 at 1 2.
              repeat rewrite map_app; simpl.
              rewrite Mem.upd_batch_app; simpl.
              rewrite Mem.upd_batch_ne; eauto.
              rewrite Mem.upd_eq; eauto.
              intros Hx; apply in_map_iff in Hx; logic_clean.
              apply encrypt_ext in H11; subst; eauto.
              repeat rewrite map_length; eauto.
            }
            repeat rewrite map_app in *; eauto.
            all: repeat rewrite map_length; eauto.
          }
          {
            rewrite Mem.upd_batch_app.
            {
              eapply in_seln in H9.
              eapply (in_split_last value_dec) in H9; logic_clean.
              rewrite H9 at 1 2.
              repeat rewrite map_app; simpl.
              rewrite Mem.upd_batch_app; simpl.
              rewrite Mem.upd_batch_ne; eauto.
              rewrite Mem.upd_eq; eauto.
              intros Hx; apply in_map_iff in Hx; logic_clean.
              apply encrypt_ext in H11; subst; eauto.
              repeat rewrite map_length; eauto.
            }
            repeat rewrite map_length; eauto.
          }
        }
      }
    }
  }
  {
    rewrite sync_upd_comm; simpl.
    rewrite upd_ne; eauto.
    rewrite sync_upd_batch_set_comm; eauto.
    rewrite upd_batch_ne; eauto.
    intros Hx; apply in_seq in Hx.
    unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; cleanup_no_match;
    simpl in *.
    rewrite map_length in *.
    pose proof data_start_where_log_ends.
    lia.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
  }
  {
    repeat rewrite seq_length, map_length; eauto.
  }
  Unshelve.
  {
    unfold log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; simpl in *; cleanup_no_match;
    simpl in *.
    repeat rewrite map_app in *.
    rewrite app_length in *.
    lia.
  }
  eauto.
Qed.


Theorem commit_txn_finished:
  forall txns hdr l_addr l_data o s s' t u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->

    exec CryptoDiskLang u o s (commit_txn l_addr l_data) (Finished s' t) ->
    exists txn,
      addr_blocks txn = l_addr /\
      data_blocks txn = l_data /\
      log_rep (txns ++ [txn]) s' /\
      (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a).
Proof.
  intros.
  eapply commit_txn_finished_oracle in H5; eauto.
  cleanup; intuition eauto.
Qed.


Arguments log_crash_rep : simpl never.

Definition commit_txn_crashed_oracle_is_1 o len :=
(o  = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size))
       DiskLayer.Crash)] \/ 
    o = [OpToken
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value
             (fun a : addr => a < disk_size)))
       (Token2 CryptoOperation
          (DiskOperation addr_dec value
             (fun a : addr => a < disk_size))
          DiskLayer.Cont);
    LayerImplementation.Crash
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value
            (fun a : addr => a < disk_size)))] \/ 
    o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size))
       DiskLayer.Cont);
 LayerImplementation.Cont
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value
         (fun a : addr => a < disk_size)));
 OpToken
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value
         (fun a : addr => a < disk_size)))
   (Token1 CryptoOperation
      (DiskOperation addr_dec value
         (fun a : addr => a < disk_size))
      Crash)] \/ 
    (exists k o' n,
    o = OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size))
       DiskLayer.Cont)
      :: LayerImplementation.Cont
          (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value
                (fun a : addr => a < disk_size)))
        :: OpToken
              (HorizontalComposition CryptoOperation
                (DiskOperation addr_dec value
                    (fun a : addr => a < disk_size)))
              (Token1 CryptoOperation
                (DiskOperation addr_dec value
                    (fun a : addr => a < disk_size))
                (Key k)) :: o' /\
      batch_operations_crypto_crashed_oracle_is o' n len) \/
  (exists k o' n,
    o = OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size))
       DiskLayer.Cont)
      :: LayerImplementation.Cont
          (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value
                (fun a : addr => a < disk_size)))
        :: OpToken
              (HorizontalComposition CryptoOperation
                (DiskOperation addr_dec value
                    (fun a : addr => a < disk_size)))
              (Token1 CryptoOperation
                (DiskOperation addr_dec value
                    (fun a : addr => a < disk_size))
                (Key k)) :: rec_oracle_finished_crypto len ++ o' /\
      batch_operations_crypto_crashed_oracle_is o' n len)).

Definition commit_txn_crashed_oracle_is_2 o len := 
  (exists k o' n,
     o = OpToken
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value
           (fun a : addr => a < disk_size)))
     (Token2 CryptoOperation
        (DiskOperation addr_dec value
           (fun a : addr => a < disk_size))
        DiskLayer.Cont)
       :: LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                 (fun a : addr => a < disk_size)))
         :: OpToken
               (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value
                     (fun a : addr => a < disk_size)))
               (Token1 CryptoOperation
                 (DiskOperation addr_dec value
                     (fun a : addr => a < disk_size))
                 (Key k)) :: rec_oracle_finished_crypto len ++ 
                 rec_oracle_finished_crypto len ++ o' /\
       (batch_operations_disk_crashed_oracle_is o' n len \/
       o' = rec_oracle_finished_disk len ++
      [OpToken
         (HorizontalComposition
            CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size)))
         (Token2 CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size))
            DiskLayer.Crash)] \/
      o' = rec_oracle_finished_disk len ++
      [OpToken
         (HorizontalComposition
            CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size)))
         (Token2 CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size))
            DiskLayer.Cont)] ++
      [LayerImplementation.Crash
         (HorizontalComposition
            CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size)))] \/
      o' = rec_oracle_finished_disk len ++
      [OpToken
         (HorizontalComposition
            CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size)))
         (Token2 CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size))
            DiskLayer.Cont)] ++
      [LayerImplementation.Cont
         (HorizontalComposition
            CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size)))] ++
      [OpToken CryptoDiskOperation
         (Token2 CryptoOperation
            (DiskOperation addr_dec value
               (fun a : addr => a < disk_size))
            DiskLayer.Crash)])).



  Definition commit_txn_crashed_oracle_is_3 o len :=  
    exists k,
    o =           
            OpToken
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr => a < disk_size)))
            (Token2 CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr => a < disk_size))
               DiskLayer.Cont)
          :: LayerImplementation.Cont
               (HorizontalComposition CryptoOperation
                  (DiskOperation addr_dec value
                     (fun a : addr => a < disk_size)))
             :: OpToken
                  (HorizontalComposition CryptoOperation
                     (DiskOperation addr_dec value
                        (fun a : addr => a < disk_size)))
                  (Token1 CryptoOperation
                     (DiskOperation addr_dec value
                        (fun a : addr => a < disk_size))
                     (Key k))
                :: rec_oracle_finished_crypto len ++
                   rec_oracle_finished_crypto len ++
                   rec_oracle_finished_disk len ++
                   [OpToken
                      (HorizontalComposition
                         CryptoOperation
                         (DiskOperation addr_dec value
                            (fun a : addr =>
                             a < disk_size)))
                      (Token2 CryptoOperation
                         (DiskOperation addr_dec value
                            (fun a : addr =>
                             a < disk_size))
                         DiskLayer.Cont);
                   LayerImplementation.Cont
                     (HorizontalComposition
                        CryptoOperation
                        (DiskOperation addr_dec value
                           (fun a : addr =>
                            a < disk_size)));
                   OpToken CryptoDiskOperation
                     (Token2 CryptoOperation
                        (DiskOperation addr_dec value
                           (fun a : addr =>
                            a < disk_size))
                        DiskLayer.Cont);
                   OpToken CryptoDiskOperation
                     (Token2 CryptoOperation
                        (DiskOperation addr_dec value
                           (fun a : addr =>
                            a < disk_size))
                        DiskLayer.Crash)].

Theorem commit_txn_crashed_oracle:
  forall txns hdr l_addr l_data o s s' u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit_txn l_addr l_data) (Crashed s') ->
    (log_rep txns s' /\ snd s' = snd s /\ 
    commit_txn_crashed_oracle_is_1 o (length (l_addr++l_data))) \/
    (log_crash_rep (During_Commit_Log_Write txns) s' /\
     (forall a, a >= data_start -> (snd s') a = (snd s) a) /\
     commit_txn_crashed_oracle_is_2 o (length (l_addr++l_data))) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_crash_rep (During_Commit_Header_Write txns (txns ++ [txn])) s' /\
       (exists new_hdr, (snd s') hdr_block_num = (Log.encode_header new_hdr, [Log.encode_header hdr]) /\
       new_hdr <> hdr) /\
       (forall a, a >= data_start -> (snd s') a = (snd s) a) /\
       commit_txn_crashed_oracle_is_3 o (length (l_addr++l_data))).
Proof.
  unfold commit_txn_crashed_oracle_is_1, 
  commit_txn_crashed_oracle_is_2,
  commit_txn_crashed_oracle_is_3,
  commit_txn, read_header;
  intros; repeat invert_exec.
  split_ors; cleanup; repeat invert_exec.
  { (** read_header crashed **)
    split_ors; cleanup; repeat invert_exec.
    { (** Read crashed **)
      left; unfold log_rep, log_header_rep; simpl; intuition eauto.
      repeat cleanup_pairs; eauto.
    }
    {(** Ret crashed **)
      repeat cleanup_pairs;
      left; unfold log_rep, log_header_rep; simpl; intuition eauto.
    }
  }  
  repeat cleanup_pairs; simpl in *;
  split_ors; cleanup; repeat invert_exec.
  { (** GetKey crashed **)
    left; unfold log_rep, log_header_rep; simpl; intuition eauto.
  }
  simpl in *;
  split_ors; cleanup; repeat invert_exec.
  {(** encrypt_all crashed **)
    eapply encrypt_all_crashed_oracle in H6; cleanup.
    simpl in *; cleanup.
    repeat cleanup_pairs;
    left; unfold log_rep, log_header_rep in *; simpl; intuition eauto.
    unfold log_rep_general, log_rep_explicit in *; simpl in *; cleanup.
    do 3 eexists; intuition eauto.
    unfold log_rep_inner in *; simpl in *; cleanup.
    intuition eauto.
    unfold txns_valid in *; simpl in *; cleanup; intuition eauto.
    eapply Forall_impl; [|eauto].
    unfold txn_well_formed, record_is_valid; intros; cleanup;
    intuition eauto.
    right; eauto.
    {
      eapply upd_batch_consistent_some; eauto.
    }
    {
      eapply upd_batch_consistent_some; eauto.
    }
  }
  apply encrypt_all_finished_oracle in H7.
  repeat cleanup_pairs; simpl in *;
  split_ors; cleanup; repeat invert_exec.
  {(** hash_all crashed **)
    eapply hash_all_crashed_oracle in H6; cleanup.
    repeat cleanup_pairs;
    left; unfold log_rep, log_header_rep in *; simpl; intuition eauto.
    exists hdr.
    unfold log_rep_general, log_rep_explicit in *; simpl in *.
    cleanup_no_match; do 2 eexists; intuition eauto.
    {
      unfold log_rep_inner in *; simpl in *; cleanup_no_match.
      intuition eauto.
      {
        unfold header_part_is_valid in *; simpl in *; logic_clean.
        intuition eauto.
        eapply hashes_in_hashmap_subset; eauto.
        eapply upd_batch_consistent_subset; eauto.
      }
      {
        unfold txns_valid in *; simpl in *; logic_clean.
        intuition eauto.
        eapply Forall_impl; [| eauto].
        unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean.
        intuition eauto.
        {
          eapply upd_batch_consistent_some; eauto.
        }
        {
          eapply upd_batch_consistent_some; eauto.
        }
      }
    }
    rewrite map_length in *; intuition eauto.
  }
  apply hash_all_finished_oracle in H8.
  repeat cleanup_pairs; simpl in *;
  split_ors; cleanup_no_match; repeat invert_exec_no_match.
  {(** write_consecutive crashed **)
    eapply write_consecutive_crashed_oracle in H6; cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    right; left.
    intuition eauto.
    {
      unfold log_header_rep, log_rep_general, log_rep_explicit in *; simpl; logic_clean.
      unfold log_crash_rep; simpl.
      exists x1, (firstn (count (current_part hdr)) x2),
      (bimap (fun v vs => (v, fst vs::snd vs)) (firstn x (map (encrypt x0) (l_addr++l_data))) (firstn x (skipn (count (current_part hdr)) x2)) ++ skipn (x + (count (current_part hdr))) x2).
      simpl in *.
      intuition eauto.
      {
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        intuition eauto.
        rewrite upd_batch_set_ne; eauto.
        intros Hx; apply in_firstn_in in Hx.
        apply in_seq in Hx.
        rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
      }
      {
        unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
        intuition eauto.
        rewrite firstn_length_l in H.
        rewrite upd_batch_set_ne; eauto.
        rewrite seln_firstn; eauto.
        apply H11; eauto.
        all: try lia.
        
        rewrite seq_length in H6.
        rewrite firstn_seq, min_l.
        intros Hx; apply in_seq in Hx.
        rewrite log_start_eq in Hx; simpl in *.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        simpl in *; lia.
        eauto.
        apply in_firstn_in in H; eauto.        
        rewrite firstn_length_l; lia.
      }
      {        
        unfold log_header_block_rep,
        log_data_blocks_rep in *;
        simpl in *; cleanup_no_match; simpl in *.
        intuition eauto.
        repeat rewrite app_length in *.
        rewrite bimap_length, min_l in H.
        do 2 rewrite firstn_length_l in H.
        rewrite skipn_length in H.
        rewrite seq_length, map_length, app_length in H6.
        
        replace (count (current_part (decode_header v)) +
                 (x + (length x2 - (x + count (current_part (decode_header v)))))) with (length x2) in H by lia.

        destruct (lt_dec i (count (current_part (decode_header v)))).
        {(** first_part of log **) 
          rewrite upd_batch_set_ne; eauto.
          rewrite seln_app; eauto.
          rewrite seln_firstn; eauto.
          apply H11; eauto.
          all: try lia.
          repeat constructor; eauto.
          rewrite firstn_length_l; lia.

          intros Hx; apply in_firstn_in, in_seq in Hx.
          rewrite log_start_eq in Hx; simpl in *; lia.
        }
        destruct (lt_dec i (x + count (current_part (decode_header v)))).
        {(** overwritten part of the log **)
          rewrite firstn_seq, min_l.
          erewrite upd_batch_set_seq_in.
          rewrite seln_app2.
          rewrite seln_app.

          erewrite seln_bimap; simpl; auto.
          repeat rewrite firstn_length_l; eauto.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
          repeat rewrite firstn_length_l; try lia.
          rewrite map_length, app_length; lia.
          rewrite bimap_length, min_l.
          repeat rewrite firstn_length_l; try lia.
          rewrite map_length, app_length; lia.
          repeat rewrite firstn_length_l; eauto.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
          repeat rewrite firstn_length_l; lia.
          
          rewrite seln_firstn.
          rewrite skipn_seln.
          rewrite firstn_length_l.
          replace (count (current_part (decode_header v)) + (i - count (current_part (decode_header v)))) with i by lia.
          apply H11; eauto.
          all: try lia.
          repeat constructor; eauto.
          rewrite firstn_length_l; lia.
          rewrite log_start_eq, firstn_length_l; lia.
          rewrite firstn_length_l; lia.
          rewrite firstn_length_l; eauto.
          rewrite map_length, app_length; lia.
          rewrite map_length, app_length; lia.
        }
        {(** last part of log **) 
          rewrite upd_batch_set_ne; eauto.
          repeat rewrite seln_app2; eauto.
          rewrite bimap_length, min_l.
          repeat rewrite firstn_length_l.
          rewrite skipn_seln; eauto.
          replace (x + count (current_part (decode_header v)) + (i - count (current_part (decode_header v)) - x)) with i by lia.          
          apply H11; eauto.
          all: try lia.
          repeat constructor; eauto.
          rewrite map_length, app_length; lia.
          repeat rewrite firstn_length_l; try lia.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
          rewrite bimap_length, min_l.
          repeat rewrite firstn_length_l; try lia.
          rewrite map_length, app_length; lia.
          repeat rewrite firstn_length_l; eauto.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
          
          rewrite firstn_length_l; lia.
          repeat constructor; eauto.
          
          rewrite firstn_seq, min_l.
          intros Hx; apply in_seq in Hx.
          rewrite log_start_eq in Hx; simpl in *; lia.
          rewrite map_length, app_length; lia.          
        }
        all: rewrite seq_length in H6; eauto.
        lia.
        lia.        
        repeat rewrite firstn_length_l; eauto.
        rewrite skipn_length.
        rewrite map_length, app_length in H6; lia.
        {
          apply in_app_iff in H; split_ors.
          {
            apply in_firstn_in in H.
            rewrite H19; eauto.
          }
          apply in_app_iff in H; split_ors.
          {
            rewrite bimap_combine_map in H.
            apply in_map_iff in H; cleanup_no_match.
            simpl.
            destruct x1; simpl; eapply in_combine_r in H10.
            apply in_firstn_in in H10.
            apply in_skipn_in in H10.
            rewrite H19; eauto.
          }
          {
            apply in_skipn_in in H.
            rewrite H19; eauto.
          }
        }
        {
          repeat rewrite map_length in *;
          repeat rewrite app_length in *.
          rewrite bimap_length, min_l.
          repeat rewrite firstn_length_l.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
          lia.
          repeat rewrite firstn_length_l; eauto.
          rewrite skipn_length; lia.
          rewrite map_length, app_length; lia.
        }
      }
      {
        rewrite seq_length in H6.
        repeat rewrite map_length in *;
        repeat rewrite app_length in *.
        rewrite bimap_length, min_l.
        repeat rewrite firstn_length_l.
        rewrite skipn_length; lia.
        rewrite map_length, app_length; lia.
        lia.
        repeat rewrite firstn_length_l; eauto.
        rewrite skipn_length; lia.
        rewrite map_length, app_length; lia.
      }
      {
        unfold log_header_block_rep in *; logic_clean; subst; eauto.
      }
      {
        unfold log_header_block_rep in *; logic_clean; subst; eauto.
      }
      {
        rewrite seq_length in H6.
        repeat rewrite map_length in *;
        repeat rewrite app_length in *.
        repeat rewrite firstn_length_l.
        unfold log_header_block_rep in *; logic_clean; subst; eauto.
        lia.
      }
      {
        unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
        split.
        {
          unfold header_part_is_valid in *; simpl in *; logic_clean; simpl in *.
          intuition eauto.
          rewrite map_app.
          rewrite firstn_app2.
          rewrite <- firstn_map_comm; eauto.
          rewrite map_length, firstn_length_l; lia.
          eapply hashes_in_hashmap_subset.
          
          rewrite map_app.
          rewrite firstn_app2.
          rewrite <- firstn_map_comm; eauto.
          rewrite map_length, firstn_length_l; lia.
          apply upd_batch_consistent_subset; eauto.
        }
        {
          unfold txns_valid in *;
          simpl in *; logic_clean; simpl in *.
          rewrite <- H in *.
          intuition eauto.
          eapply Forall_impl; [| eauto].
          
          unfold txn_well_formed, record_is_valid; intros; logic_clean.
          simpl in *; intuition eauto.

          rewrite <- skipn_firstn_comm.
          rewrite map_app.
          rewrite firstn_app_l.
          rewrite <- firstn_map_comm; eauto.
          rewrite firstn_firstn, min_l.
          rewrite skipn_firstn_comm; eauto.
          lia.
          rewrite map_length, firstn_length_l; lia.

          rewrite <- skipn_firstn_comm.
          rewrite map_app.
          rewrite firstn_app_l.
          rewrite <- firstn_map_comm; eauto.
          rewrite firstn_firstn, min_l.
          rewrite skipn_firstn_comm; eauto.
          lia.
          rewrite map_length, firstn_length_l; lia.
          {
            eapply upd_batch_consistent_some; eauto.
          }
          {
            eapply upd_batch_consistent_some; eauto.
          }
        }
      }
    }
    {
      apply upd_batch_set_ne.
      intros Hx; apply in_firstn_in, in_seq in Hx.
      pose proof data_start_where_log_ends.
      unfold log_header_rep, log_rep_general,
      log_rep_explicit, log_header_block_rep in *;
      simpl in *; cleanup_no_match; simpl in *.
      rewrite map_length, log_start_eq in *.
      lia.
    }
    {
      repeat rewrite seq_length, map_length in *; 
      intuition eauto.
      do 3 eexists; intuition eauto.
    }
    {
      apply seq_length.
    }
  }
  apply write_consecutive_finished_oracle in H9.
  2: apply seq_length.
  simpl in *; logic_clean; repeat cleanup_pairs; simpl in *.
  split_ors; cleanup_no_match; repeat invert_exec_no_match.
  {
    eapply update_header_crashed_oracle in H9; eauto; subst.
    {
      right; left.
      cleanup_no_match.
      split.
      {
        clear H10.
        unfold log_header_rep, log_rep_general, log_rep_explicit in *; simpl; logic_clean.
        unfold log_crash_rep; simpl.
          exists x, (firstn (count (current_part hdr)) x2),
          (bimap (fun v vs => (v, fst vs::snd vs)) (map (encrypt x0) (l_addr++l_data)) 
          (firstn (length (l_addr++l_data)) (skipn (count (current_part hdr)) x2)) ++ 
          skipn (length (l_addr++l_data) + (count (current_part hdr))) x2).
          simpl in *.
          intuition eauto.
          {
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            setoid_rewrite upd_batch_set_ne; eauto.
            intros Hx;
            apply in_seq in Hx.
            rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
          }
          {
            unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite firstn_length_l in H.
            setoid_rewrite upd_batch_set_ne; eauto.
            rewrite seln_firstn; eauto.
            apply H10; eauto.
            all: try lia.
            intros Hx; apply in_seq in Hx.
            rewrite log_start_eq in Hx; simpl in *.
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            simpl in *; lia.
            eauto.
            apply in_firstn_in in H; eauto.        
            rewrite firstn_length_l; lia.
          }
          {
            
            unfold log_header_block_rep, log_data_blocks_rep in *; simpl in *; cleanup_no_match; simpl in *.
            intuition eauto.
            repeat rewrite app_length in *.
            rewrite bimap_length, min_l in H.
            rewrite firstn_length_l in H.
            rewrite skipn_length in H.
            repeat rewrite map_length, app_length in H.
            
            replace (count (current_part (decode_header v)) +
      (length l_addr + length l_data +
       (length x2 - (length l_addr + length l_data + count (current_part (decode_header v)))))) with (length x2) in H by lia.

            destruct (lt_dec i (count (current_part (decode_header v)))).
            {(** first_part of log **) 
              rewrite upd_batch_set_ne; eauto.
              rewrite seln_app; eauto.
              rewrite seln_firstn; eauto.
              apply H10; eauto.
              all: try lia.
              repeat constructor; eauto.
              rewrite firstn_length_l; lia.
              
              intros Hx; apply in_seq in Hx.
              rewrite log_start_eq in Hx; simpl in *; lia.
            }
            destruct (lt_dec i (length (l_addr++l_data) + count (current_part (decode_header v)))).
            {(** overwritten part of the log **)
              erewrite upd_batch_set_seq_in.
              rewrite seln_app2.
              rewrite seln_app.

              erewrite seln_bimap; simpl; auto.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length; lia.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length; lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
             
              rewrite skipn_length; lia.
              repeat rewrite firstn_length_l; lia.
              
              rewrite seln_firstn.
              rewrite skipn_seln.
              rewrite firstn_length_l.
              replace (count (current_part (decode_header v)) + (i - count (current_part (decode_header v)))) with i by lia.
              apply H10; eauto.
              all: try lia.
              repeat constructor; eauto.
              rewrite app_length in *;
              rewrite firstn_length_l; lia.
              rewrite log_start_eq, firstn_length_l; lia.
              
              rewrite firstn_length_l; eauto.
              rewrite map_length, app_length in *; lia.
              rewrite map_length, app_length in *; lia.
            } 
            {(** last part of log **) 
              rewrite upd_batch_set_ne; eauto.
              repeat rewrite seln_app2; eauto.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_seln; eauto.
              rewrite map_length, app_length in *.
              replace (length l_addr + length l_data + count (current_part (decode_header v)) +
        (i - count (current_part (decode_header v)) - (length l_addr + length l_data)))  with i by lia.          
              apply H10; eauto.
              all: try lia.
              repeat constructor; eauto.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length, app_length in *; lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.              
              rewrite skipn_length; lia.
              rewrite firstn_length_l; lia.
              
              intros Hx; apply in_seq in Hx.              
              rewrite map_length, app_length in *;
              rewrite log_start_eq in Hx; simpl in *; lia.         
            }
            lia.    
            repeat rewrite firstn_length_l; eauto.            
            rewrite map_length, app_length; lia.
            rewrite skipn_length; lia.
            {
              apply in_app_iff in H; split_ors.
              {
                apply in_firstn_in in H.
                rewrite H17; eauto.
              }
              apply in_app_iff in H; split_ors.
              {
                rewrite bimap_combine_map in H.
                apply in_map_iff in H; cleanup_no_match.
                simpl.
                destruct x; simpl; eapply in_combine_r in H9.
                apply in_firstn_in in H9.
                apply in_skipn_in in H9.
                rewrite H17; eauto.
              }
              {
                apply in_skipn_in in H.
                rewrite H17; eauto.
              }
            }
            {
              repeat rewrite map_length in *;
              repeat rewrite app_length in *.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_length;
              rewrite map_length, app_length; lia.
              lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
            }
          }
          
          {
            repeat rewrite map_length in *;
            repeat rewrite app_length in *.
            rewrite bimap_length, min_l.
            repeat rewrite firstn_length_l.
            rewrite skipn_length;
            rewrite map_length, app_length; lia.
            lia.
            repeat rewrite firstn_length_l; eauto.
            rewrite map_length, app_length; lia.
            rewrite skipn_length; lia.
          }
          {
            unfold log_header_block_rep in *; logic_clean; subst; eauto.
          }
          {
            unfold log_header_block_rep in *; logic_clean; subst; eauto.
          }
          {
            repeat rewrite map_length in *;
            repeat rewrite app_length in *.
            repeat rewrite firstn_length_l.
            unfold log_header_block_rep in *; logic_clean; subst; eauto.
            lia.
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
            split.
            {
              unfold header_part_is_valid in *; simpl in *; logic_clean; simpl in *.
              intuition eauto.
              rewrite map_app.
              rewrite firstn_app2.
              rewrite <- firstn_map_comm; eauto.
              rewrite map_length, firstn_length_l; lia.
              eapply hashes_in_hashmap_subset.
              
              rewrite map_app.
              rewrite firstn_app2.
              rewrite <- firstn_map_comm; eauto.
              rewrite map_length, firstn_length_l; lia.
              apply upd_batch_consistent_subset; eauto.
            }
            {
              unfold txns_valid in *;
              simpl in *; logic_clean; simpl in *.
              rewrite <- H in *.
              intuition eauto.
              eapply Forall_impl; [| eauto].
              
              unfold txn_well_formed, record_is_valid; intros; logic_clean.
              simpl in *; intuition eauto.

              rewrite <- skipn_firstn_comm.
              rewrite map_app.
              rewrite firstn_app_l.
              rewrite <- firstn_map_comm; eauto.
              rewrite firstn_firstn, min_l.
              rewrite skipn_firstn_comm; eauto.
              lia.
              rewrite map_length, firstn_length_l; lia.

              rewrite <- skipn_firstn_comm.
              rewrite map_app.
              rewrite firstn_app_l.
              rewrite <- firstn_map_comm; eauto.
              rewrite firstn_firstn, min_l.
              rewrite skipn_firstn_comm; eauto.
              lia.
              rewrite map_length, firstn_length_l; lia.
              {
                eapply upd_batch_consistent_some; eauto.
              }
              {
                eapply upd_batch_consistent_some; eauto.
              }
            }
          }
        }
        split.
        {
          clear H10; simpl.
          intuition eauto.
          eapply upd_batch_set_ne.
          intros Hx; apply in_seq in Hx.
          pose proof data_start_where_log_ends.
          unfold log_header_rep, log_rep_general,
          log_rep_explicit, log_header_block_rep in *;
          simpl in *; cleanup_no_match; simpl in *.
          rewrite map_length, log_start_eq in *.
          lia.
        }
        {
          repeat rewrite seq_length, map_length.
          do 3 eexists; intuition eauto;
          cleanup_no_match; intuition eauto.
        }
    }
  }
  {
    eapply update_header_finished_oracle in H10; eauto.
    right; right.
    cleanup_no_match; repeat cleanup_pairs.
    exists (Build_txn {|
           key := x0;
           start := count (current_part (decode_header v0));
           addr_count := length l_addr;
           data_count := length l_data |}
                 (firstn (length l_data) (blocks_to_addr_list l_addr))
                 l_addr l_data).
    simpl.
    intuition eauto.

    {
      unfold log_header_rep, log_rep_general,
      log_rep_explicit in *; cleanup_no_match.
      unfold log_crash_rep; simpl.
      exists v0, (encode_header
           (update_hdr (decode_header v0)
              {|
              hash := rolling_hash (hash (current_part (decode_header v0)))
                        (map (encrypt x0) (l_addr ++ l_data));
              count := count (current_part (decode_header v0)) + (length l_addr + length l_data);
              records := records (current_part (decode_header v0)) ++
                         [{|
                          key := x0;
                          start := count (current_part (decode_header v0));
                          addr_count := length l_addr;
                          data_count := length l_data |}] |})).

      rewrite encode_decode_header; simpl.
      exists (firstn (count (current_part (decode_header (fst x)))) x1),
      (bimap (fun v vs => (v, fst vs::snd vs)) (map (encrypt x0) (l_addr++l_data))
             (firstn (length (l_addr++l_data)) (skipn (count (current_part (decode_header (fst x)))) x1)) ++
             skipn (length (l_addr++l_data) + (count (current_part (decode_header (fst x))))) x1).
          simpl in *.
          intuition eauto.
          {
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite upd_eq; simpl; eauto.
            simpl in *; subst; eauto.
            rewrite upd_batch_set_ne in D0;
            cleanup_no_match; simpl; eauto.

            intros Hx; apply in_seq in Hx.
            rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.
          }
          {
            unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite firstn_length_l in H18.
            rewrite upd_ne.
            rewrite upd_batch_set_ne; eauto.
            rewrite seln_firstn; eauto.
            apply H; eauto.
            all: try lia.
            
            intros Hx; apply in_seq in Hx.
            rewrite log_start_eq in Hx; simpl in *.
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            simpl in *; lia.
            rewrite log_start_eq, hdr_block_num_eq; lia.
            apply in_firstn_in in H18; eauto.        
            rewrite firstn_length_l; lia.
          }
          { 
            unfold log_header_block_rep, log_data_blocks_rep in *;
            simpl in *; cleanup_no_match; simpl in *.
            intuition eauto.
            
            rewrite upd_batch_set_ne in D0;
            cleanup_no_match; simpl; eauto.
            
            repeat rewrite app_length in *.
            rewrite bimap_length, min_l in H9.
            rewrite firstn_length_l in H9.
            rewrite skipn_length in H9.
            repeat rewrite map_length, app_length in H9.
            
            replace (count (current_part (decode_header v0)) +
        (length l_addr + length l_data +
         (length x1 - (length l_addr + length l_data + count (current_part (decode_header v0)))))) with (length x1) in H7 by lia.
            rewrite upd_ne.
            destruct (lt_dec i (count (current_part (decode_header v0)))).
            {(** first_part of log **) 
              rewrite upd_batch_set_ne; eauto.
              rewrite seln_app; eauto.
              rewrite seln_firstn; eauto.
              apply H; eauto.
              all: try lia.
              repeat constructor; eauto.
              rewrite firstn_length_l; lia.

              intros Hx; apply in_seq in Hx.
              rewrite log_start_eq in Hx; simpl in *; lia.
            }
            destruct (lt_dec i (length (l_addr++l_data) + count (current_part (decode_header v0)))).
            {(** overwritten part of the log **)
              erewrite upd_batch_set_seq_in.
              rewrite seln_app2.
              rewrite seln_app.

              erewrite seln_bimap; simpl; auto.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length; lia.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length; lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
             
              rewrite skipn_length; lia.
              repeat rewrite firstn_length_l; lia.

              rewrite seln_firstn.
              rewrite skipn_seln.
              rewrite firstn_length_l.
              replace (count (current_part (decode_header v0)) + (i - count (current_part (decode_header v0)))) with i by lia.
              apply H; eauto.
              all: try lia.
              repeat constructor; eauto.
              rewrite app_length in *;
              rewrite firstn_length_l; lia.
              rewrite log_start_eq, firstn_length_l; lia.
              
              rewrite firstn_length_l; eauto.
              rewrite map_length, app_length in *; lia.
              rewrite map_length, app_length in *; lia.
            }
            {(** last part of log **) 
              rewrite upd_batch_set_ne; eauto.
              repeat rewrite seln_app2; eauto.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_seln; eauto.
              rewrite map_length, app_length in *.
              replace (length l_addr + length l_data + count (current_part (decode_header v0)) +
        (i - count (current_part (decode_header v0)) - (length l_addr + length l_data)))  with i by lia.          
              apply H; eauto.
              all: try lia.
              repeat constructor; eauto.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l; try lia.
              rewrite map_length, app_length in *; lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.              
              rewrite skipn_length; lia.  
              rewrite firstn_length_l; lia.
              
              intros Hx; apply in_seq in Hx.              
              rewrite map_length, app_length in *;
              rewrite log_start_eq in Hx; simpl in *; lia.         
            }
            rewrite log_start_eq, hdr_block_num_eq; lia.
            lia.    
            repeat rewrite firstn_length_l; eauto.            
            rewrite map_length, app_length; lia.
            rewrite skipn_length; lia.
            {
              intros Hx; apply in_seq in Hx.              
              rewrite map_length, app_length in *;
              rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.
            }
            {
              apply in_app_iff in H9; split_ors.
              {
                apply in_firstn_in in H9.
                rewrite H10; eauto.
              }
              apply in_app_iff in H9; split_ors.
              {
                rewrite bimap_combine_map in H9.
                apply in_map_iff in H9; cleanup_no_match.
                simpl.
                destruct x; simpl; eapply in_combine_r in H19.
                apply in_firstn_in in H19.
                apply in_skipn_in in H19.
                rewrite H10; eauto.
              }
              {
                apply in_skipn_in in H9.
                rewrite H10; eauto.
              }
            }
            {
              repeat rewrite map_length in *;
              repeat rewrite app_length in *.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_length;
              rewrite map_length, app_length; lia.
              lia.
              repeat rewrite firstn_length_l; eauto.
              rewrite map_length, app_length; lia.
              rewrite skipn_length; lia.
            }
          }
          
          {
            repeat rewrite map_length in *;
            repeat rewrite app_length in *.
            rewrite bimap_length, min_l.
            repeat rewrite firstn_length_l.
            rewrite skipn_length;
            rewrite map_length, app_length; lia.
            lia.
            repeat rewrite firstn_length_l; eauto.
            rewrite map_length, app_length; lia.
            rewrite skipn_length; lia.
          }
          {
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; rewrite app_length in *;
            lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.    
          }
          {
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.            
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; rewrite app_length in *;
            lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.
          }
          {
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.
            
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; rewrite app_length in *;
            lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.
          }
          {
            repeat rewrite map_length in *;
            repeat rewrite app_length in *.
            repeat rewrite firstn_length_l.            
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.
            
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq, log_start_eq in Hx; simpl in *; lia.
                        
            unfold log_header_block_rep in *; logic_clean; subst; eauto.
            lia.
          }
          {
            unfold log_rep_inner in *; simpl in *; logic_clean.
            unfold log_header_block_rep in *; logic_clean; subst; eauto.
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            split.
            { 
              unfold header_part_is_valid in *; simpl in *;
              logic_clean; simpl in *.
              intuition eauto.
              repeat rewrite map_app.
              rewrite firstn_app.
              rewrite map_length, firstn_length_l.
              rewrite D in *; simpl in *.
              replace (count (current_part (decode_header v0)) + (length l_addr + length l_data) -
        count (current_part (decode_header v0))) with (length l_addr + length l_data) by lia.
              rewrite <- firstn_map_comm; eauto.
              rewrite firstn_firstn, min_r by lia.
              rewrite firstn_app2.
              repeat rewrite rolling_hash_app.
              rewrite bimap_combine_map, map_map; simpl.
              rewrite map_fst_combine.
              rewrite H, rolling_hash_app; eauto.
              rewrite app_length, map_length,
              firstn_length_l, app_length.
              rewrite map_length; eauto.
              rewrite skipn_length; lia.
              rewrite map_length, bimap_length, min_l.
              rewrite app_length;
              repeat rewrite map_length; eauto.
              rewrite firstn_length_l.
              repeat rewrite app_length;
              repeat rewrite map_length; eauto.
              rewrite skipn_length; lia.
              lia.              
              eapply hashes_in_hashmap_subset.
              
              repeat rewrite map_app.
              rewrite firstn_app_le.
              rewrite firstn_app2.
              {
                repeat rewrite <- firstn_map_comm.
                eapply hashes_in_hashmap_app.
                eapply hashes_in_hashmap_subset.
                eauto.
                eapply upd_batch_consistent_subset; eauto.
                rewrite bimap_combine_map.
                rewrite map_map; simpl.
                rewrite map_fst_combine.
                rewrite <- map_app.
                setoid_rewrite <- H.
                rewrite D; simpl.
                subst; eapply hashes_in_hashmap_upd; eauto.
      
                all: try rewrite firstn_length_l; repeat rewrite app_length;
                repeat rewrite map_length; try lia.
                rewrite skipn_length. rewrite app_length in *.
                setoid_rewrite H11; lia.
              }

              repeat rewrite map_length;
              rewrite bimap_length, min_l.
              rewrite D in *; simpl in *.
              rewrite app_length;
              repeat rewrite map_length;
              rewrite firstn_length_l; lia.
              rewrite firstn_length_l.
              repeat rewrite app_length;
              repeat rewrite map_length; eauto.
              rewrite skipn_length; lia.
              rewrite D in *; simpl in *.
              rewrite map_length, firstn_length_l; lia.
              eauto.
              rewrite D in *; simpl in *.
              rewrite app_length in *; lia.
              {
                rewrite D in *; simpl in *.
                rewrite map_app; simpl; rewrite fold_left_app; simpl.            
                lia.
              }
              {
                rewrite D in *; simpl in *; eauto.
                eapply records_are_consecutive_starting_from_app_one; 
                simpl; eauto.
              }              
            }
            {
              simpl in *; 
              rewrite D in *; simpl in *.
              unfold txns_valid in *;
              simpl in *; logic_clean; simpl in *.
              rewrite <- H9 in *.
              intuition eauto.
              {
                rewrite map_app; simpl; eauto.
              }
              {
                apply Forall_app.
                {
                  eapply Forall_impl; [| eauto].
                  
                  unfold txn_well_formed, record_is_valid; intros; logic_clean.
                  simpl in *; intuition eauto.
                  lia.
                  
                  rewrite <- skipn_firstn_comm.
                  rewrite map_app.
                  rewrite firstn_app_l.
                  rewrite <- firstn_map_comm; eauto.
                  rewrite firstn_firstn, min_l.
                  rewrite skipn_firstn_comm; eauto.
                  lia.
                  rewrite map_length, firstn_length_l; lia.
                  
                  rewrite <- skipn_firstn_comm.
                  rewrite map_app.
                  rewrite firstn_app_l.
                  rewrite <- firstn_map_comm; eauto.
                  rewrite firstn_firstn, min_l.
                  rewrite skipn_firstn_comm; eauto.
                  lia.
                  rewrite map_length, firstn_length_l; lia.
                  {
                    eapply upd_batch_consistent_some; eauto.
                  }
                  {
                    eapply upd_batch_consistent_some; eauto.
                  }
                }
                {
                  unfold txn_well_formed, record_is_valid;
                  simpl; intuition eauto; try lia.
                  {
                    repeat rewrite map_app.
                    rewrite skipn_app_eq.
                    rewrite bimap_combine_map.
                    rewrite map_map; simpl.
                    rewrite map_fst_combine.
                    rewrite <- app_assoc.
                    rewrite firstn_app2; eauto.
                    rewrite map_length; eauto.
                    
                    rewrite firstn_length_l.
                    repeat rewrite app_length;
                    repeat rewrite map_length; eauto.
                    rewrite skipn_length; lia.
                    rewrite map_length, firstn_length_l; lia.
                  }
                  {
                    repeat rewrite map_app.
                    rewrite skipn_app_r_ge.
                    rewrite bimap_combine_map.
                    rewrite map_map; simpl.
                    rewrite map_fst_combine.
                    rewrite <- app_assoc.
                    rewrite skipn_app_eq.
                    rewrite firstn_app2; eauto.
                    rewrite map_length; eauto.

                    repeat rewrite map_length.                    
                    rewrite firstn_length_l; lia.
                    rewrite firstn_length_l.
                    repeat rewrite app_length;
                    repeat rewrite map_length; eauto.
                    rewrite skipn_length; lia.
                    rewrite map_length, firstn_length_l; lia.
                  }
                  {
                    repeat rewrite map_app in *.
                    rewrite Mem.upd_batch_app.
            rewrite consistent_with_upds_upd_batch_swap.
            {
              eapply in_seln in H18.
              eapply (in_split_last value_dec) in H18; logic_clean.
              rewrite H18 at 1 2.
              repeat rewrite map_app; simpl.
              rewrite Mem.upd_batch_app; simpl.
              rewrite Mem.upd_batch_ne; eauto.
              rewrite Mem.upd_eq; eauto.
              intros Hx; apply in_map_iff in Hx; logic_clean.
              apply encrypt_ext in H20; subst; eauto.
              repeat rewrite map_length; eauto.
            }
            repeat rewrite map_app in *; eauto.
            all: repeat rewrite map_length; eauto.
          }
          {
            repeat rewrite map_app in *.
            rewrite Mem.upd_batch_app.
            {
              eapply in_seln in H18.
              eapply (in_split_last value_dec) in H18; logic_clean.
              rewrite H18 at 1 2.
              repeat rewrite map_app; simpl.
              rewrite Mem.upd_batch_app; simpl.
              rewrite Mem.upd_batch_ne; eauto.
              rewrite Mem.upd_eq; eauto.
              intros Hx; apply in_map_iff in Hx; logic_clean.
              apply encrypt_ext in H20; subst; eauto.
              repeat rewrite map_length; eauto.
            }
            repeat rewrite map_length; eauto.
          }
                }
              }
            }
            {
              intros Hx; apply in_seq in Hx.
              rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
            }
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; simpl in *.
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            split.
            { 
              unfold header_part_is_valid in *; simpl in *;
              logic_clean; simpl in *.
              intuition eauto.
              repeat rewrite map_app.
              rewrite firstn_app2.
              rewrite <- firstn_map_comm; eauto.
              
              rewrite map_length,
              firstn_length_l; eauto; lia.
              repeat rewrite map_app.
              rewrite firstn_app2.
              rewrite <- firstn_map_comm.
              eapply hashes_in_hashmap_subset; eauto.
              apply upd_batch_consistent_subset; eauto.
              repeat rewrite <- map_app; eauto.
              rewrite map_length,
              firstn_length_l; eauto; lia.
            }
            {
              unfold txns_valid in *;
              simpl in *; logic_clean; simpl in *.
              rewrite <- H9 in *.
              intuition eauto.
              {
                eapply Forall_impl; [| eauto].
                
                unfold txn_well_formed, record_is_valid; intros; logic_clean.
                simpl in *; intuition eauto.
                  
                rewrite <- skipn_firstn_comm.
                rewrite map_app.
                rewrite firstn_app_l.
                rewrite <- firstn_map_comm; eauto.
                rewrite firstn_firstn, min_l.
                rewrite skipn_firstn_comm; eauto.
                lia.
                rewrite map_length, firstn_length_l; lia.
                
                rewrite <- skipn_firstn_comm.
                rewrite map_app.
                rewrite firstn_app_l.
                rewrite <- firstn_map_comm; eauto.
                rewrite firstn_firstn, min_l.
                rewrite skipn_firstn_comm; eauto.
                lia.
                rewrite map_length, firstn_length_l; lia.
                eapply upd_batch_consistent_some; eauto.
                eapply upd_batch_consistent_some; eauto.
              }
            }
            {
              intros Hx; apply in_seq in Hx.
              rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
            }              
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; simpl in *.
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            2: {
              intros Hx; apply in_seq in Hx.
              rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
            }
            rewrite app_length in *.      
            rewrite seln_app2, seln_app1.
            erewrite seln_bimap; simpl.
            erewrite seln_firstn.
            erewrite skipn_seln.
            replace (count (current_part (decode_header v0)) +
            (i -
             length
               (firstn
                  (count
                     (current_part (decode_header v0)))
                  x1))) with i.
            unfold log_data_blocks_rep in *; cleanup_no_match.
            erewrite e1; simpl; eauto.
            eapply in_seln.
            all: try lia.
            all: rewrite firstn_length_l; try lia.
            rewrite map_length, app_length; eauto.
            rewrite skipn_length; lia.
            rewrite map_length, app_length; lia.
            rewrite bimap_length, min_l.
            rewrite map_length, app_length; lia.
            rewrite map_length, app_length, firstn_length_l; try lia.
            rewrite skipn_length; lia.
          }
          {
            rewrite firstn_length_l by lia.
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; simpl in *.
            rewrite upd_batch_set_ne in D0; cleanup_no_match; eauto.
            
            intros Hx; apply in_seq in Hx.
            rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
          }
    }
    {
      rewrite upd_eq; eauto; simpl.
      unfold log_rep_inner in *; simpl in *; cleanup_no_match; simpl in *.
      unfold log_header_block_rep in *; simpl in *;
      cleanup_no_match; subst; simpl in *.
      rewrite upd_batch_set_ne in D0; cleanup_no_match.
      2: {
        intros Hx; apply in_seq in Hx.
        rewrite hdr_block_num_eq, log_start_eq in Hx; lia.
      }
      unfold log_header_rep, log_rep_general, log_rep_explicit,
      log_header_block_rep in *; simpl in *; cleanup_no_match; simpl in *.
      rewrite decode_encode_header.
      destruct l1; simpl in *; try congruence; eauto.
      eexists; intuition eauto.
      unfold update_hdr in *.
      destruct (decode_header v0); cleanup_no_match; simpl in *.
      inversion H.
      destruct old_part; simpl in *.
      inversion H18.
      assert (length (records ++
      [{|
       key := x0;
       start := count + (length l_addr + length l_data);
       addr_count := length l_addr;
       data_count := length l_data |}]) <> length records). {
         rewrite app_length; simpl; lia.
       }
       rewrite H21 in H9; eauto.
    }
    {
      unfold log_header_rep, log_rep_general, log_rep_explicit,
      log_header_block_rep in *; simpl in *; cleanup_no_match; simpl in *.
      rewrite upd_ne.
      rewrite upd_batch_set_ne; eauto.
      {
        intros Hx; apply in_seq in Hx.
        pose proof data_start_where_log_ends.
        rewrite map_length, app_length in *;
        simpl in *; lia.
      }
      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
      }
    }
    {
      repeat rewrite seq_length, map_length in *.
      intuition eauto.
    }
  }
  Unshelve.
  all: repeat constructor; eauto.
Qed.

Theorem commit_txn_crashed:
  forall txns hdr l_addr l_data o s s' u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit_txn l_addr l_data) (Crashed s') ->
    (log_rep txns s' /\ snd s' = snd s) \/
    (log_crash_rep (During_Commit_Log_Write txns) s' /\
     (forall a, a >= data_start -> (snd s') a = (snd s) a)) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_crash_rep (During_Commit_Header_Write txns (txns ++ [txn])) s' /\
       (forall a, a >= data_start -> (snd s') a = (snd s) a)).
Proof.
  intros.
  eapply commit_txn_crashed_oracle in H5; eauto.
  intuition eauto.
  right; right; cleanup; intuition eauto.
Qed.

Definition commit_finished_oracle_is_true o len:=
  exists k, o = OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont)
:: LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
   :: commit_txn_finished_oracle_is len
        k ++ [LayerImplementation.Cont CryptoDiskOperation].

Theorem commit_finished_oracle:
  forall txns l_addr l_data hdr o s s' t u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 -> 
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit l_addr l_data) (Finished s' t) ->
    (exists txn,
       t = true /\
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_rep (txns ++ [txn]) s' /\
       (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a) /\
       commit_finished_oracle_is_true o (length (l_addr ++ l_data))  /\
       count (current_part hdr) + length (l_addr ++ l_data) <= log_length) \/
    (t = false /\ s' = s /\ 
    count (current_part hdr) + length (l_addr ++ l_data) > log_length /\
    o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation (DiskOperation addr_dec value (fun a : addr => a < disk_size))
       DiskLayer.Cont);
 LayerImplementation.Cont
   (HorizontalComposition CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size)));
 LayerImplementation.Cont CryptoDiskOperation]).
Proof.
  unfold commit_finished_oracle_is_true,
  commit, read_header; intros.
  repeat invert_exec.
  right; repeat cleanup_pairs; eauto.
  {
    intuition eauto.
    unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *.
    rewrite app_length;    
    apply Nat.ltb_lt; eauto.
  }
  repeat cleanup_pairs.
  eapply commit_txn_finished_oracle in H6; eauto.
  logic_clean; left; eexists; intuition eauto.
  cleanup.
  {
    unfold commit_txn_finished_oracle_is; 
    repeat rewrite <- app_assoc; 
    simpl; eexists; 
    repeat rewrite <- app_assoc; simpl; intuition eauto.
  }
  unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *.
  simpl in *; cleanup; simpl; rewrite app_length; eauto.
  apply Nat.ltb_ge; eauto.
  unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *.
  simpl in *; cleanup; simpl; rewrite app_length; eauto.
  apply Nat.ltb_ge; eauto.
Qed.

Theorem commit_finished:
  forall txns l_addr l_data hdr o s s' t u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit l_addr l_data) (Finished s' t) ->
    (exists txn,
       t = true /\
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_rep (txns ++ [txn]) s' /\
       (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a)) \/
    (t = false /\ s' = s /\ count (current_part hdr) + length (l_addr ++ l_data) > log_length).
Proof.
  intros.
  eapply commit_finished_oracle in H4; eauto.
  intuition eauto; cleanup; intuition eauto.
  left; eexists; intuition eauto.
Qed.



Lemma records_are_consecutive_starting_from_app_one_rev:
forall (l1 : list txn_record) (n : nat) (r : txn_record),
records_are_consecutive_starting_from n (l1 ++ [r]) ->
records_are_consecutive_starting_from n l1 /\
start r =
fold_left Nat.add
(map (fun rec : txn_record => addr_count rec + data_count rec) l1) n.
Proof.
induction l1; simpl; intros; try solve [intuition eauto].
cleanup.
apply IHl1 in H0; cleanup; eauto.
intuition eauto.
rewrite Nat.add_assoc; eauto.
Qed.

Definition commit_crashed_oracle_is_1 o len :=
  (o = [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value
          (fun a : addr => a < disk_size))
       DiskLayer.Crash)] \/ 
      o = [OpToken
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value
             (fun a : addr => a < disk_size)))
       (Token2 CryptoOperation
          (DiskOperation addr_dec value
             (fun a : addr => a < disk_size))
          DiskLayer.Cont);
    LayerImplementation.Crash
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value
            (fun a : addr => a < disk_size)))] \/
      o = [OpToken
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr => a < disk_size)))
            (Token2 CryptoOperation
               (DiskOperation addr_dec value
                  (fun a : addr => a < disk_size))
               DiskLayer.Cont);
         LayerImplementation.Cont
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value
                 (fun a : addr => a < disk_size)));
         LayerImplementation.Crash
           CryptoDiskOperation] \/
           (exists o',
           o = OpToken
           (HorizontalComposition CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
           (Token2 CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size))
              DiskLayer.Cont)
         :: LayerImplementation.Cont
              (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value (fun a : addr => a < disk_size))) :: o' /\
                 commit_txn_crashed_oracle_is_1 o' len)).

Definition commit_crashed_oracle_is_2 o len :=
  (exists o', o = OpToken
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
     (Token2 CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size))
        DiskLayer.Cont)
   :: LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size))) :: o' /\
           commit_txn_crashed_oracle_is_2 o' len).

Definition commit_crashed_oracle_is_3 o len :=
  (exists o', o = OpToken
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
     (Token2 CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size))
        DiskLayer.Cont)
   :: LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a : addr => a < disk_size))) :: o' /\
           commit_txn_crashed_oracle_is_3 o' len).

Definition commit_crashed_oracle_is_4 o len :=
  (exists k, o = OpToken
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
  (Token2 CryptoOperation
     (DiskOperation addr_dec value (fun a : addr => a < disk_size))
     DiskLayer.Cont)
:: LayerImplementation.Cont
     (HorizontalComposition CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size)))
   :: commit_txn_finished_oracle_is len k ++ 
   [LayerImplementation.Crash CryptoDiskOperation]).

Theorem commit_crashed_oracle:
  forall hdr txns l_addr l_data o s s' u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit l_addr l_data) (Crashed s') ->
    (log_rep txns s' /\ snd s' = snd s /\  
    commit_crashed_oracle_is_1 o (length (l_addr++l_data))) \/
    (log_crash_rep (During_Commit_Log_Write txns) s' /\
     (forall a, a >= data_start -> (snd s') a = (snd s) a) /\
     commit_crashed_oracle_is_2 o (length (l_addr++l_data)) /\
     count (current_part hdr) + length l_addr + length l_data <= log_length) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_crash_rep (During_Commit_Header_Write txns (txns ++ [txn])) s' /\
       (exists new_hdr, (snd s') hdr_block_num = (Log.encode_header new_hdr, [Log.encode_header hdr]) /\
       new_hdr <> hdr) /\
       (forall a, a >= data_start -> (snd s') a = (snd s) a) /\
       commit_crashed_oracle_is_3 o  (length (l_addr++l_data)) /\
       count (current_part hdr) + length l_addr + length l_data <= log_length /\
       (forall i : nat,
          i < length l_addr + length l_data ->
          fst ((snd s') (log_start + Log.count (Log.current_part hdr) + i)) =
          seln (map (encrypt (key (record txn))) (l_addr ++ l_data)) i value0 /\
          length (snd ((snd s') (log_start + Log.count (Log.current_part hdr) + i))) = 1)) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_rep (txns ++ [txn]) s' /\
       (forall a, a >= data_start -> (snd s') a = sync (snd s) a) /\
       commit_crashed_oracle_is_4 o (length (l_addr++l_data)) /\
       count (current_part hdr) + length l_addr + length l_data <= log_length).
Proof.
  unfold commit_crashed_oracle_is_1,
  commit_crashed_oracle_is_2,
  commit_crashed_oracle_is_3,
  commit_crashed_oracle_is_4,
  commit, read_header; simpl; intros.
  repeat invert_exec.
  split_ors; cleanup; repeat invert_exec; eauto.
  {(** read_header crashed **)
    split_ors; cleanup; repeat invert_exec; simpl; left;
    intuition eauto; try lia.
    all: unfold log_rep; eauto.
  }
  {(** read_header crashed **)
    unfold log_rep; simpl; left; intuition eauto; try lia.
  }
  eapply Nat.ltb_ge in D.
  split_ors; cleanup; repeat invert_exec; eauto.
  {(** commit_txn_crashed **) 
    unfold log_rep in *; cleanup.
    eapply commit_txn_crashed_oracle in H5; eauto.
    intuition eauto.
    simpl; left; intuition eauto; try lia.

    simpl; right.
    unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *.
    intuition eauto; try lia.
    
    simpl; right; right; left; eauto.
    unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *.
    eexists; do 6 (split; eauto); try lia.
    split; eauto; try lia.
    {
      simpl in *.
      intros; unfold log_crash_rep, log_data_blocks_rep,
      log_rep_inner, txns_valid, txn_well_formed in *; logic_clean.
      apply forall_app_l in H32.
      inversion H32; cleanup.
      destruct (lt_dec i (length (addr_blocks x))).
      {
        rewrite map_app.
      rewrite seln_app1.
      rewrite H45.
      setoid_rewrite H12.
      rewrite seln_app2.
      rewrite map_app.
      replace (start (record x)) with 
      (length (map fst x5)).
      rewrite skipn_app.
      rewrite seln_firstn.
      assert (A: (((fix add (n m : nat) {struct n} : nat :=
      match n with
      | 0 => m
      | S p => S (add p m)
      end)
     (count (current_part (decode_header (fst (snd s hdr_block_num))))) i -
      length x5) = i)). {
        unfold log_header_block_rep in *; simpl in *;
      cleanup.
      unfold header_part_is_valid in *; simpl in *; cleanup.
      apply Minus.minus_plus.
      }
      setoid_rewrite A.
      erewrite seln_map.
      split; eauto.
      rewrite <- A.
      fold PeanoNat.Nat.add.
      erewrite <- seln_app2.
      eapply H27.
      simpl in *.
      unfold log_header_block_rep in *; simpl in *;
      cleanup.
      unfold header_part_is_valid in *; simpl in *; cleanup.
      lia.
      unfold header_part_is_valid in *; simpl in *; cleanup.
      rewrite <- H31, <- H37.
      repeat rewrite map_app; simpl.
      erewrite fold_left_app.
      simpl.
      lia.
      unfold header_part_is_valid in *; simpl in *; cleanup.
      lia.
      {
        unfold header_part_is_valid in *; simpl in *; cleanup.
        repeat rewrite app_length in *.
        replace (length x6) with (log_length - length x5) by lia.
        rewrite H28.
        lia.
      }
      eauto.
      {
        rewrite map_length.
        unfold header_part_is_valid in *; simpl in *; cleanup.
        rewrite <- H31 in *.
        rewrite map_app in *; simpl in *.
        unfold record_is_valid in *; simpl in *.
        rewrite map_app in *; simpl in *.
        eapply records_are_consecutive_starting_from_app_one_rev in H55; 
        destruct H55; setoid_rewrite H28; rewrite <- H37; eauto.
      }
      {
        unfold header_part_is_valid in *; simpl in *; cleanup.
        fold Nat.add; lia.
      }
      {
        unfold header_part_is_valid in *; simpl in *; cleanup.
        fold Nat.add; lia.
      }
      {
        unfold header_part_is_valid in *; simpl in *; cleanup.
        fold Nat.add; lia.
      }
      rewrite map_length; eauto.
      }
      {
        apply Nat.nlt_ge in n.
        rewrite map_app.
        rewrite seln_app2.
        rewrite H46.
        fold Nat.add in *.
        setoid_rewrite H12.
        all: fold Nat.add in *.
        rewrite seln_app2.
        rewrite map_app.
        replace (start (record x)) with 
        (length (map fst x5)).
        rewrite skipn_app_r_ge.
        assert (a: length (addr_blocks x) + length (map fst x5) - length (map fst x5) = length (addr_blocks x)) by lia.
        setoid_rewrite a.
        rewrite seln_firstn.
        assert (A: ((count (current_part (decode_header (fst (snd s hdr_block_num)))) + i -
        length x5) = i)). {
          unfold log_header_block_rep in *; simpl in *;
          cleanup.
          unfold header_part_is_valid in *; simpl in *; cleanup.
          apply Minus.minus_plus.
        }
        setoid_rewrite A.
        all: repeat rewrite map_length.
        rewrite skipn_seln.
        erewrite seln_map.
        replace (length (addr_blocks x) + (i - length (addr_blocks x))) with i by lia.
        split; eauto.
        rewrite <- A.
        erewrite <- seln_app2.
        eapply H27.
        simpl in *.
        unfold log_header_block_rep in *; simpl in *;
        cleanup.
        unfold header_part_is_valid in *; simpl in *; cleanup.
        lia.
        unfold header_part_is_valid in *; simpl in *; cleanup.
        rewrite <- H31, <- H37.
        repeat rewrite map_app; simpl.
        erewrite fold_left_app.
        simpl.
        lia.
        unfold header_part_is_valid in *; simpl in *; cleanup.
        lia.
        {
          unfold header_part_is_valid in *; simpl in *; cleanup.
          repeat rewrite app_length in *.
          replace (length x6) with (log_length - length x5) by lia.
          rewrite H28.
          lia.
        }
        lia.
        remember (length x5) as c; 
        remember (length (addr_blocks x)) as c1;
        setoid_rewrite <- Heqc; lia.
        {
          unfold header_part_is_valid in *; simpl in *; cleanup.
          rewrite <- H31 in *.
          rewrite map_app in *; simpl in *.
          unfold record_is_valid in *; simpl in *.
          rewrite map_app in *; simpl in *.
          eapply records_are_consecutive_starting_from_app_one_rev in H55; 
          destruct H55; setoid_rewrite H28; rewrite <- H37; eauto.
        }
        {
          unfold header_part_is_valid in *; simpl in *; cleanup.
          lia.
        }
        {
          unfold header_part_is_valid in *; simpl in *; cleanup.
          lia.
        }
        {
          unfold header_part_is_valid in *; simpl in *; cleanup.
          lia.
        }
        eauto.
      }
    }
    { 
      rewrite app_length;
      unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
      simpl in *; cleanup; simpl in *; lia.
    }
  }
  {
    unfold log_rep in *; cleanup.
    eapply commit_txn_finished_oracle in H6; eauto.
    intuition eauto.
    simpl; right; right; right; intuition eauto; try lia.
    cleanup; eexists; intuition eauto.
    eexists; intuition eauto.
    unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *; lia.
    rewrite app_length;
    unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *; lia.
  }
Qed.

Theorem commit_crashed:
  forall txns l_addr l_data o s s' u,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_rep txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    length l_addr > 0 ->
    length l_data > 0 ->
    
    exec CryptoDiskLang u o s (commit l_addr l_data) (Crashed s') ->
    (log_rep txns s' /\ snd s' = snd s) \/
    (log_crash_rep (During_Commit_Log_Write txns) s' /\
     (forall a, a >= data_start -> (snd s') a = (snd s) a)) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_crash_rep (During_Commit_Header_Write txns (txns ++ [txn])) s' /\
       (forall a, a >= data_start -> (snd s') a = (snd s) a)) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_rep (txns ++ [txn]) s' /\
       (forall a, a >= data_start -> (snd s') a = sync (snd s) a)).
Proof.
  intros.
  unfold log_rep in *; cleanup. 
  eapply commit_crashed_oracle in H5; eauto.
  intuition eauto; cleanup; eauto.
Qed.

Theorem recover_finished:
  forall o s txns s' r u,
    log_reboot_rep txns s ->
    exec CryptoDiskLang u o s recover (Finished s' r) ->
    log_rep txns s' /\
    r = combine (map addr_list txns) (map data_blocks txns) /\
    (forall a, a >= data_start -> snd s' a = sync (snd s) a).
Proof.
  unfold log_reboot_rep, log_rep; intros; cleanup.
  unfold recover, write_header in *.
  repeat invert_exec; cleanup_no_match.
  {
    eapply read_encrypted_log_finished in H0; eauto.
    cleanup_no_match; simpl in *.
    {
      repeat cleanup_pairs.
      eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
      eapply decrypt_txns_finished in H3; eauto.
      clear H0 H2 H4 H5.
      cleanup_no_match; repeat cleanup_pairs.

      unfold log_rep_general, log_rep_explicit in *; cleanup.
      split.
      do 3 eexists; do 2 split; simpl.  
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite sync_upd_comm; simpl.
        rewrite upd_eq; eauto.
      }
      
      instantiate (1:= map (fun vs => (fst vs, [])) x2).
      simpl in *.
      rewrite encode_decode_header; simpl.
      rewrite map_length; intuition eauto.
      {
        unfold log_data_blocks_rep in *; cleanup; simpl in *; intuition eauto.

        {
          rewrite map_length in H11.
          rewrite sync_upd_comm; simpl.
          rewrite upd_ne.
          unfold sync; erewrite seln_map. 
          rewrite H; eauto.
          rewrite <- H3; eauto.
          lia.
          pose proof hdr_before_log.
          lia.
        }
        {
          apply in_map_iff in H11; cleanup; simpl; eauto.
        }
        {
          rewrite map_length, <- H3; eauto.
        }
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D in *; simpl in *; eauto.
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D in *; simpl in *; eauto.
      }
      {
        rewrite map_map; simpl.
        unfold log_rep_inner in *; cleanup_no_match; simpl in *.
        unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
        rewrite D in *; simpl in *; eauto.
        intuition eauto.
        {
          eapply header_part_is_valid_subset; eauto.
        }
        eapply txns_valid_subset; eauto.
      }
      {
        split.
        unfold log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H7.
        erewrite bimap_get_addr_list.
        eauto.
        3: eauto.
        destruct x1; eauto.
        rewrite map_length; eauto.
        simpl.
        intros.
        rewrite sync_upd_comm; simpl.
        rewrite upd_ne; eauto.
        pose proof hdr_before_log.
        pose proof data_start_where_log_ends.
        lia.
      }
      {
        unfold log_rep_general, log_rep_explicit in *; cleanup.
        split.
        do 3 eexists; do 2 split; simpl.  
        {
          unfold log_header_block_rep in *; cleanup; simpl in *.
          rewrite sync_upd_comm; simpl.
          rewrite upd_eq; eauto.
        }
      
        instantiate (1:= map (fun vs => (fst vs, [])) x2).
        simpl in *.
        rewrite encode_decode_header; simpl.
        rewrite map_length; intuition eauto.
        {
          unfold log_data_blocks_rep in *; cleanup; simpl in *; intuition eauto.
          
          {
            rewrite map_length in H11.
            rewrite sync_upd_comm; simpl.
            rewrite upd_ne.
            unfold sync; erewrite seln_map. 
            rewrite H1; eauto.
            rewrite <- H3; eauto.
            lia.
            pose proof hdr_before_log.
            lia.
          }
        {
          apply in_map_iff in H11; cleanup; simpl; eauto.
        }
        {
          rewrite map_length, <- H3; eauto.
        }
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D in *; simpl in *; eauto.
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D in *; simpl in *; eauto.
      }
      {
        rewrite map_map; simpl.
        unfold log_rep_inner in *; cleanup_no_match; simpl in *.
        unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
        rewrite D in *; simpl in *; eauto.
        intuition eauto.
        {
          eapply header_part_is_valid_subset; eauto.
        }
        eapply txns_valid_subset; eauto.
      }
      {
        split.
        unfold log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H7.
        erewrite bimap_get_addr_list.
        eauto.
        3: eauto.
        destruct x1; eauto.
        rewrite map_length; eauto.
        simpl.
        intros.
        rewrite sync_upd_comm; simpl.
        rewrite upd_ne; eauto.
        pose proof hdr_before_log.
        pose proof data_start_where_log_ends.
        lia.
      }

      }
    }
  }
Qed.

Theorem recover_crashed:
  forall o s txns s' u,
    log_reboot_rep txns s ->
    exec CryptoDiskLang u o s recover (Crashed s') ->
    (log_reboot_rep txns s' /\
      (forall a, a >= data_start -> snd s' a = snd s a)) \/
     (log_crash_rep (During_Recovery txns) s' /\
      (forall a, a >= data_start -> snd s' a = snd s a)) \/
     (log_rep txns s' /\
      (forall a, a >= data_start -> snd s' a = sync (snd s) a)) .
Proof.
  unfold log_reboot_rep, recover; intros; cleanup.
  repeat invert_exec_no_match; cleanup_no_match; eauto.
  split_ors; cleanup_no_match.
  {
    eapply read_encrypted_log_crashed in H0; eauto.
    cleanup; eauto.
    left; split; eauto.
    do 4 eexists; eauto.
    {
      unfold log_rep_explicit in *; cleanup; intuition eauto.
      {
        unfold log_header_block_rep in *; cleanup; eauto.
      }
      {
        unfold log_data_blocks_rep in *; cleanup; eauto.
      }
      {
        unfold log_rep_inner in *; logic_clean; intuition eauto.
        eapply header_part_is_valid_subset; eauto; cleanup; eauto.
        cleanup; eauto.
      }
    }
  }
  {
    eapply read_encrypted_log_finished in H2; eauto.
    cleanup_no_match; simpl in *; try congruence.
    {
      unfold write_header in *.
      invert_exec_no_match; split_ors; cleanup_no_match; repeat invert_exec_no_match.
      {
        {
          repeat cleanup_pairs; eauto.
          left; split; eauto.
          do 4 eexists; eauto.
          {
            unfold log_rep_explicit in *; cleanup; intuition eauto.
            unfold log_rep_inner in *; logic_clean; intuition eauto.
            eapply header_part_is_valid_subset; eauto; cleanup; eauto.
          }
        }
      }
      
      split_ors; cleanup_no_match; repeat invert_exec_no_match.
      {
        repeat cleanup_pairs.
        right; left; split.
        {
          
          unfold log_rep_explicit, log_header_block_rep in *;
          cleanup_no_match; simpl in *.
          rewrite D in *; simpl in *.
          unfold log_crash_rep.
          exists v, (encode_header
                  {|
                    old_part := match x0 with
                                | Current_Part => current_part (decode_header v)
                                | Old_Part => old_part (decode_header v)
                                end;
                    current_part := match x0 with
                                    | Current_Part => current_part (decode_header v)
                                    | Old_Part => old_part (decode_header v)
                                    end |}).
          simpl.
          exists x2.
          repeat rewrite encode_decode_header; simpl.
          cleanup_no_match; simpl in *.
          cleanup_no_match.
          intuition eauto.
          {
            unfold log_header_block_rep; simpl; intuition eauto.
            rewrite upd_eq; eauto.
          }
          {
            unfold log_data_blocks_rep in *; simpl; intuition eauto.
            rewrite upd_ne; eauto.
          }
          {
            destruct x0; eauto.
          }
          {
            destruct x0; eauto.
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; intuition eauto.
            eapply header_part_is_valid_subset; eauto; cleanup; eauto.    
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; intuition eauto.
            cleanup; intuition eauto.
            {
              left; intuition eauto.
              eapply header_part_is_valid_subset; eauto; cleanup; eauto.
            }
            {
              right; intuition eauto.
              eapply header_part_is_valid_subset; eauto; cleanup; eauto.

            }
          }
        }
        {
          intros.
          apply upd_ne.
          pose proof hdr_before_log.
          pose proof data_start_where_log_ends; lia.
        }
      }
      {
        repeat cleanup_pairs; eauto.
        eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H.
        logic_clean.
        eapply decrypt_txns_crashed in H3; eauto.
        (* clear H0 H3 H4 H6. *)
        cleanup_no_match.
        
        right; right; split.
        unfold log_rep, log_rep_general.
        {
          unfold log_rep_explicit, log_header_block_rep in *;
          cleanup_no_match; simpl in *.
          rewrite D in *; simpl in *.
          eexists.
          exists (encode_header
               {|
                 old_part := match x0 with
                             | Current_Part => current_part (decode_header v)
                             | Old_Part => old_part (decode_header v)
                             end;
                 current_part := match x0 with
                                 | Current_Part => current_part (decode_header v)
                                 | Old_Part => old_part (decode_header v)
                                 end |}, []).
          simpl.
          exists (map (fun vs => (fst vs, [])) x2).
          repeat rewrite encode_decode_header; simpl.
          rewrite map_map, map_length.
          cleanup_no_match; simpl in *.
          cleanup_no_match.
          intuition eauto.
          {
            rewrite sync_upd_comm; simpl.
            rewrite upd_eq; eauto.
          }
          {
            unfold log_data_blocks_rep in *; simpl; intuition eauto.
            repeat cleanup_pairs.
            rewrite map_length in H10.
            rewrite sync_upd_comm; simpl in *.
            rewrite upd_ne; eauto.
            unfold sync; erewrite seln_map;
            simpl; eauto.
            rewrite H; eauto.            
            rewrite <- H12; eauto.
            apply in_map_iff in H10; cleanup; eauto.
            rewrite map_length; eauto.
          }
          {
            destruct x0; eauto.
          }
          {
            destruct x0; eauto.
          }
          {
            unfold log_rep_inner in *; simpl in *; cleanup_no_match; intuition eauto.
            eapply header_part_is_valid_subset; eauto; cleanup; eauto.
            eapply txns_valid_subset; eauto; cleanup; eauto.   
          }
        }
        {
          simpl; intros.
          repeat cleanup_pairs.
          rewrite sync_upd_comm; simpl.
          apply upd_ne.
          pose proof hdr_before_log.
          pose proof data_start_where_log_ends; lia.
        }          
      }
    }
  }
Qed.


