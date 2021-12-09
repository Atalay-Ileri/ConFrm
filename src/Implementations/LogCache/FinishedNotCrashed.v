Require Import Lia Datatypes PeanoNat Compare_dec Framework TotalMem FSParameters Log Log.Specs.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer. 
Require Import Log LogCache LogCache.RepImplications.
Require Import FunctionalExtensionality.



Lemma BatchOperations_encrypt_all_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.encrypt_all k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.encrypt_all k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H1; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_hash_all_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.hash_all k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.hash_all k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H1; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_write_batch_finished_oracle_eq:
forall u k1 k2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 ,

exec CryptoDiskLang u o1 s1
(BatchOperations.write_batch k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.write_batch k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length k1 = length k2 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  unfold BatchOperations.write_batch.
  induction k1; destruct k2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto; simpl in *; try lia.
  - repeat invert_exec; cleanup; eauto; try lia.
  - repeat invert_exec; cleanup; eauto; try lia.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHk1 in H1; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_write_consecutive_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,

exec CryptoDiskLang u o1 s1
(BatchOperations.write_consecutive k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.write_consecutive k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  unfold BatchOperations.write_consecutive.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H1; eauto.
  subst; eauto.
Qed.


Lemma BatchOperations_read_consecutive_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.read_consecutive k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.read_consecutive k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
l1 = l2 ->
o1 = o2.
Proof.
  unfold BatchOperations.write_consecutive.
  induction l1; simpl; intros; cleanup; try lia.
  simpl in *; repeat invert_exec; eauto.
  simpl in *; repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_decrypt_all_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.decrypt_all k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.decrypt_all k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H1; eauto.
  subst; eauto.
Qed.




Lemma log_read_header_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
read_header  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
read_header (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent read_header.
  unfold read_header; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  Opaque read_header.
Qed.

Lemma log_write_header_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 h1 h2,
exec CryptoDiskLang u o1 s1
(write_header h1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(write_header h2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent write_header.
  unfold write_header; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  Opaque write_header.
Qed.

Lemma log_update_header_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 h1 h2,
exec CryptoDiskLang u o1 s1
(update_header h1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(update_header h2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent update_header.
  unfold update_header; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply log_read_header_finished_oracle_eq in H; eauto.
  cleanup.
  eapply log_write_header_finished_oracle_eq in H3; eauto.
  subst; eauto.
  Opaque update_header.
Qed.



Lemma log_commit_txn_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit_txn a1 v1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(commit_txn a2 v2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length (a2 ++ v2) = length (a1 ++ v1) ->
o1 = o2.
Proof.
  unfold commit_txn; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia.
  repeat rewrite <- app_assoc in *; cleanup.

  eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
  simpl in *; cleanup.

  repeat rewrite <- app_assoc in *; cleanup.
  eapply_fresh BatchOperations_encrypt_all_finished_oracle_eq in H13; eauto. 
  cleanup.

  eapply BatchOperations.encrypt_all_finished in H13.
  eapply BatchOperations.encrypt_all_finished in H4.
  cleanup.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply_fresh BatchOperations_hash_all_finished_oracle_eq in H15; eauto. 
  cleanup.

  eapply BatchOperations.hash_all_finished in H15.
  eapply BatchOperations.hash_all_finished in H6.
  cleanup.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply BatchOperations_write_consecutive_finished_oracle_eq in H16; eauto. 
  cleanup.

  repeat rewrite <- app_assoc in *; cleanup.
  eapply log_update_header_finished_oracle_eq in H17; eauto.
  subst; eauto.
  all: repeat rewrite map_length; eauto. 
Qed.

Lemma log_commit_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit a1 v1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(commit a2 v2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length (a1 ++ v1) = length (a2 ++ v2) ->
(log_length >=
count
  (current_part
     (decode_header
        (fst (snd s1 hdr_block_num)))) +
(length a1 + length v1) <-> log_length >=
count
  (current_part
     (decode_header
        (fst (snd s2 hdr_block_num)))) +
(length a2 + length v2)) ->
o1 = o2.
Proof.
  Transparent commit.
  unfold commit; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *;
  try eapply_fresh log_read_header_finished_oracle_eq in H; eauto;
  subst; eauto; cleanup.
  {
    apply Nat.ltb_ge in D0.
    apply Nat.ltb_lt in D.
    Transparent read_header.
    unfold read_header in *; repeat invert_exec; cleanup.
    repeat cleanup_pairs; lia.
    Opaque read_header.
  }
  {
    apply Nat.ltb_ge in D.
    apply Nat.ltb_lt in D0.
    Transparent read_header.
    unfold read_header in *; repeat invert_exec; cleanup.
    repeat cleanup_pairs; lia.
    Opaque read_header.
  }
  {
    eapply log_commit_txn_finished_oracle_eq in H5; eauto.
    cleanup; eauto.
  }
  Opaque commit.
Qed.

Lemma log_check_hash_finished_oracle_eq:
forall u l1 l2 h1 h2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(check_hash l1 h1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(check_hash l2 h2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  Transparent check_hash.
  unfold check_hash; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *;
  try eapply_fresh BatchOperations_hash_all_finished_oracle_eq in H; eauto;
  subst; eauto; cleanup.
Qed.


Lemma log_read_encrypted_log_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,

exec CryptoDiskLang u o1 s1
read_encrypted_log (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
read_encrypted_log (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent read_encrypted_log.
  unfold read_encrypted_log; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *;
  try eapply_fresh log_read_header_finished_oracle_eq in H; eauto;
  subst; eauto; cleanup.
  {
      eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H4; eauto. 
      cleanup.
      eapply_fresh log_check_hash_finished_oracle_eq in H5; eauto. 
      cleanup; eauto.
      all: admit.
  }
  {
      eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H4; eauto. 
      cleanup.
      eapply_fresh log_check_hash_finished_oracle_eq in H5; eauto. 
      cleanup; eauto.

      unfold check_hash in *; repeat invert_exec; try congruence.
      (* Impossible case between related states. *)
      all: admit.
  }
  {
    admit. (* Impossible case between related states. *)
  }
  {
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H5.
    2: apply H2. 
    all: eauto. 
    cleanup.

    eapply_fresh log_check_hash_finished_oracle_eq in H6; eauto. 
    cleanup; eauto.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H7; eauto.
    cleanup; eauto.
    all: admit.
  }
  Opaque read_encrypted_log.
Admitted.

Lemma log_decrypt_txn_finished_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(decrypt_txn txn_rec1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(decrypt_txn txn_rec2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length
  (firstn (addr_count txn_rec1 + data_count txn_rec1)
     (skipn (start txn_rec1) l1)) =
length
  (firstn (addr_count txn_rec2 + data_count txn_rec2)
     (skipn (start txn_rec2) l2)) ->
o1 = o2.
Proof.
  unfold decrypt_txn; simpl; intros.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto.
  cleanup; eauto.
Qed.


Lemma log_apply_txn_finished_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(apply_txn txn_rec1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(apply_txn txn_rec2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length
  (firstn (addr_count txn_rec2 + data_count txn_rec2) (skipn (start txn_rec2) l2)) =
length
  (firstn (addr_count txn_rec1 + data_count txn_rec1) (skipn (start txn_rec1) l1)) ->
o1 = o2.
Proof.
  Transparent apply_txn.
  unfold apply_txn; simpl; intros.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply_fresh log_decrypt_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply BatchOperations_write_batch_finished_oracle_eq in H4; eauto.
  cleanup; eauto.
  eapply Specs.decrypt_txn_finished in H0; eauto.
Admitted.


Lemma log_apply_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(apply_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(apply_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length txn_recs1 = length txn_recs2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply log_apply_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHtxn_recs1 in H3; eauto.
  cleanup; eauto.
  admit.
Admitted.

Lemma log_decrypt_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(decrypt_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(decrypt_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length txn_recs1 = length txn_recs2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHtxn_recs1 in H3; eauto.
  cleanup; eauto.
Admitted.


Lemma log_flush_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(flush_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(flush_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length txn_recs1 = length txn_recs2 ->
o1 = o2.
Proof.
  Transparent flush_txns.
  unfold flush_txns; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *.
  eapply log_apply_txns_finished_oracle_eq in H; eauto.
  simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_update_header_finished_oracle_eq in H9; eauto.
  cleanup; eauto.
Qed.

Lemma log_apply_log_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
apply_log (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
apply_log (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent apply_log.
  unfold apply_log; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *;
  try eapply_fresh log_read_header_finished_oracle_eq in H0; eauto;
  subst; eauto; cleanup.
  eapply log_read_encrypted_log_finished_oracle_eq in H; eauto.
  cleanup.
  eapply log_flush_txns_finished_oracle_eq in H3; eauto.
  cleanup; eauto.
Admitted.


Lemma log_recover_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
Log.recover (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
Log.recover (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent Log.recover.
  unfold Log.recover; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia;
  repeat rewrite <- app_assoc in *;
  try eapply_fresh log_read_header_finished_oracle_eq in H0; eauto;
  subst; eauto; cleanup.
  eapply log_read_encrypted_log_finished_oracle_eq in H; eauto.
  cleanup.
  eapply log_write_header_finished_oracle_eq in H6; eauto.
  cleanup.
  simpl in *; cleanup.
  eapply log_decrypt_txns_finished_oracle_eq in H8; eauto.
  cleanup; eauto.
Admitted.

Lemma log_init_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 ,
exec CryptoDiskLang u o1 s1
(Log.init l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(Log.init l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  Transparent Log.init.
  unfold Log.init; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H; eauto.
  cleanup.
  eapply BatchOperations_write_batch_finished_oracle_eq in H6; eauto.
  cleanup; eauto.
  all: repeat rewrite map_length; eauto.
Qed.


Lemma read_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 a1 a2,
exec CachedDiskLang u o1 s1
(read a1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(read a2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold read; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
Qed.



Lemma write_batch_to_cache_finished_oracle_eq:
forall u l1 l2 l3 l4 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CachedDiskLang u o1 s1
(LogCache.write_batch_to_cache l1 l3)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(LogCache.write_batch_to_cache l2 l4) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply IHl1 in H3; eauto.
  cleanup; eauto.
Qed.

Lemma write_lists_to_cache_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CachedDiskLang u o1 s1
(LogCache.write_lists_to_cache l1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(LogCache.write_lists_to_cache l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHl1 in H3; eauto.
  subst; eauto.
Admitted.


Lemma recover_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CachedDiskLang u o1 s1
recover  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
recover (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold recover; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply log_recover_finished_oracle_eq in H10; eauto.
  cleanup.
  eapply write_lists_to_cache_finished_oracle_eq in H8; eauto.
  cleanup; eauto.
Admitted.


Lemma init_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 ,
exec CachedDiskLang u o1 s1
(init l1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(init l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  unfold init; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  apply map_ext_eq_prefix in H10; eauto; cleanup.
  eapply log_init_finished_oracle_eq in H8; eauto.
  subst; eauto.
  repeat rewrite combine_length_eq.
  all: repeat rewrite map_length; eauto.
  repeat constructor.
  exact key0.
  intros; cleanup; intuition congruence.
Qed.

Lemma write_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 a1 a2 v1 v2,
exec CachedDiskLang u o1 s1
(write a1 v1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(write a2 v2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold write; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
Admitted.



(* Finished Not Crashed proofs*)
Lemma BatchOperations_read_consecutive_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.read_consecutive st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
n1 = n2 ->
~exec CryptoDiskLang u o2 s2
(BatchOperations.read_consecutive st2 n2) (Crashed s2').
Proof.
  unfold not; induction n1; destruct n2; simpl; intros; cleanup;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  eapply IHn1.
  eauto.
  3: eauto.
  all: eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_read_consecutive_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  lia.
Qed.

Lemma BatchOperations_hash_all_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.hash_all st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length n1 = length n2 ->
~exec CryptoDiskLang u o2 s2
(BatchOperations.hash_all st2 n2) (Crashed s2').
Proof.
  unfold not; induction n1; destruct n2; simpl; intros; cleanup;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  eapply IHn1.
  eauto.
  3: eauto.
  all: eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_hash_all_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  lia.
Qed.

Lemma BatchOperations_decrypt_all_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.decrypt_all st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length n1 = length n2 ->
~exec CryptoDiskLang u o2 s2
(BatchOperations.decrypt_all st2 n2) (Crashed s2').
Proof.
  unfold not; induction n1; destruct n2; simpl; intros; cleanup;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  eapply IHn1.
  eauto.
  3: eauto.
  all: eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  lia.
Qed.

Lemma BatchOperations_write_batch_finished_not_crashed:
forall u st1 st2 n1 n2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.write_batch st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length st1 = length st2 ->
length n1 = length n2 ->
~exec CryptoDiskLang u o2 s2
(BatchOperations.write_batch st2 n2) (Crashed s2').
Proof.
  unfold not; induction st1; destruct st2; simpl; intros; cleanup;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  simpl in *.
  eapply IHst1.
  eauto.
  4: eauto.
  all: eauto.

  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_write_batch_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  all: lia.
Qed.


Lemma log_read_header_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
read_header (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
read_header (Crashed s2').
Proof.
  Transparent read_header.
  unfold read_header, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  Opaque read_header.
Qed.

Lemma log_check_hash_finished_not_crashed:
forall u l1 l2 h1 h2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(check_hash l1 h1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
~exec CryptoDiskLang u o2 s2
(check_hash l2 h2) (Crashed s2').
Proof.
  unfold check_hash, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.

  repeat rewrite <- app_assoc in *.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_hash_all_finished_not_crashed; eauto.
    
    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_hash_all_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.


    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_hash_all_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.

    repeat rewrite <- app_assoc in *.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_hash_all_finished_not_crashed; eauto.

    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_hash_all_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.


    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_hash_all_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
Qed.

Lemma log_read_encrypted_log_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
read_encrypted_log (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
read_encrypted_log (Crashed s2').
Proof.
  Transparent read_encrypted_log.
  unfold read_encrypted_log, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  {
    repeat rewrite <- app_assoc in *.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_read_header_finished_not_crashed; eauto.

    repeat rewrite <- app_assoc in *.
    eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.
    shelve.

    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_read_consecutive_finished_oracle_eq in H2; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
       eapply log_check_hash_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.
    shelve.

    repeat rewrite <- app_assoc in *.
    eapply log_check_hash_finished_oracle_eq in H3; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    shelve.

    shelve.
    shelve.
  }
  {
    repeat rewrite <- app_assoc in *.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_read_header_finished_not_crashed; eauto.

    repeat rewrite <- app_assoc in *.
    eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    apply H2.
    3:eauto.
    all: eauto.
    shelve.

    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_read_consecutive_finished_oracle_eq in H2; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_check_hash_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.
    shelve.

    shelve.

    repeat rewrite <- app_assoc in *.
    eapply log_check_hash_finished_oracle_eq in H3; eauto; cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.

    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    4: eauto.
    2: eauto.
    all: eauto.
    shelve.

    repeat rewrite <- app_assoc in *.
    eapply BatchOperations_read_consecutive_finished_oracle_eq in H4; eauto; cleanup.
    simpl in *; cleanup.
    shelve.
    shelve.
    shelve.
  }
  Unshelve.
Admitted.

Lemma log_write_header_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 h1 h2,
exec CryptoDiskLang u o1 s1
(write_header h1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(write_header h2) (Crashed s2').
Proof.
  Transparent write_header.
  unfold write_header, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
Qed.

Lemma log_decrypt_txn_finished_not_crashed:
forall u rec1 rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(decrypt_txn rec1 l1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length (firstn (addr_count rec1 + data_count rec1) (skipn (start rec1) l1)) =
length (firstn (addr_count rec2 + data_count rec2) (skipn (start rec2) l2)) ->
~exec CryptoDiskLang u o2 s2
(decrypt_txn rec2 l2) (Crashed s2').
Proof.
  unfold decrypt_txn, not;  intros. 
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_not_crashed. 
  4: eauto.
  eauto.
  all: eauto.

  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
Qed.

Lemma log_decrypt_txns_finished_not_crashed:
forall u recs1 recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(decrypt_txns recs1 l1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length recs1 = length recs2 ->
~exec CryptoDiskLang u o2 s2
(decrypt_txns recs2 l2) (Crashed s2').
Proof.
  unfold not; 
  induction recs1; destruct recs2; simpl; intros; try lia.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_not_crashed. 
  4: eauto.
  eauto.
  all: eauto.
  shelve.

  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  eapply IHrecs1.
  4: eauto.
  eauto.
  all: eauto.
  shelve.

  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txns_finished_oracle_eq in H3; eauto. 
  cleanup; simpl in *; cleanup.
  lia.
  shelve.
Admitted.


Lemma log_recover_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
Log.recover (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
Log.recover (Crashed s2').
Proof.
  unfold Log.recover, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_not_crashed in H; eauto.
  

  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  eapply log_write_header_finished_not_crashed; eauto.
  
  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H2; eauto. 
  cleanup; simpl in *; cleanup.


  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H2; eauto. 
  cleanup; simpl in *; cleanup.
  eapply log_decrypt_txns_finished_not_crashed. 
  4: eauto.
  eauto.
  all: eauto.
  shelve.
Admitted.


Lemma log_init_finished_not_crashed:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(Log.init l1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
~exec CryptoDiskLang u o2 s2
(Log.init l2) (Crashed s2').
Proof.
  unfold Log.init, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_not_crashed in H; eauto.
  

  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  eapply BatchOperations_write_batch_finished_not_crashed. 
  eauto.
  4: eauto.
  all: repeat rewrite map_length; eauto.
  

  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_write_batch_finished_oracle_eq in H3; eauto. 
  cleanup; simpl in *; cleanup.
  all: repeat rewrite map_length; eauto.
Qed.




Lemma write_batch_to_cache_finished_not_crashed:
forall u a1 a2 v1 v2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CachedDiskLang u o1 s1
(LogCache.write_batch_to_cache a1 v1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CachedDiskLang u o2 s2
(LogCache.write_batch_to_cache a2 v2) (Crashed s2').
Proof.
  unfold not; induction a1; destruct a2; 
  simpl; intros; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
Qed.


Lemma write_lists_to_cache_finished_not_crashed:
forall u a1 a2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CachedDiskLang u o1 s1
(LogCache.write_lists_to_cache a1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length a1 = length a2 ->
~exec CachedDiskLang u o2 s2
(LogCache.write_lists_to_cache a2) (Crashed s2').
Proof.
  unfold not; induction a1; destruct a2; 
  simpl; intros; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_not_crashed; eauto.

  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_oracle_eq in H; eauto.
  cleanup; eauto.
  shelve.
Admitted.

Lemma read_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2,
exec CachedDiskLang u o1 s1
(read a1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CachedDiskLang u o2 s2
(read a2) (Crashed s2').
Proof.
  unfold read, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
Qed.

Opaque Log.recover.
Lemma recover_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CachedDiskLang u o1 s1
recover (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CachedDiskLang u o2 s2
recover (Crashed s2').
Proof.
  unfold recover, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat rewrite <- app_assoc in *.
  eapply map_ext_eq_prefix in H2.
  cleanup.
  eapply log_recover_finished_not_crashed; eauto.
  solve [repeat constructor].
  intros; cleanup; intuition congruence.

  repeat rewrite <- app_assoc in *.
  eapply_fresh map_ext_eq_prefix in H2.
  cleanup.
  eapply log_recover_finished_oracle_eq in H6; eauto.
  cleanup.
  eapply write_lists_to_cache_finished_not_crashed.
  4: eauto.
  eauto.
  all: eauto.
  shelve.
  solve [repeat constructor].
  intros; cleanup; intuition congruence.
Admitted.

Opaque Log.init.
Lemma init_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2,
exec CachedDiskLang u o1 s1
(init a1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
length a1 = length a2 ->
~exec CachedDiskLang u o2 s2
(init a2) (Crashed s2').
Proof.
  unfold init, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  eapply map_ext_eq_prefix in H8; cleanup.
  eapply log_init_finished_not_crashed. 
  eauto.
  3: eauto.
  all: eauto.
  repeat rewrite combine_length_eq; eauto.
  all: repeat rewrite map_length; eauto.
  solve [repeat econstructor].
  intros; cleanup; intuition congruence.
Qed.

Opaque apply_log commit.
Lemma write_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2 v1 v2,
exec CachedDiskLang u o1 s1
(write a1 v1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CachedDiskLang u o2 s2
(write a2 v2) (Crashed s2').
Proof. Admitted.
(*
  unfold write, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
*)
