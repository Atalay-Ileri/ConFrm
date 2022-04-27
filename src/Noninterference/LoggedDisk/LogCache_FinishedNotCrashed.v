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

Lemma read_header_finished:
forall u o1 s1 s1' r1 vp1 txns1 hdr1,

exec CryptoDiskLang u o1 s1
read_header (Finished s1' r1) ->

log_reboot_rep_explicit_part  hdr1 txns1 vp1 s1 ->

r1 = hdr1 /\ s1' = s1.
Proof.
  Transparent read_header.
  unfold read_header; intros.
  repeat invert_exec.
  unfold log_reboot_rep_explicit_part, log_rep_general, 
  log_rep_explicit, log_header_block_rep in *.
  cleanup.
  repeat cleanup_pairs; eauto.
  Opaque read_header.
Qed.

Lemma log_read_encrypted_log_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 vp txns1 txns2 hdr1 hdr2,

exec CryptoDiskLang u o1 s1
read_encrypted_log (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
read_encrypted_log (Finished s2' r2) ->

log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->

Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 

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
      eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H9; eauto. 
      cleanup.
      eapply_fresh log_check_hash_finished_oracle_eq in H10; eauto. 
      cleanup; eauto.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      eapply BatchOperations.read_consecutive_finished in H7; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H9; eauto; cleanup.
      eauto.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup; eauto.
  }
  
  {
      unfold check_hash in *; repeat invert_exec; try congruence.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup.
      eapply BatchOperations.read_consecutive_finished in H7; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H9; eauto; cleanup.
      eapply BatchOperations.hash_all_finished in H8; eauto; cleanup. 
      eapply BatchOperations.hash_all_finished in H10; eauto; cleanup.

      exfalso.
      unfold log_reboot_rep_explicit_part , log_rep_general, 
      log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match.
      unfold log_reboot_rep_explicit_part , log_rep_general, 
      log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match.
      assert(firstn (count (current_part
      (decode_header (fst (snd s1 hdr_block_num))))) (map fst x7) = x13). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H32; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H9; eauto.
        rewrite <- H3; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e1; eauto.
        lia.
        setoid_rewrite H32; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H32; eauto.
        lia.
      }
      assert(firstn (count (current_part
      (decode_header (fst (snd s2 hdr_block_num))))) (map fst x2) = x6). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H24; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H0; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e; eauto.
        lia.
        setoid_rewrite H24; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H24; eauto.
      }
      subst.
      unfold log_rep_inner, header_part_is_valid in *; logic_clean.
      destruct vp; eauto.
      apply H10; eauto.
  }
  {
      unfold check_hash in *; repeat invert_exec; try congruence.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup.
      eapply BatchOperations.read_consecutive_finished in H7; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H10; eauto; cleanup.
      eapply BatchOperations.hash_all_finished in H8; eauto; cleanup. 
      eapply BatchOperations.hash_all_finished in H11; eauto; cleanup.

      exfalso.
      unfold log_reboot_rep_explicit_part , log_rep_general, 
      log_rep_explicit, log_header_block_rep in *;
      cleanup_no_match.
      assert(firstn (count (current_part
      (decode_header (fst (snd s1 hdr_block_num))))) (map fst x9) = x16). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H32; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H10; eauto.
        rewrite <- H3; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e1; eauto.
        lia.
        setoid_rewrite H32; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H32; eauto.
        lia.
      }
      assert(firstn (count (current_part
      (decode_header (fst (snd s2 hdr_block_num))))) (map fst x2) = x6). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H24; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H0; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e; eauto.
        lia.
        setoid_rewrite H24; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H24; eauto.
      }
      subst.
      unfold log_rep_inner, header_part_is_valid in *; logic_clean.
      destruct vp; eauto.
      apply H29; eauto.
      rewrite <- H3; eauto.
  }
  {
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H10.
    2: apply H7. 
    all: eauto. 
    cleanup.

    eapply_fresh log_check_hash_finished_oracle_eq in H11; eauto. 
    cleanup; eauto.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H12; eauto.
    cleanup; eauto.
    eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto. 
      cleanup; eauto.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto. 
      eapply BatchOperations.read_consecutive_finished in H7; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H10; eauto; cleanup.
      eauto.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup; eauto.
  }
  Opaque read_encrypted_log.
Qed.

Lemma log_decrypt_txn_finished_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(decrypt_txn txn_rec1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(decrypt_txn txn_rec2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
length l1 = length l2 ->
addr_count txn_rec1 = addr_count txn_rec2 ->
data_count txn_rec1 = data_count txn_rec2 ->
start txn_rec1 = start txn_rec2 ->
o1 = o2.
Proof.
  unfold decrypt_txn; simpl; intros.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto.
  cleanup; eauto.
  repeat rewrite firstn_length, skipn_length.
  lia.
Qed.


Lemma log_apply_txn_finished_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(apply_txn txn_rec1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(apply_txn txn_rec2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1 ->
length
  (blocks_to_addr_list
     (firstn
        (addr_count
           txn_rec1)
        (map
           (decrypt
              (key txn_rec1))
           (firstn
              (addr_count
                 txn_rec1 +
               data_count
                 txn_rec1)
              (skipn
                 (start
                 txn_rec1)
                 l1))))) >= data_count txn_rec1 ->
length
(blocks_to_addr_list
  (firstn
      (addr_count
        txn_rec2)
      (map
        (decrypt
            (key txn_rec2))
        (firstn
            (addr_count
              txn_rec2 +
            data_count
              txn_rec2)
            (skipn
              (start
              txn_rec2)
              l2))))) >= data_count txn_rec2 ->
addr_count txn_rec1 = addr_count txn_rec2 ->
data_count txn_rec1 = data_count txn_rec2 ->
start txn_rec1 = start txn_rec2 -> 
length l2 = length l1 ->
o1 = o2.
Proof.
  Transparent apply_txn.
  unfold apply_txn; simpl; intros.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply_fresh log_decrypt_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply BatchOperations_write_batch_finished_oracle_eq in H10; eauto.
  cleanup; eauto.
  {
    eapply Specs.decrypt_txn_finished in H; eauto.
    eapply Specs.decrypt_txn_finished in H0; eauto.
    cleanup; simpl.
    repeat rewrite firstn_length_l; eauto.

    rewrite skipn_length.
    rewrite map_length.
    repeat rewrite firstn_length_l.
    lia.
    rewrite skipn_length; lia.
    lia.

    rewrite skipn_length.
    rewrite map_length.
    repeat rewrite firstn_length_l.
    lia.
    rewrite skipn_length; lia.
    cleanup; lia.
  }
  {
    eapply Specs.decrypt_txn_finished in H; eauto.
    eapply Specs.decrypt_txn_finished in H0; eauto.
    cleanup; simpl.
    repeat rewrite skipn_length.
    repeat rewrite map_length.
    repeat rewrite firstn_length_l.
    lia.
    rewrite skipn_length; lia.
    rewrite skipn_length; lia.

    rewrite skipn_length.
    rewrite map_length.
    repeat rewrite firstn_length_l.
    lia.
    rewrite skipn_length; lia.
    cleanup; lia.

    rewrite skipn_length.
    rewrite map_length.
    repeat rewrite firstn_length_l.
    lia.
    rewrite skipn_length; lia.
    cleanup; lia.
  }
Qed.


Lemma log_apply_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(apply_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(apply_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall2 (fun txn_rec1 txn_rec2 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1 /\
length
  (blocks_to_addr_list
     (firstn
        (addr_count
           txn_rec1)
        (map
           (decrypt
              (key txn_rec1))
           (firstn
              (addr_count
                 txn_rec1 +
               data_count
                 txn_rec1)
              (skipn
                 (start
                 txn_rec1)
                 l1))))) >= data_count txn_rec1 /\
length
(blocks_to_addr_list
  (firstn
      (addr_count
        txn_rec2)
      (map
        (decrypt
            (key txn_rec2))
        (firstn
            (addr_count
              txn_rec2 +
            data_count
              txn_rec2)
            (skipn
              (start
              txn_rec2)
              l2))))) >= data_count txn_rec2 /\
addr_count txn_rec1 = addr_count txn_rec2 /\
data_count txn_rec1 = data_count txn_rec2 /\
start txn_rec1 = start txn_rec2) 
txn_recs1 txn_recs2 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; 
  eapply_fresh forall2_length in H2; simpl in *; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  inversion H2; cleanup.
  eapply log_apply_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHtxn_recs1 in H4; eauto.
  cleanup; eauto.
  rewrite <- H3 in *; eauto.
  cleanup; lia.
Qed.

Lemma log_decrypt_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(decrypt_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(decrypt_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall2 (fun txn_rec1 txn_rec2 =>
addr_count txn_rec1 = addr_count txn_rec2 /\
data_count txn_rec1 = data_count txn_rec2 /\
start txn_rec1 = start txn_rec2) 
txn_recs1 txn_recs2 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; 
  eapply_fresh forall2_length in H2; simpl in *; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  inversion H2; cleanup.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHtxn_recs1 in H4; eauto.
  cleanup; eauto.
Qed.


Lemma log_flush_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(flush_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(flush_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall2 (fun txn_rec1 txn_rec2 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1 /\
length
  (blocks_to_addr_list
     (firstn
        (addr_count
           txn_rec1)
        (map
           (decrypt
              (key txn_rec1))
           (firstn
              (addr_count
                 txn_rec1 +
               data_count
                 txn_rec1)
              (skipn
                 (start
                 txn_rec1)
                 l1))))) >= data_count txn_rec1 /\
length
(blocks_to_addr_list
  (firstn
      (addr_count
        txn_rec2)
      (map
        (decrypt
            (key txn_rec2))
        (firstn
            (addr_count
              txn_rec2 +
            data_count
              txn_rec2)
            (skipn
              (start
              txn_rec2)
              l2))))) >= data_count txn_rec2 /\
addr_count txn_rec1 = addr_count txn_rec2 /\
data_count txn_rec1 = data_count txn_rec2 /\
start txn_rec1 = start txn_rec2) 
txn_recs1 txn_recs2 ->
length l1 = length l2 ->
o1 = o2.
Proof.
  Transparent flush_txns.
  unfold flush_txns; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; eapply_fresh forall2_length in H2; simpl in *; try lia;
  repeat rewrite <- app_assoc in *.
  eapply log_apply_txns_finished_oracle_eq in H0; only 2: apply H; eauto.
  simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_update_header_finished_oracle_eq in H10; eauto.
  cleanup; eauto.
  rewrite <- H3 in *; eauto.
Qed.

Lemma blocks_to_addr_list_length_eq:
  forall l1 l2 : list value,
  length l1 = length l2 ->
  length (blocks_to_addr_list l1) = length (blocks_to_addr_list l2).
  Proof.
    intros.
    pose proof blocks_to_addr_list_length_le_preserve l1 l2.
    pose proof blocks_to_addr_list_length_le_preserve l2 l1.
    apply Nat.le_antisymm; lia.
  Qed.

Lemma log_apply_log_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 hdr1 hdr2 txns1 txns2,
exec CryptoDiskLang u o1 s1
apply_log (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
apply_log (Finished s2' r2) ->

log_header_rep hdr1 txns1 s1 ->
log_header_rep hdr2 txns2 s2 ->

count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 

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
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H0. 
  2: apply H.
  all: eauto.
  cleanup.
  eapply log_flush_txns_finished_oracle_eq in H8; eauto.
  cleanup; eauto.
  unfold log_header_rep, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished in H; eauto.
  eapply read_encrypted_log_finished in H0; eauto.
  cleanup; simpl.
  all: intros; try congruence.
  eapply_fresh forall2_length in H5.
  eapply forall2_forall in H5.
  eapply forall_forall2.
  eapply Forall_forall; intros.
  apply in_combine_swap in H.
  eapply Forall_forall in H5; eauto.
  simpl in *.
  unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
  rewrite <- H24, <- H32 in *.
  setoid_rewrite <- combine_map' in H.
  apply in_map_iff in H.
  cleanup.
  eapply in_seln_exists in H34; cleanup.
  erewrite seln_combine in H1.
  destruct x, x2; simpl in *;
  inversion H1; subst.
  {
   intuition; eauto.
   {
     eapply Forall_forall in H25.
     2: eapply in_seln.
     unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite firstn_length_l.
    rewrite <- H35; eauto.
    rewrite map_length.
    setoid_rewrite H20; eauto.
    rewrite combine_length in H; lia.
   }
   {
    eapply Forall_forall in H25.
    2: eapply in_seln.
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H35 in *.
    eapply Nat.le_trans; eauto.
    eapply blocks_to_addr_list_length_le_preserve.
    rewrite firstn_length_l.
    lia.
    rewrite map_length.
    rewrite firstn_length_l.
    lia.
    rewrite skipn_length.
    rewrite firstn_length_l.
    lia.
    rewrite map_length.
    setoid_rewrite H20; eauto.
    rewrite combine_length in H; lia.
   }
   {
     rewrite <- H0, <- H5 in *.
    eapply Forall_forall in H33.
    2: eapply in_seln.
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H34 in *.
    eapply Nat.le_trans; eauto.
    eapply blocks_to_addr_list_length_le_preserve.
    rewrite firstn_length_l.
    lia.
    rewrite map_length.
    rewrite firstn_length_l.
    lia.
    rewrite skipn_length.
    rewrite firstn_length_l.
    lia.
    rewrite map_length.
    setoid_rewrite H28; eauto.
    rewrite combine_length in H; lia.
   }
  }
  rewrite <- H24, <- H32 in *; eauto.
  repeat rewrite map_length in *; eauto.
  eauto.
  {
    unfold log_header_rep, log_rep_general in *; cleanup.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H0; eauto.
    cleanup; simpl.
    all: intros; try congruence.
    unfold log_rep_explicit in *; logic_clean.
    repeat rewrite firstn_length_l; eauto.
    rewrite map_length, <- H3; eauto.
    setoid_rewrite H23; eauto.
    rewrite map_length; eauto.
    setoid_rewrite H17; eauto.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    logic_clean; do 2 eexists; intuition eauto.
    congruence.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    logic_clean; do 2 eexists; intuition eauto.
    congruence.
  }
  Unshelve.
  all: repeat constructor; exact key0.
Qed.


Lemma log_recover_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 vp hdr1 hdr2 txns1 txns2,
exec CryptoDiskLang u o1 s1
Log.recover (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
Log.recover (Finished s2' r2) ->
log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->


count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (old_part hdr1)) (records (old_part hdr2)) -> 

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
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H0; 
  only 2: apply H; eauto.
  cleanup.
  eapply log_write_header_finished_oracle_eq in H12; eauto.
  cleanup.
  simpl in *; cleanup.
  eapply log_decrypt_txns_finished_oracle_eq in H10. 
  3: eauto.
  all: eauto.
  cleanup; eauto.
  {
    unfold log_reboot_rep_explicit_part, log_rep_general in *; cleanup.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H0; eauto.
    cleanup_no_match; simpl.
    all: intros; try congruence.
    eapply_fresh forall2_length in H5.
    eapply_fresh forall2_length in H6.
    destruct vp; simpl in *.
    {
      eapply forall2_forall in H5.
      eapply forall_forall2.
      eapply Forall_forall; intros.
      eapply Forall_forall in H5; eauto.
      eauto.
    }
    {
      eapply forall2_forall in H6.
      eapply forall_forall2.
      eapply Forall_forall; intros.
      eapply Forall_forall in H6; eauto.
      eauto.
    }
    rewrite <- H3 in *; eauto.
  }
  {
    unfold log_reboot_rep_explicit_part, log_rep_general in *; cleanup.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H0; eauto.
    cleanup_no_match; simpl.
    all: intros; try congruence.
    eapply_fresh forall2_length in H5.
    eapply_fresh forall2_length in H6.
    destruct vp; simpl in *.
    {
      unfold log_rep_explicit in *; logic_clean.
      repeat rewrite firstn_length_l; eauto.
      rewrite map_length, <- H3; eauto.
      setoid_rewrite H25; eauto.
      rewrite map_length; eauto.
      setoid_rewrite H31; eauto.
    }
    {
      unfold log_rep_explicit in *; logic_clean.
      repeat rewrite firstn_length_l; eauto.
      rewrite map_length, <- H4; eauto.
      setoid_rewrite H25; eauto.
      rewrite map_length; eauto.
      setoid_rewrite H31; eauto.
    }
    rewrite <- H3 in *; eauto.
  }
Qed.

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
Forall2 (fun a b => length (fst a) = length (fst b)) l1 l2 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros; 
  eapply_fresh forall2_length in H2; simpl in *; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  inversion H2; cleanup.
  eapply write_batch_to_cache_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHl1 in H3; eauto.
  subst; eauto.
Qed.

Set Nested Proofs Allowed.
Lemma in_combine_combine_same:
forall T1 T2 (l1: list T1) (l2: list T2) t,
In t (combine (combine l1 l1) (combine l2 l2)) ->
In (fst (fst t), fst (snd t)) (combine l1 l2) /\
fst (fst t) = snd (fst t) /\
fst (snd t) = snd (snd t).
Proof.
  induction l1; simpl; intros; eauto.
  tauto.
  destruct l2; simpl in *; try tauto.
  split_ors; cleanup; eauto.
  apply IHl1 in H; cleanup; eauto.
Qed.

Lemma recover_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 vp hdr1 hdr2 txns1 txns2,
exec CachedDiskLang u o1 s1
recover  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
recover (Finished s2' r2) ->
log_reboot_rep_explicit_part  hdr1 txns1 vp (snd s1) ->
log_reboot_rep_explicit_part  hdr2 txns2 vp (snd s2) ->

count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (old_part hdr1)) (records (old_part hdr2)) -> 

o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold recover; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply_fresh map_ext_eq_prefix in H17; cleanup.
  eapply_fresh log_recover_finished_oracle_eq in H12; 
  only 2: apply H16; eauto.
  cleanup.
  eapply write_lists_to_cache_finished_oracle_eq in H10. 
  3: eauto.
  all: eauto.
  cleanup; eauto.
  eapply Specs.recover_finished in H12; eauto.
  eapply Specs.recover_finished in H16; eauto.
  cleanup; eauto.
  2: unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  2: unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  eapply_fresh forall2_length in H5.
  eapply_fresh forall2_length in H6.
  destruct vp; simpl in *.
  {
    eapply forall2_forall in H5.
    eapply forall_forall2.
    eapply Forall_forall; intros.
    setoid_rewrite <- combine_map' in H20.
    setoid_rewrite <- combine_map' in H20.
    apply in_map_iff in H20.
    cleanup.
    repeat cleanup_pairs.
    unfold log_reboot_rep_explicit_part, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    apply in_combine_combine_same in H21; simpl in *; logic_clean.
    subst.
    rewrite <- H18, <- H29 in *.
    eapply Forall_forall in H5; eauto.
    2: setoid_rewrite <- combine_map';
      apply in_map; eauto.
    simpl in *.

    eapply in_seln_exists in H21; cleanup_no_match.
    erewrite seln_combine in H0.
    simpl in *;
    inversion H0; subst.
    eapply Forall_forall in H30.
    2: eapply in_seln with (n:= x7).
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H33, <- H37 in *; eauto.
    eapply Forall_forall in H20.
    2: eapply in_seln with (n:= x7).
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H44, <- H48 in *; eauto.
    repeat rewrite firstn_length_l; eauto.
    rewrite H11, H12; eauto.
    rewrite combine_length in H; lia.
    rewrite combine_length in H; lia.
    rewrite <- H18, <- H29 in *.
    repeat rewrite map_length in Hx; eauto.
    repeat rewrite combine_length; 
    repeat rewrite map_length.
    unfold log_reboot_rep_explicit_part, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H27, <- H36 in *.
    repeat rewrite map_length in Hx; eauto.
  }
  {
    eapply forall2_forall in H6.
    eapply forall_forall2.
    eapply Forall_forall; intros.
    setoid_rewrite <- combine_map' in H20.
    setoid_rewrite <- combine_map' in H20.
    apply in_map_iff in H20.
    cleanup.
    repeat cleanup_pairs.
    unfold log_reboot_rep_explicit_part, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    apply in_combine_combine_same in H21; simpl in *; logic_clean.
    subst.
    rewrite <- H18, <- H29 in *.
    eapply Forall_forall in H6; eauto.
    2: setoid_rewrite <- combine_map';
      apply in_map; eauto.
    simpl in *.

    eapply in_seln_exists in H21; cleanup_no_match.
    erewrite seln_combine in H0.
    simpl in *;
    inversion H0; subst.
    eapply Forall_forall in H30.
    2: eapply in_seln with (n:= x7).
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H33, <- H37 in *; eauto.
    eapply Forall_forall in H20.
    2: eapply in_seln with (n:= x7).
    unfold txn_well_formed, record_is_valid in *;
    simpl in *; logic_clean.
    rewrite H44, <- H48 in *; eauto.
    repeat rewrite firstn_length_l; eauto.
    rewrite H11, H12; eauto.
    rewrite combine_length in H; lia.
    rewrite combine_length in H; lia.
    rewrite <- H18, <- H29 in *.
    repeat rewrite map_length in Hx0; eauto.
    repeat rewrite combine_length; 
    repeat rewrite map_length.
    unfold log_reboot_rep_explicit_part, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H27, <- H36 in *.
    repeat rewrite map_length in Hx0; eauto.
  }
  repeat constructor.
  apply key0.
  intros; cleanup; try congruence.
  Unshelve.
  all: repeat constructor; exact key0.
Qed.


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

(*
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
*)
 

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

Lemma read_consecutive_log_finished:
forall n vp hdr txns hdr_blockset log_blocksets s o s' u r,
log_rep_explicit Hdr_Synced Synced vp hdr
      txns hdr_blockset log_blocksets s ->
exec CryptoDiskLang u o s
      (BatchOperations.read_consecutive log_start n) (Finished s' r) ->
n <= log_length ->
s' = s /\
r = firstn n (map fst log_blocksets).
Proof.
  intros.
  eapply BatchOperations.read_consecutive_finished in H0; cleanup.
  split; eauto.
  unfold log_rep_explicit in *; cleanup.
  eapply list_seln_ext.
  rewrite firstn_length_l; eauto.
  rewrite map_length.
  setoid_rewrite H4; eauto.

  intros.
  rewrite seln_firstn; eauto.
  erewrite seln_map.
  unfold log_data_blocks_rep in *; cleanup.
  erewrite <- e.
  edestruct H2; eauto.
  cleanup; eauto.
  lia.
  setoid_rewrite H4; lia.
Qed.

Lemma log_read_encrypted_log_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 hdr1 hdr2 vp  txns1 txns2,
exec CryptoDiskLang u o1 s1
read_encrypted_log (Finished s1' r1) ->
log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->

Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 

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
    eapply_fresh log_read_header_finished_oracle_eq in H; eauto; cleanup.
    eapply read_header_finished in H; eauto.
    eapply read_header_finished in H9; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    cleanup.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H7; eauto; cleanup.
    unfold log_reboot_rep_explicit_part  in *; cleanup.
    eapply read_consecutive_log_finished in H12; eauto.
    eapply read_consecutive_log_finished in H7; eauto.
    cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_check_hash_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.
    repeat rewrite firstn_length_l; eauto.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H11; lia.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H17; lia.

    repeat rewrite <- app_assoc in *.
    eapply_fresh log_check_hash_finished_oracle_eq in H8; eauto; cleanup; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    repeat rewrite firstn_length_l; eauto.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H18; lia.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H12; lia.


    unfold check_hash in *.
    repeat invert_exec; simpl in *; cleanup;
    try congruence.
    clear H10.

    eapply BatchOperations.hash_all_finished in H8.
    eapply BatchOperations.hash_all_finished in H7.
    cleanup.
    unfold log_rep_explicit,
    log_rep_inner,
    header_part_is_valid in *; logic_clean.
    destruct vp; try congruence.
    apply H6; eauto.
    unfold log_rep_explicit in *; logic_clean; eauto.
    unfold log_rep_explicit in *; logic_clean; eauto.
  }
  {
    repeat rewrite <- app_assoc in *.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_read_header_finished_not_crashed; eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh log_read_header_finished_oracle_eq in H; eauto; cleanup.
    eapply read_header_finished in H; eauto.
    eapply read_header_finished in H10; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    cleanup.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    4: eauto.
    3:eauto.
    all: eauto.
    rewrite <- H2 in *; eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H7; eauto; cleanup.
    unfold log_reboot_rep_explicit_part  in *; cleanup.
    eapply read_consecutive_log_finished in H13; eauto.
    eapply read_consecutive_log_finished in H7; eauto.
    cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_check_hash_finished_not_crashed.
    eauto.
    3:eauto.
    all: eauto.
    repeat rewrite firstn_length_l; eauto.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H12; lia.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H18; lia.

    unfold check_hash in *.
    repeat invert_exec; simpl in *; cleanup;
    try congruence.

    eapply BatchOperations.hash_all_finished in H8.
    eapply BatchOperations.hash_all_finished in H7.
    cleanup.
    unfold log_rep_explicit,
    log_rep_inner,
    header_part_is_valid in *; logic_clean.
    destruct vp; try congruence.
    apply H1; eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh log_check_hash_finished_oracle_eq in H8; eauto; cleanup; eauto.
    repeat invert_exec; simpl in *; cleanup;
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    4: eauto.
    3:eauto.
    all: eauto.
    rewrite <- H3 in *; eauto.
    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H9; eauto; cleanup.
    simpl in *; cleanup.

    repeat rewrite firstn_length_l; eauto.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H19; lia.
    unfold log_rep_explicit in *; cleanup.
    rewrite map_length; 
    setoid_rewrite H13; lia.

    unfold log_rep_explicit in *; logic_clean; eauto.
    unfold log_rep_explicit in *; logic_clean; eauto. 
  }
Qed.

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
addr_count rec1 = addr_count rec2 ->
data_count rec1 = data_count rec2 ->
start rec1 = start rec2 ->
start rec1 + addr_count rec1 + data_count rec1 <= length l1 ->
start rec2 + addr_count rec2 + data_count rec2 <= length l2 ->
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
  repeat rewrite firstn_length_l; eauto.
  rewrite skipn_length; lia.
  rewrite skipn_length; lia.

  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite firstn_length_l; eauto.
  rewrite skipn_length; lia.
  rewrite skipn_length; lia.
Qed.

Lemma log_decrypt_txns_finished_not_crashed:
forall u recs1 recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(decrypt_txns recs1 l1) (Finished s1' r1) ->

Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) recs1 recs2 -> 
Forall (fun rec1 => start rec1 + addr_count rec1 + data_count rec1 <= length l1) recs1 ->
Forall (fun rec2 => start rec2 + addr_count rec2 + data_count rec2 <= length l2) recs2 ->

length l1 = length l2 ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(decrypt_txns recs2 l2) (Crashed s2').
Proof.
  unfold not; 
  induction recs1; destruct recs2; simpl; intros;
  eapply_fresh forall2_length in H0; simpl in *; try lia.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  inversion H0; clear H0; subst; eauto.
  inversion H1; clear H1; subst; eauto.
  inversion H2; clear H2; subst; eauto.
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
  lia.

  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  eapply IHrecs1; eauto.
  rewrite <- H3 in *; eauto.

  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txns_finished_oracle_eq in H3. 
  4: eauto.
  all: eauto. 
  cleanup; simpl in *; cleanup.
Qed.


Lemma log_recover_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 hdr1 hdr2 txns1 txns2 vp,
exec CryptoDiskLang u o1 s1
Log.recover (Finished s1' r1) ->

log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->

Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (old_part hdr1)) (Log.records (old_part hdr2)) -> 

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
  eapply log_read_encrypted_log_finished_oracle_eq in H12.
  7: eauto. 
  3: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  eapply log_write_header_finished_not_crashed; eauto.
  
  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_oracle_eq in H12.
  7: eauto. 
  3: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H8; eauto. 
  cleanup; simpl in *; cleanup.

  repeat rewrite <- app_assoc in *.
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H12.
  7: eauto. 
  3: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H8; eauto. 
  cleanup; simpl in *; cleanup.
  eapply log_decrypt_txns_finished_not_crashed. 
  7: eauto.
  all: eauto.
  {
    unfold log_reboot_rep_explicit_part in *; logic_clean.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H12; eauto.
    cleanup_no_match.
    repeat cleanup_pairs.
    destruct vp; eauto.
  }
  {
    unfold log_reboot_rep_explicit_part in *; logic_clean.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H12; eauto.
    cleanup_no_match.
    repeat cleanup_pairs.
    unfold log_rep_explicit, log_rep_inner,
    txns_valid, header_part_is_valid in *; logic_clean; simpl in *.
    rewrite <- H31.
    apply Forall_forall; intros.
    apply in_map_iff in H37; logic_clean; subst.
    eapply Forall_forall in H32; eauto.
    unfold txn_well_formed, record_is_valid in *; logic_clean.
    rewrite firstn_length_l; eauto.
    rewrite map_length.
    setoid_rewrite H27; eauto.
  }
  {
    unfold log_reboot_rep_explicit_part in *; logic_clean.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H12; eauto.
    cleanup_no_match.
    repeat cleanup_pairs.
    unfold log_rep_explicit, log_rep_inner,
    txns_valid, header_part_is_valid in *; logic_clean; simpl in *.
    rewrite <- H18.
    apply Forall_forall; intros.
    apply in_map_iff in H37; logic_clean; subst.
    eapply Forall_forall in H19; eauto.
    unfold txn_well_formed, record_is_valid in *; logic_clean.
    rewrite firstn_length_l; eauto.
    rewrite map_length.
    setoid_rewrite H11; eauto.
  }
  {
    unfold log_reboot_rep_explicit_part in *; logic_clean.
    eapply read_encrypted_log_finished in H; eauto.
    eapply read_encrypted_log_finished in H12; eauto.
    cleanup_no_match.
    repeat cleanup_pairs.
    unfold log_rep_explicit, log_rep_inner,
    txns_valid, header_part_is_valid in *; logic_clean; simpl in *.
    repeat rewrite firstn_length_l; eauto.
    destruct vp; eauto.
    rewrite map_length.
    setoid_rewrite H11; eauto.
    rewrite map_length.
    setoid_rewrite H27; eauto.
  }
Qed.


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
Forall2 (fun l1 l2 => length (fst l1) = length (fst l2)) a1 a2 ->
~exec CachedDiskLang u o2 s2
(LogCache.write_lists_to_cache a2) (Crashed s2').
Proof.
  unfold not; induction a1; destruct a2; 
  simpl; intros;
  eapply_fresh forall2_length in H1; simpl in *;  try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  inversion H1; clear H1; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_not_crashed; eauto.

  inversion H1; clear H1; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_oracle_eq in H; eauto.
  cleanup; eauto.
Qed.

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
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 hdr1 hdr2 txns1 txns2 vp,
exec CachedDiskLang u o1 s1
recover (Finished s1' r1) ->

log_reboot_rep_explicit_part  hdr1 txns1 vp (snd s1) ->
log_reboot_rep_explicit_part  hdr2 txns2 vp (snd s2) ->

Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (old_part hdr1)) (Log.records (old_part hdr2)) -> 

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
  eapply map_ext_eq_prefix in H8.
  cleanup.
  eapply log_recover_finished_not_crashed; eauto.
  solve [repeat constructor].
  intros; cleanup; intuition congruence.

  repeat rewrite <- app_assoc in *.
  eapply_fresh map_ext_eq_prefix in H8.
  cleanup.
  eapply log_recover_finished_oracle_eq in H6; eauto.
  cleanup.
  eapply write_lists_to_cache_finished_not_crashed.
  4: eauto.
  eauto.
  all: eauto.
  {
    eapply Specs.recover_finished in H12; eauto.
    2: unfold log_reboot_rep; eauto.
    eapply Specs.recover_finished in H14; eauto.
    2: unfold log_reboot_rep; eauto.
    cleanup.
    eapply_fresh forall2_length in H4.
    eapply_fresh forall2_length in H5.
    destruct vp; simpl in *.
    {
      eapply forall2_forall in H4.
      eapply forall_forall2.
      eapply Forall_forall; intros.
      setoid_rewrite <- combine_map' in H14.
      setoid_rewrite <- combine_map' in H14.
      apply in_map_iff in H14.
      cleanup.
      repeat cleanup_pairs.
      unfold log_reboot_rep_explicit_part, log_rep_explicit, 
      log_rep_inner, txns_valid in *; logic_clean.
      apply in_combine_combine_same in H16; simpl in *; logic_clean.
      subst.
      rewrite <- H20, <- H29 in *.
      eapply Forall_forall in H4; eauto.
      2: setoid_rewrite <- combine_map';
        apply in_map; eauto.
      simpl in *.

      eapply in_seln_exists in H16; cleanup_no_match.
      erewrite seln_combine in H0.
      simpl in *;
      inversion H0; subst.
      eapply Forall_forall in H30.
      2: eapply in_seln with (n:= x5).
      unfold txn_well_formed, record_is_valid in *;
      simpl in *; logic_clean.
      rewrite H33, <- H37 in *; eauto.
      eapply Forall_forall in H21.
      2: eapply in_seln with (n:= x5).
      unfold txn_well_formed, record_is_valid in *;
      simpl in *; logic_clean.
      rewrite H44, <- H48 in *; eauto.
      repeat rewrite firstn_length_l; eauto.
      rewrite H14, H16; eauto.
      rewrite combine_length in H; lia.
      rewrite combine_length in H; lia.
      rewrite <- H20, <- H29 in *.
      repeat rewrite map_length in Hx; eauto.
      repeat rewrite combine_length; 
      repeat rewrite map_length.
      unfold log_reboot_rep_explicit_part, log_rep_explicit, 
      log_rep_inner, txns_valid in *; logic_clean.
      rewrite <- H23, <- H32 in *.
      repeat rewrite map_length in Hx; eauto.
    }
    {
      eapply forall2_forall in H5.
      eapply forall_forall2.
      eapply Forall_forall; intros.
      setoid_rewrite <- combine_map' in H14.
      setoid_rewrite <- combine_map' in H14.
      apply in_map_iff in H14.
      cleanup.
      repeat cleanup_pairs.
      unfold log_reboot_rep_explicit_part, log_rep_explicit, 
      log_rep_inner, txns_valid in *; logic_clean.
      apply in_combine_combine_same in H16; simpl in *; logic_clean.
      subst.
      rewrite <- H20, <- H29 in *.
      eapply Forall_forall in H5; eauto.
      2: setoid_rewrite <- combine_map';
        apply in_map; eauto.
      simpl in *.

      eapply in_seln_exists in H16; cleanup_no_match.
      erewrite seln_combine in H0.
      simpl in *;
      inversion H0; subst.
      eapply Forall_forall in H30.
      2: eapply in_seln with (n:= x5).
      unfold txn_well_formed, record_is_valid in *;
      simpl in *; logic_clean.
      rewrite H33, <- H37 in *; eauto.
      eapply Forall_forall in H21.
      2: eapply in_seln with (n:= x5).
      unfold txn_well_formed, record_is_valid in *;
      simpl in *; logic_clean.
      rewrite H44, <- H48 in *; eauto.
      repeat rewrite firstn_length_l; eauto.
      rewrite H14, H16; eauto.
      rewrite combine_length in H; lia.
      rewrite combine_length in H; lia.
      rewrite <- H20, <- H29 in *.
      repeat rewrite map_length in Hx0; eauto.
      repeat rewrite combine_length; 
      repeat rewrite map_length.
      unfold log_reboot_rep_explicit_part, log_rep_explicit, 
      log_rep_inner, txns_valid in *; logic_clean.
      rewrite <- H23, <- H32 in *.
      repeat rewrite map_length in Hx0; eauto.
    }
  }
  solve [repeat constructor].
  intros; cleanup; intuition congruence.
  Unshelve.
  all: repeat constructor; exact key0.
Qed.

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
