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
(* length l1 = length l2 -> *)
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
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
(*length l1 = length l2 ->*)
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
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
(* length k1 = length k2 ->
length l1 = length l2 -> *)
o1 = o2.
Proof.
  unfold BatchOperations.write_batch.
  induction k1; destruct k2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat (repeat invert_exec; cleanup; eauto; simpl in *; cleanup; try lia).
  repeat (repeat invert_exec; cleanup; eauto; simpl in *; cleanup; try lia).
  repeat (repeat invert_exec; cleanup; eauto; simpl in *; cleanup; try lia).
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHk1 in H0; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_write_consecutive_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,

exec CryptoDiskLang u o1 s1
(BatchOperations.write_consecutive k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.write_consecutive k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
(*length l1 = length l2 ->*)
o1 = o2.
Proof.
  unfold BatchOperations.write_consecutive.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
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
(*l1 = l2 ->*)
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply IHl1 in H1; eauto.
  subst; eauto.
Qed.

Lemma BatchOperations_decrypt_all_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.decrypt_all k1 l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.decrypt_all k2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
(*length l1 = length l2 ->*)
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
  repeat invert_exec; cleanup; eauto.
  repeat rewrite <- app_assoc in *; cleanup.
  simpl in *; cleanup.
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
(*length (a2 ++ v2) = length (a1 ++ v1) ->*)
o1 = o2.
Proof.
  unfold commit_txn; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto; try lia.
  repeat rewrite <- app_assoc in *; cleanup.

  eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
  simpl in *; cleanup.

  repeat rewrite <- app_assoc in *; cleanup.
  eapply_fresh BatchOperations_encrypt_all_finished_oracle_eq in H12; eauto. 
  cleanup.

  eapply BatchOperations.encrypt_all_finished in H12.
  eapply BatchOperations.encrypt_all_finished in H3.
  cleanup.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply_fresh BatchOperations_hash_all_finished_oracle_eq in H14; eauto. 
  cleanup.

  eapply BatchOperations.hash_all_finished in H14.
  eapply BatchOperations.hash_all_finished in H5.
  cleanup.
  repeat rewrite <- app_assoc in *; cleanup.
  eapply BatchOperations_write_consecutive_finished_oracle_eq in H15; eauto. 
  cleanup.

  repeat rewrite <- app_assoc in *; cleanup.
  eapply log_update_header_finished_oracle_eq in H16; eauto.
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
(*
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
(length a2 + length v2)) -> *)
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
    Transparent read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup.
    simpl in *; congruence.
    Opaque read_header.
  }
  {
    Transparent read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup.
    simpl in *; congruence.
    Opaque read_header.
  }
  {
    eapply log_commit_txn_finished_oracle_eq in H3; eauto.
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
(*length l1 = length l2 ->*)
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

(*Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> *)

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
      eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H6; eauto. 
      cleanup.
      eapply_fresh log_check_hash_finished_oracle_eq in H7; eauto. 
      cleanup; eauto.
      (*
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      eapply BatchOperations.read_consecutive_finished in H4; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H6; eauto; cleanup.
      eauto.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup; eauto.
      *)
  }
  
  {
      unfold check_hash in *; repeat invert_exec; try congruence.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup.
      eapply BatchOperations.read_consecutive_finished in H4; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H6; eauto; cleanup.
      eapply BatchOperations.hash_all_finished in H5; eauto; cleanup. 
      eapply BatchOperations.hash_all_finished in H7; eauto; cleanup.

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
        setoid_rewrite H29; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H6; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e1; eauto.
        lia.
        setoid_rewrite H29; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H29; eauto.
      }
      assert(firstn (count (current_part
      (decode_header (fst (snd s2 hdr_block_num))))) (map fst x2) = x6). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H21; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H0; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e; eauto.
        lia.
        setoid_rewrite H21; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H21; eauto.
      }
      subst.
      unfold log_rep_inner, header_part_is_valid in *; logic_clean.
      destruct vp; eauto.
      apply H7; eauto.
  }
  {
      unfold check_hash in *; repeat invert_exec; try congruence.
      eapply read_header_finished in H; eauto.
      eapply read_header_finished in H0; eauto.
      cleanup.
      eapply BatchOperations.read_consecutive_finished in H4; eauto; cleanup. 
      eapply BatchOperations.read_consecutive_finished in H7; eauto; cleanup.
      eapply BatchOperations.hash_all_finished in H5; eauto; cleanup. 
      eapply BatchOperations.hash_all_finished in H8; eauto; cleanup.

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
        setoid_rewrite H29; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H7; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e1; eauto.
        lia.
        setoid_rewrite H29; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H29; eauto.
      }
      assert(firstn (count (current_part
      (decode_header (fst (snd s2 hdr_block_num))))) (map fst x2) = x6). {
        eapply list_seln_ext.
        cleanup.
        rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H21; eauto.
        rewrite firstn_length_l; eauto.
        intros.
        rewrite seln_firstn.
        erewrite seln_map.
        edestruct H0; eauto.
        cleanup.
        unfold log_data_blocks_rep in *; cleanup.
        rewrite <- e; eauto.
        lia.
        setoid_rewrite H21; eauto. lia.
        eauto.
        rewrite map_length.
        setoid_rewrite H21; eauto.
      }
      subst.
      unfold log_rep_inner, header_part_is_valid in *; logic_clean.
      destruct vp; eauto.
      apply H26; eauto.
  }
  {
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H7.
    2: apply H4. 
    all: eauto. 
    cleanup.

    eapply_fresh log_check_hash_finished_oracle_eq in H8; eauto. 
    cleanup; eauto.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H9; eauto.
    cleanup; eauto.
    (*
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
    *)
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
(* length l1 = length l2 ->
addr_count txn_rec1 = addr_count txn_rec2 ->
data_count txn_rec1 = data_count txn_rec2 ->
start txn_rec1 = start txn_rec2 ->
*)
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
(*start txn_rec1 +
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
length l2 = length l1 -> *)
o1 = o2.
Proof.
  Transparent apply_txn.
  unfold apply_txn; simpl; intros.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply_fresh log_decrypt_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply BatchOperations_write_batch_finished_oracle_eq in H3; eauto.
  cleanup; eauto.
  (*
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
  *)
Qed.


Lemma log_apply_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(apply_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(apply_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; simpl in *; try lia.
  repeat invert_exec; eauto.
  {
    repeat invert_exec; eauto.
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    inversion H3; subst;
    inversion H5; subst;
    destruct (addr_count t); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D0.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    congruence.
    repeat invert_exec; eauto.
    congruence.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  {
    repeat invert_exec; eauto.
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    inversion H2; subst;
    inversion H4; subst;
    destruct (addr_count a); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D0.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    congruence.
    repeat invert_exec; eauto.
    congruence.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  repeat invert_exec; eauto.
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  repeat rewrite <- app_assoc in *.
  eapply log_apply_txn_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHtxn_recs1 in H6; eauto.
  cleanup; eauto.
Qed.

Lemma log_decrypt_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(decrypt_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(decrypt_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; try lia.
  repeat invert_exec; eauto.
  repeat invert_exec; eauto.
  {
    repeat invert_exec; eauto.
    unfold decrypt_txn in *.
    repeat invert_exec; eauto.
    inversion H3; subst;
    inversion H5; subst;
    destruct (addr_count t); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  {
    repeat invert_exec; eauto.
    unfold decrypt_txn in *.
    repeat invert_exec; eauto.
    inversion H2; subst;
    inversion H4; subst;
    destruct (addr_count a); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  unfold decrypt_txn in *.
  repeat rewrite <- app_assoc in *.
  repeat invert_exec; eauto.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H; eauto.
  inversion H2; subst;
    inversion H4; subst;
    inversion H3; subst;
    inversion H5; subst;
    cleanup.
    repeat rewrite <- app_assoc in *.
  eapply IHtxn_recs1 in H6; eauto.
  cleanup; eauto.
Qed.


Lemma log_flush_txns_finished_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2,
exec CryptoDiskLang u o1 s1
(flush_txns txn_recs1 l1) (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(flush_txns txn_recs2 l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Transparent flush_txns.
  unfold flush_txns; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  simpl in *; try lia;
  repeat rewrite <- app_assoc in *.
  eapply log_apply_txns_finished_oracle_eq in H0; only 2: apply H; eauto.
  simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_update_header_finished_oracle_eq in H12; eauto.
  cleanup; eauto.
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

(* 
count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 
*)
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
  unfold log_header_rep, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished in H; eauto.
  eapply read_encrypted_log_finished in H0; eauto.
  cleanup; simpl in *.
  all: intros; try congruence.
  eapply log_flush_txns_finished_oracle_eq in H5; simpl; eauto.
  subst; eauto.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    eapply Forall_forall in H20; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    eapply Forall_forall in H28; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H20; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    rewrite map_length; setoid_rewrite H15. lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H28; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    rewrite map_length; setoid_rewrite H23. lia.
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

(*
count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (old_part hdr1)) (records (old_part hdr2)) -> 
*)

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
  eapply log_write_header_finished_oracle_eq in H8; eauto.
  cleanup.
  simpl in *; cleanup.
  unfold log_reboot_rep_explicit_part, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished in H; eauto.
  eapply read_encrypted_log_finished in H0; eauto.
  cleanup_no_match; simpl in * .
  all: intros; try congruence.
  eapply log_decrypt_txns_finished_oracle_eq in H6. 
  3: eauto.
  all: eauto.
  cleanup; eauto.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H34, <- H26 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H35; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H34, <- H26 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H27; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H34, <- H26 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H35; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
    rewrite map_length; setoid_rewrite H30. cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H34, <- H26 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H27; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
    rewrite map_length; setoid_rewrite H22. 
    cleanup; lia.
  }
  (*
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
  *)
Qed.

Lemma log_init_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 ,
exec CryptoDiskLang u o1 s1
(Log.init l1)  (Finished s1' r1) ->
exec CryptoDiskLang u o2 s2
(Log.init l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
(* length l1 = length l2 -> *)
o1 = o2.
Proof.
  Transparent Log.init.
  unfold Log.init; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H; eauto.
  cleanup.
  eapply BatchOperations_write_batch_finished_oracle_eq in H5; eauto.
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
(* length l1 = length l2 -> *)
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
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) l1 -> 
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) l2 -> 
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros;  simpl in *; try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  {
    repeat invert_exec; eauto.
    inversion H3; cleanup; subst;
    destruct (fst p), (snd p); simpl in *; try lia; simpl in *.
    repeat invert_exec; eauto.
    simpl in *; cleanup.
  }
  {
    repeat invert_exec; eauto.
    inversion H2; cleanup; subst;
    destruct (fst a), (snd a); simpl in *; try lia; simpl in *.
    repeat invert_exec; eauto.
    simpl in *; cleanup.
  }
  repeat invert_exec; eauto.
  inversion H2; subst;
  inversion H3; subst;
  repeat rewrite <- app_assoc in *.
  eapply write_batch_to_cache_finished_oracle_eq in H; eauto.
  cleanup.
  eapply IHl1 in H4; eauto.
  cleanup; eauto.
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
(*
count (current_part hdr1) = count (current_part hdr2) ->
count (old_part hdr1) = count (old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (current_part hdr1)) (records (current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (records (old_part hdr1)) (records (old_part hdr2)) -> 
*)
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold recover; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat rewrite <- app_assoc in *.
  eapply_fresh map_ext_eq_prefix in H13; cleanup.
  eapply_fresh log_recover_finished_oracle_eq in H12; 
  only 2: apply H8; eauto.
  cleanup.
  eapply Specs.recover_finished in H8; eauto.
  eapply Specs.recover_finished in H12; eauto.
  cleanup; eauto.
  eapply write_lists_to_cache_finished_oracle_eq in H6. 
  3: eauto.
  all: eauto.
  cleanup; eauto.
  shelve.
  shelve.
  unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  repeat constructor.
  apply key0.
  intros; cleanup; try congruence.
  Unshelve.
  all: try solve [repeat constructor; exact key0].
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H16.
    apply in_map_iff in H16; cleanup; simpl in *.
    apply in_combine_same in H17; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H31; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
  }
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H16.
    apply in_map_iff in H16; cleanup; simpl in *.
    apply in_combine_same in H17; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H23; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
  }
Qed.


Lemma init_finished_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 ,
exec CachedDiskLang u o1 s1
(init l1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(init l2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
(* length l1 = length l2 -> *)
o1 = o2.
Proof.
  unfold init; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  apply map_ext_eq_prefix in H9; eauto; cleanup.
  eapply log_init_finished_oracle_eq in H7; eauto.
  subst; eauto.
  repeat constructor.
  exact key0.
  intros; cleanup; intuition congruence.
Qed.




Lemma write_finished_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 r2 a1 a2 v1 v2 hdr1 hdr2 txns1 txns2,
(*
Coq.Bool.Sumbool.bool_of_sumbool(Forall_dec (fun a : nat => a < data_length)
(fun a : nat => lt_dec a data_length) a1) = 
Coq.Bool.Sumbool.bool_of_sumbool (Forall_dec (fun a : nat => a < data_length)
(fun a : nat => lt_dec a data_length) a2) -> 
NoDup_dec a1 = NoDup_dec a2 ->
Nat.eq_dec (length a1) (length v1) = Nat.eq_dec (length a2) (length v2) ->
le_dec (length (addr_list_to_blocks (map (Init.Nat.add data_start) a1)) +
length v1) log_length = 
le_dec (length (addr_list_to_blocks (map (Init.Nat.add data_start) a2)) +
length v2) log_length ->

length a1 = length a2 ->
length a1 = length v1 ->
length a2 = length v2 ->

count (current_part (decode_header (fst (snd (snd s1) hdr_block_num))))  =
count (current_part (decode_header (fst (snd (snd s2) hdr_block_num)))) ->
count
  (old_part
     (decode_header (fst (snd (snd s1) hdr_block_num)))) =
count
  (old_part
     (decode_header (fst (snd (snd s2) hdr_block_num)))) ->

Forall2
  (fun rec1 rec2 : txn_record =>
   addr_count rec1 = addr_count rec2 /\
   data_count rec1 = data_count rec2 /\
   start rec1 = start rec2)
  (records
     (current_part
        (decode_header
           (fst (snd (snd s1) hdr_block_num)))))
  (records
     (current_part
        (decode_header
           (fst (snd (snd s2) hdr_block_num))))) -> 
*)
log_header_rep hdr1 txns1 (snd s1) ->
log_header_rep hdr2 txns2 (snd s2) ->
(NoDup a1 <-> NoDup a2) ->
(Forall (fun a => a < data_length) a1 <->
Forall (fun a => a < data_length) a2) -> 
exec CachedDiskLang u o1 s1
(write a1 v1)  (Finished s1' r1) ->
exec CachedDiskLang u o2 s2
(write a2 v2) (Finished s2' r2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold write; intros.
  (*
  assert (A: length (addr_list_to_blocks
    (map (Init.Nat.add data_start) a1)) = 
  length (addr_list_to_blocks
    (map (Init.Nat.add data_start) a2))). {
    apply addr_list_to_blocks_length_eq; eauto.
    repeat rewrite map_length; eauto.
  }
  *)
  cleanup; try solve [intuition eauto; lia]. 
  {
    repeat invert_exec; simpl in *; cleanup;
  eauto.

  {
    simpl in *.
    repeat rewrite <-  app_assoc in *; cleanup.
    eapply_fresh map_ext_eq_prefix in H5; eauto.
    cleanup. 
    eapply log_commit_finished_oracle_eq in H10; eauto; cleanup.
    simpl in *; cleanup.
    eapply write_batch_to_cache_finished_oracle_eq in H11; subst; eauto.
    subst; eauto.
    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
  }
  {
    exfalso; simpl in *.
    repeat rewrite <-  app_assoc in *; cleanup.
    eapply map_ext_eq_prefix in H5; eauto.
    cleanup. 
    eapply_fresh log_commit_finished_oracle_eq in H10; eauto; cleanup.
    simpl in *; cleanup.

    assert (A0: (firstn (length v1)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a1)))) = (map (Init.Nat.add data_start)
          a1)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a1)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    assert (A1: (firstn (length v2)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a2)))) = (map (Init.Nat.add data_start)
          a2)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a2)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    eapply commit_finished_oracle in H8; eauto.
    eapply commit_finished_oracle in H10; eauto.
    repeat split_ors; logic_clean; try congruence; try lia.
    all: try setoid_rewrite A0; try setoid_rewrite A1; eauto.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a1)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.

    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.

    lia.
    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a2)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.
    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
  }
  {
    exfalso; simpl in *.
    repeat rewrite <-  app_assoc in *; cleanup.
    eapply map_ext_eq_prefix in H5; eauto.
    cleanup. 
    eapply_fresh log_commit_finished_oracle_eq in H16; 
    try apply H8; eauto; cleanup.
    simpl in *; cleanup.

    assert (A0: (firstn (length v1)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a1)))) = (map (Init.Nat.add data_start)
          a1)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a1)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    assert (A1: (firstn (length v2)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a2)))) = (map (Init.Nat.add data_start)
          a2)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a2)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    eapply commit_finished_oracle in H8; eauto.
    eapply commit_finished_oracle in H16; eauto.

    repeat split_ors; logic_clean; try congruence; try lia.
    all: try setoid_rewrite A0; try setoid_rewrite A1; eauto.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a1)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.

    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a2)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.
    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
  }
  {
    simpl in *.
    repeat rewrite <-  app_assoc in *; cleanup.
    eapply_fresh map_ext_eq_prefix in H5; eauto.
    cleanup. 
    eapply_fresh log_commit_finished_oracle_eq in H16; 
    try apply H8; eauto; cleanup.
    simpl in *; cleanup.
    eapply_fresh map_ext_eq_prefix in H5; eauto.
    cleanup.
    assert (A0: (firstn (length v1)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a1)))) = (map (Init.Nat.add data_start)
          a1)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a1)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    assert (A1: (firstn (length v2)
    (blocks_to_addr_list
      (addr_list_to_blocks
        (map (Init.Nat.add data_start)
          a2)))) = (map (Init.Nat.add data_start)
          a2)). {
      edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
      a2)).
      cleanup.
      apply firstn_app2.
      rewrite map_length; lia.
    }
    eapply commit_finished in H8; eauto.
    eapply commit_finished in H16; eauto.
    simpl in *;
    repeat split_ors; logic_clean; repeat rewrite app_length in *; try congruence; try lia.
    eapply_fresh log_apply_log_finished_oracle_eq in H11; 
    try apply H19; subst; eauto.
    cleanup.
    eapply apply_log_finished in H11; eauto.
    eapply apply_log_finished in H19; eauto.
    unfold log_rep in *; cleanup. 
    repeat rewrite <- app_assoc in *.
    eapply_fresh map_ext_eq_prefix in H16; eauto.
    cleanup.

    eapply_fresh log_commit_finished_oracle_eq in H22; 
    try apply H14; eauto; cleanup.
    simpl in *; cleanup.
    eapply commit_finished in H14; eauto.
    eapply commit_finished in H22; eauto.
    unfold log_rep_general, log_rep_explicit, log_rep_inner, header_part_is_valid
    , txns_valid in *;
    simpl in *; logic_clean.
    repeat match goal with
    | [H: [] = _ |- _ ] =>
    rewrite <- H in *; clear H
    end.
    simpl in *.
    repeat split_ors; logic_clean; repeat rewrite app_length in *; try congruence; try lia.

    eapply write_batch_to_cache_finished_oracle_eq in H17; 
    subst; eauto.
    subst; eauto.
    all: try setoid_rewrite H1; try setoid_rewrite A0; try setoid_rewrite A1; eauto.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a1)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.

    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a2)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.
    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.
   
    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup; eauto.
    try solve [do 2 eexists; intuition eauto].
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup; eauto.
    try solve [do 2 eexists; intuition eauto].
    cleanup.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    try setoid_rewrite A0; try setoid_rewrite A1; eauto.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a1)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia.

    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    apply Forall_map.
    eapply Forall_impl; eauto.
    pose proof data_fits_in_disk.
    simpl; intros; split; lia.

    edestruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start)
    a2)).
    unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit, 
    log_header_block_rep in *; cleanup.
    repeat rewrite app_length in *.
    rewrite map_length; lia. 
    erewrite addr_list_to_blocks_length_eq.
    2: rewrite map_length; eauto.
    apply addr_list_to_blocks_length_nonzero; eauto.
    lia.

    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
    repeat econstructor. 
    exact key0.
    intuition; cleanup; congruence.
  }
  }
  all: try solve [exfalso; intuition eauto; lia].
  all: repeat invert_exec; eauto.
  Transparent commit read_header.
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  solve [unfold commit, read_header in H7; repeat invert_exec;
  simpl in *; congruence].
  Opaque commit read_header.
Qed.

 

(* Finished Not Crashed proofs*)
Lemma BatchOperations_read_consecutive_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.read_consecutive st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(* n1 = n2 -> *)
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
Qed.

Lemma BatchOperations_hash_all_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.hash_all st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(*length n1 = length n2 ->*)
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
Qed.

Lemma BatchOperations_decrypt_all_finished_not_crashed:
forall u n1 n2 st1 st2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.decrypt_all st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(* length n1 = length n2 -> *)
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
Qed.

Lemma BatchOperations_write_batch_finished_not_crashed:
forall u st1 st2 n1 n2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(BatchOperations.write_batch st1 n1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(* 
length st1 = length st2 ->
length n1 = length n2 ->
*)
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
  3: eauto.
  all: eauto.

  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_write_batch_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
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
(* length l1 = length l2 -> *)
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
(*
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
*)
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
    eapply read_header_finished in H6; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    cleanup.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    eauto.
    2:eauto.
    all: eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H4; eauto; cleanup.
    unfold log_reboot_rep_explicit_part  in *; cleanup.
    eapply read_consecutive_log_finished in H9; eauto.
    eapply read_consecutive_log_finished in H4; eauto.
    cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_check_hash_finished_not_crashed.
    eauto.
    2:eauto.
    all: eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh log_check_hash_finished_oracle_eq in H5; eauto; cleanup; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.


    unfold check_hash in *.
    repeat invert_exec; simpl in *; cleanup;
    try congruence.
    clear H7.

    eapply BatchOperations.hash_all_finished in H5.
    eapply BatchOperations.hash_all_finished in H4.
    cleanup.
    unfold log_rep_explicit,
    log_rep_inner,
    header_part_is_valid in *; logic_clean.
    destruct vp; try congruence.
    apply H3; eauto.
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
    eapply read_header_finished in H7; eauto.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    cleanup.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    3: eauto.
    2:eauto.
    all: eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H4; eauto; cleanup.
    unfold log_reboot_rep_explicit_part  in *; cleanup.
    eapply read_consecutive_log_finished in H10; eauto.
    eapply read_consecutive_log_finished in H4; eauto.
    cleanup.
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply log_check_hash_finished_not_crashed.
    eauto.
    2:eauto.
    all: eauto.

    unfold check_hash in *.
    repeat invert_exec; simpl in *; cleanup;
    try congruence.

    eapply BatchOperations.hash_all_finished in H5.
    eapply BatchOperations.hash_all_finished in H4.
    cleanup.
    unfold log_rep_explicit,
    log_rep_inner,
    header_part_is_valid in *; logic_clean.
    destruct vp; try congruence.
    apply H1; eauto.

    repeat rewrite <- app_assoc in *.
    eapply_fresh log_check_hash_finished_oracle_eq in H5; eauto; cleanup; eauto.
    repeat invert_exec; simpl in *; cleanup;
    try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup;
    eauto.
    eapply BatchOperations_read_consecutive_finished_not_crashed.
    3: eauto.
    2: eauto.
    all: eauto.
    repeat rewrite <- app_assoc in *.
    eapply_fresh BatchOperations_read_consecutive_finished_oracle_eq in H6; eauto; cleanup.
    simpl in *; cleanup.

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

Lemma log_update_header_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 h1 h2,
exec CryptoDiskLang u o1 s1
(update_header h1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(update_header h2) (Crashed s2').
Proof.
  Transparent update_header read_header.
  unfold update_header, read_header, write_header, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  Opaque read_header.
Qed.

Lemma log_decrypt_txn_finished_not_crashed:
forall u rec1 rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(decrypt_txn rec1 l1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(*
addr_count rec1 = addr_count rec2 ->
data_count rec1 = data_count rec2 ->
start rec1 = start rec2 ->
start rec1 + addr_count rec1 + data_count rec1 <= length l1 ->
start rec2 + addr_count rec2 + data_count rec2 <= length l2 ->
*)
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
  3: eauto.
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
Forall (fun rec => addr_count rec > 0) recs1 ->
Forall (fun rec => addr_count rec > 0) recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
recs2 ->
(*
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) recs1 recs2 -> 
Forall (fun rec1 => start rec1 + addr_count rec1 + data_count rec1 <= length l1) recs1 ->
Forall (fun rec2 => start rec2 + addr_count rec2 + data_count rec2 <= length l2) recs2 ->

length l1 = length l2 ->
*)
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(decrypt_txns recs2 l2) (Crashed s2').
Proof.
  unfold not; 
  induction recs1; destruct recs2; simpl; intros; simpl in *; try lia.
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

  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  unfold decrypt_txn in *.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  destruct (firstn
  (addr_count
    t +
   data_count
    t)
  (skipn
    (start
    t) l2)); simpl in *;
    cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  {
    inversion H1; subst;
    inversion H3; subst;
    destruct (addr_count t); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  {
    unfold decrypt_txn in *; repeat invert_exec; simpl in *; cleanup;
    eauto.
    inversion H1; subst;
    inversion H3; subst;
    destruct (addr_count t); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  {
    unfold decrypt_txn in *; repeat invert_exec; simpl in *; cleanup;
    eauto.
    inversion H1; subst;
    inversion H3; subst;
    destruct (addr_count t); try lia; simpl in *.
    cleanup; simpl in *; try lia.
    apply skipn_eq_nil in D.
    split_ors; cleanup; simpl in *; try lia.
    repeat invert_exec; eauto.
    simpl in *; congruence.
  }
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  unfold decrypt_txn in *.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  destruct (firstn
  (addr_count
    a +
   data_count
    a)
  (skipn
    (start
    a) l1)); simpl in *;
    cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_not_crashed. 
  eauto.
  2: eauto.
  eauto.

  inversion H0;
  inversion H1;
  inversion H2;
  inversion H3; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  eapply IHrecs1; eauto.

  inversion H0;
  inversion H1;
  inversion H2;
  inversion H3; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txns_finished_oracle_eq in H8. 
  3: eauto.
  all: eauto. 
  cleanup; simpl in *; cleanup.
Qed.


Lemma log_recover_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 hdr1 hdr2 txns1 txns2 vp,
exec CryptoDiskLang u o1 s1
Log.recover (Finished s1' r1) ->

log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->

(*
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (old_part hdr1)) (Log.records (old_part hdr2)) -> 
*)

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
  eapply log_read_encrypted_log_finished_oracle_eq in H8.
  5: eauto. 
  2: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  eapply log_write_header_finished_not_crashed; eauto.
  
  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_oracle_eq in H8.
  5: eauto. 
  2: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H4; eauto. 
  cleanup; simpl in *; cleanup.

  repeat rewrite <- app_assoc in *.
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H8.
  5: eauto. 
  2: eauto.
  all: eauto.
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H4; eauto. 
  cleanup; simpl in *; cleanup.
  unfold log_reboot_rep_explicit_part in *; logic_clean.
  eapply read_encrypted_log_finished in H; eauto.
  eapply read_encrypted_log_finished in H8; eauto.
  simpl in *; cleanup_no_match.
  eapply log_decrypt_txns_finished_not_crashed. 
  7: eauto.
  all: simpl; eauto.
  all: simpl.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    try rewrite <- H32 in H.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H33; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H24 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H25; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    try rewrite <- H32 in H.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H33; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    cleanup; lia.
    rewrite map_length; setoid_rewrite H28. 
    cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H24 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H25; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    cleanup; lia.
    rewrite map_length; setoid_rewrite H20. 
    cleanup; lia.
  }
Qed.


Lemma log_init_finished_not_crashed:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(Log.init l1) (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
(*length l1 = length l2 ->*)
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
  eapply BatchOperations_write_batch_finished_not_crashed; eauto.
  

  repeat rewrite <- app_assoc in *.
  eapply log_write_header_finished_oracle_eq in H; eauto. 
  cleanup; simpl in *; cleanup.
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_write_batch_finished_oracle_eq in H2; eauto. 
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
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) a1 -> 
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) a2 -> 
~exec CachedDiskLang u o2 s2
(LogCache.write_lists_to_cache a2) (Crashed s2').
Proof.
  unfold not; induction a1; destruct a2; 
  simpl; intros; simpl in *;  try lia;
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).
  {
    repeat invert_exec; eauto.
    inversion H2; cleanup; subst;
    destruct (fst p), (snd p); simpl in *; try lia; simpl in *.
    repeat invert_exec; eauto.
    simpl in *; split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    repeat invert_exec; eauto.
    inversion H2; cleanup; subst;
    destruct (fst p), (snd p); simpl in *; try lia; simpl in *.
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    repeat invert_exec; eauto.
    inversion H1; cleanup; subst;
    destruct (fst a), (snd a); simpl in *; try lia; simpl in *.
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    rewrite <- app_assoc in *.
    eapply write_batch_to_cache_finished_not_crashed; eauto.
  }
  {
    inversion H1; cleanup;
    inversion H2; cleanup;
    repeat rewrite <- app_assoc in *.
    eapply write_batch_to_cache_finished_oracle_eq in H; eauto; cleanup.
    eapply IHa1; eauto.
  }
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
(*
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) ->
Log.count (Log.old_part hdr1) = Log.count (Log.old_part hdr2) ->
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (Log.current_part hdr1)) (Log.records (Log.current_part hdr2)) -> 
Forall2 (fun rec1 rec2 => addr_count rec1 = addr_count rec2 /\
data_count rec1 = data_count rec2 /\
start rec1 = start rec2) (Log.records (old_part hdr1)) (Log.records (old_part hdr2)) -> 
*)
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
  eapply map_ext_eq_prefix in H4.
  cleanup.
  eapply log_recover_finished_not_crashed; eauto.
  solve [repeat constructor].
  intros; cleanup; intuition congruence.

  repeat rewrite <- app_assoc in *.
  eapply_fresh map_ext_eq_prefix in H4.
  cleanup.
  eapply log_recover_finished_oracle_eq in H2; eauto.
  cleanup.
  eapply Specs.recover_finished in H8; eauto.
  2: unfold log_reboot_rep; eauto.
  eapply Specs.recover_finished in H10; eauto.
  2: unfold log_reboot_rep; eauto.
  cleanup.
  eapply write_lists_to_cache_finished_not_crashed.
  5: eauto.
  eauto.
  all: eauto.
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H10.
    apply in_map_iff in H10; cleanup; simpl in *.
    apply in_combine_same in H12; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H29; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
  }
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H10.
    apply in_map_iff in H10; cleanup; simpl in *.
    apply in_combine_same in H12; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H21; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
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
(* length a1 = length a2 -> *)
~exec CachedDiskLang u o2 s2
(init a2) (Crashed s2').
Proof.
  unfold init, not; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  eauto.
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup;
  eauto).

  eapply map_ext_eq_prefix in H7; cleanup.
  eapply log_init_finished_not_crashed. 
  eauto.
  3: eauto.
  all: eauto.
  repeat rewrite combine_length_eq; eauto.
  all: repeat rewrite map_length; eauto.
  solve [repeat econstructor].
  intros; cleanup; intuition congruence.
Qed.

Lemma BatchOperations_encrypt_all_finished_not_crashed:
forall v1 v2 u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2,
exec CryptoDiskLang u o1 s1
(BatchOperations.encrypt_all a1 v1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(BatchOperations.encrypt_all a2 v2) (Crashed s2').
Proof.
  unfold not; induction v1; intros; destruct v2; simpl in *;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup.

  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply IHv1; eauto.
  eapply BatchOperations_encrypt_all_finished_oracle_eq in H; eauto;
  cleanup.
  simpl in *; cleanup.
Qed.


Lemma commit_txn_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit_txn a1 v1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(commit_txn a2 v2) (Crashed s2').
Proof.
  unfold commit_txn, not; intros; cleanup.
  repeat invert_exec; cleanup.
  split_ors; cleanup; simpl in *;
  repeat rewrite <- app_assoc in *.
  eapply log_read_header_finished_not_crashed; eauto.
  eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_encrypt_all_finished_not_crashed; eauto.
  eapply BatchOperations_encrypt_all_finished_oracle_eq in H3; eauto; cleanup.

  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_hash_all_finished_not_crashed; eauto.
  eapply BatchOperations_hash_all_finished_oracle_eq in H5; eauto; cleanup.

  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply BatchOperations_write_batch_finished_not_crashed; eauto.
  eapply BatchOperations_write_consecutive_finished_oracle_eq in H6; eauto; cleanup.

  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.

  Transparent update_header.
  clear H11. (* clear read_header *)
  unfold update_header, write_header in *; 
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply log_read_header_finished_not_crashed; eauto.
  eapply log_read_header_finished_oracle_eq in H5; eauto; cleanup.
  simpl in *; cleanup.
  Opaque update_header.

  eapply log_update_header_finished_oracle_eq in H7; eauto; cleanup.
  simpl in *; cleanup.
Qed.

Lemma commit_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit a1 v1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(commit a2 v2) (Crashed s2').
Proof.
  Transparent commit.
  unfold commit, not; simpl; intros; cleanup.
  repeat invert_exec; cleanup.
  {
    split_ors; cleanup;
    repeat rewrite <- app_assoc in *.
    
    eapply log_read_header_finished_not_crashed; eauto.

    eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.
    repeat invert_exec; simpl in *; cleanup.

    repeat invert_exec; simpl in *; cleanup.
    split_ors; cleanup; simpl in *.

    Transparent read_header.
    unfold commit_txn in *;
    repeat invert_exec; simpl in *; cleanup;
    split_ors; cleanup; simpl in *;
    unfold read_header in *; 
    repeat invert_exec; simpl in *; cleanup;
    try split_ors; cleanup; simpl in *;
    repeat invert_exec; simpl in *; cleanup.

    unfold commit_txn, read_header in *;
    repeat invert_exec; simpl in *; cleanup.
    Opaque read_header.
  }
  {
    split_ors; cleanup; repeat rewrite <- app_assoc in *.
    eapply log_read_header_finished_not_crashed; eauto.
    eapply log_read_header_finished_oracle_eq in H; eauto; cleanup.

    repeat invert_exec; simpl in *; cleanup.
    clear H3. (* clear read_header *)
    Transparent read_header.
    unfold commit_txn, read_header in *;
    repeat invert_exec; simpl in *; cleanup.

    repeat invert_exec; simpl in *; cleanup;
    split_ors; cleanup; simpl in *;
    repeat rewrite <- app_assoc in *.
    eapply commit_txn_finished_not_crashed; eauto.
    eapply log_commit_txn_finished_oracle_eq in H2; eauto; cleanup.
    repeat invert_exec; simpl in *; cleanup.
  }
Qed.

Lemma apply_txn_finished_not_crashed:
forall rec1 rec2 l1 l2 u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(apply_txn rec1 l1)  (Finished s1' r1) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(apply_txn rec2 l2) (Crashed s2').
Proof.
  unfold apply_txn, not; intros;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat rewrite <- app_assoc in *.
  eapply log_decrypt_txn_finished_not_crashed; eauto.
  eapply log_decrypt_txn_finished_oracle_eq in H; eauto; cleanup.
  eapply BatchOperations_write_batch_finished_not_crashed; eauto.
Qed.

Lemma apply_txns_finished_not_crashed:
forall recs1 recs2 l1 l2 u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(apply_txns recs1 l1)  (Finished s1' r1) ->
Forall (fun rec => addr_count rec > 0) recs1 ->
Forall (fun rec => addr_count rec > 0) recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
recs2 ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(apply_txns recs2 l2) (Crashed s2').
Proof.
  unfold not; induction recs1; destruct recs2; simpl; intros;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat rewrite <- app_assoc in *.
  {
    unfold apply_txn in *;
    repeat invert_exec; simpl in *; cleanup;
    split_ors; cleanup; simpl in *;
    repeat rewrite <- app_assoc in *.

    unfold decrypt_txn in *;
    repeat invert_exec; simpl in *; cleanup;
    split_ors; cleanup; simpl in *;
    repeat rewrite <- app_assoc in *.
    destruct ((firstn (addr_count t + data_count t) (skipn (start t) l2))); simpl in *;
    repeat invert_exec; simpl in *; cleanup;
    split_ors; cleanup; simpl in *;
    repeat invert_exec; simpl in *; cleanup;
    repeat rewrite <- app_assoc in *.

    inversion H1; subst;
    inversion H3; subst.
    destruct_fresh ((firstn (addr_count t + data_count t) (skipn (start t) l2))); simpl in *.
    apply length_zero_iff_nil in D.
    rewrite firstn_length_l in D; try lia.
    rewrite skipn_length; lia.
    repeat invert_exec; simpl in *; cleanup.

    unfold decrypt_txn in *;
    repeat invert_exec; simpl in *; cleanup.

    inversion H1; subst;
    inversion H3; subst.
    destruct_fresh ((firstn (addr_count t + data_count t) (skipn (start t) l2))); simpl in *.
    apply length_zero_iff_nil in D.
    rewrite firstn_length_l in D; try lia.
    rewrite skipn_length; lia.
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    unfold apply_txn, decrypt_txn  in *;
    repeat invert_exec; simpl in *; cleanup;
    repeat rewrite <- app_assoc in *.

    inversion H1; subst;
    inversion H3; subst.
    destruct_fresh ((firstn (addr_count t + data_count t) (skipn (start t) l2))); simpl in *.
    apply length_zero_iff_nil in D.
    rewrite firstn_length_l in D; try lia.
    rewrite skipn_length; lia.
    repeat invert_exec; simpl in *; cleanup.
  }
  {
    unfold apply_txn, decrypt_txn  in *;
    repeat invert_exec; simpl in *; cleanup;
    repeat rewrite <- app_assoc in *.
    destruct_fresh ((firstn (addr_count a + data_count a) (skipn (start a) l1))); simpl in *;
    repeat invert_exec; simpl in *; cleanup.
  }
  split_ors; cleanup; simpl in *;
  repeat rewrite <- app_assoc in *.
  eapply apply_txn_finished_not_crashed; eauto.
  eapply log_apply_txn_finished_oracle_eq in H; eauto; cleanup.
  inversion H0; subst;
  inversion H1; subst;
  inversion H2; subst;
  inversion H3; subst; eauto.
Qed.


Lemma log_flush_txns_finished_not_crashed:
forall recs1 recs2 l1 l2 u o1 o2 o3 o4 s1 s2 s1' s2' r1,
exec CryptoDiskLang u o1 s1
(flush_txns recs1 l1)  (Finished s1' r1) ->

Forall (fun rec => addr_count rec > 0) recs1 ->
Forall (fun rec => addr_count rec > 0) recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
recs2 ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
(flush_txns recs2 l2) (Crashed s2').
Proof.
  unfold flush_txns, not; intros.
  repeat invert_exec; simpl in *; cleanup;
  split_ors; cleanup; simpl in *;
  repeat rewrite <- app_assoc in *.
  eapply apply_txns_finished_not_crashed; eauto.
  eapply log_apply_txns_finished_oracle_eq in H; eauto; cleanup.
  repeat invert_exec; simpl in *; cleanup;
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  {
    Transparent update_header.
    unfold update_header, read_header, write_header in *;
    repeat invert_exec; simpl in *; cleanup.
    split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup.
  split_ors; cleanup; simpl in *;
  repeat invert_exec; simpl in *; cleanup.
    Opaque update_header.
  }
  eapply log_update_header_finished_oracle_eq in H7; eauto; cleanup.
  simpl in *; cleanup.
Qed.

Lemma log_apply_log_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 hdr1 hdr2 txns1 txns2 vp,
exec CryptoDiskLang u o1 s1
apply_log  (Finished s1' r1) ->
log_reboot_rep_explicit_part hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part hdr2 txns2 vp s2 ->
o1 ++ o3 = o2 ++ o4 ->
~exec CryptoDiskLang u o2 s2
apply_log (Crashed s2').
Proof.
  Transparent apply_log.
  unfold apply_log, not; intros.
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  split_ors; cleanup; 
  repeat invert_exec; simpl in *; cleanup;
  repeat rewrite <- app_assoc in *.
  eapply log_read_encrypted_log_finished_not_crashed; eauto.
  
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H; eauto; cleanup.
  unfold log_reboot_rep_explicit_part in *; cleanup_no_match.
  eapply read_encrypted_log_finished in H; eauto.
  eapply read_encrypted_log_finished in H5; eauto.
  cleanup_no_match; simpl in *.
  eapply log_flush_txns_finished_not_crashed; only 7: eauto; eauto.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H21, <- H29 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H30; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H21, <- H29 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    eapply Forall_forall in H22; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H21, <- H29 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H30; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    lia.
    rewrite map_length; setoid_rewrite H25. 
    cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H21, <- H29 in *.
    apply in_map_iff in H.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H22; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    lia.
    rewrite map_length; setoid_rewrite H17. 
    cleanup; lia.
  }
Qed.

Opaque apply_log commit.
Lemma write_finished_not_crashed:
forall u o1 o2 o3 o4 s1 s2 s1' s2' r1 a1 a2 v1 v2 txns1 txns2,
exec CachedDiskLang u o1 s1
(write a1 v1)  (Finished s1' r1) ->
log_rep txns1 (snd s1) ->
log_rep txns2 (snd s2) ->
o1 ++ o3 = o2 ++ o4 ->
~exec CachedDiskLang u o2 s2
(write a2 v2) (Crashed s2').
Proof. 
  unfold write, not; intros.
  cleanup.
  all: try match goal with 
  | [H: exec _ _ _ _ (Ret _) (Finished _ _ ),
    H0: exec _ _ _ _ (Ret _) (Crashed _) |- _ ] =>
  repeat invert_exec; cleanup; simpl in *; cleanup
  end.
  {
    repeat invert_exec; simpl in *; cleanup; eauto.
    {
      split_ors; cleanup; repeat invert_exec; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply commit_finished_not_crashed; eauto.

      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply log_commit_finished_oracle_eq in H6; eauto; cleanup.
      split_ors; cleanup; repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply write_batch_to_cache_finished_not_crashed; eauto.

      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply log_commit_finished_oracle_eq in H6; eauto; cleanup.
      split_ors; cleanup; repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.

      split_ors; cleanup; repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      {
        Transparent apply_log.
        unfold apply_log in *.
        repeat invert_exec; simpl in *; cleanup;
        split_ors; cleanup;
        unfold read_encrypted_log in *;
        repeat invert_exec; simpl in *; cleanup;
        try split_ors; cleanup;
        unfold read_header in *;
        repeat invert_exec; simpl in *; cleanup;
        try split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup.
        Opaque apply_log.
      }
      {
        Transparent apply_log.
        unfold apply_log, read_encrypted_log, read_header  in *.
        repeat invert_exec; simpl in *; cleanup.
        Opaque apply_log.
      }
      {
        Transparent apply_log.
        unfold apply_log, read_encrypted_log, read_header  in *.
        repeat invert_exec; simpl in *; cleanup.
        Opaque apply_log.
      }
    }
    {
      split_ors; cleanup; repeat invert_exec; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply commit_finished_not_crashed; only 2: eauto; eauto.

      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply log_commit_finished_oracle_eq in H6; eauto; cleanup.
      split_ors; cleanup; repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      {
        Transparent apply_log.
        unfold apply_log, read_encrypted_log, read_header  in *.
        repeat invert_exec; simpl in *; cleanup.
        Opaque apply_log.
      }
      {
        Transparent apply_log.
        unfold apply_log, read_encrypted_log, read_header  in *.
        repeat invert_exec; simpl in *; cleanup.
        Opaque apply_log.
      }
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply_fresh log_commit_finished_oracle_eq in H6; eauto; cleanup.
      split_ors; cleanup; repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.

      unfold log_rep in *; cleanup.
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a1)).
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a2)).
      eapply commit_finished in H6; eauto.
      eapply commit_finished in H14; eauto.
      repeat split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      
      eapply log_apply_log_finished_not_crashed; eauto.
      unfold log_rep_general in *; cleanup.
      do 2 eexists; split; eauto.
      intros; congruence.
      unfold log_rep_general in *; cleanup.
      do 2 eexists; split; eauto.
      intros; congruence.
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply log_apply_log_finished_oracle_eq in H9; eauto; cleanup.
      split_ors; cleanup; repeat invert_exec; 
      simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      split_ors; cleanup; repeat invert_exec; 
      simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply_fresh HC_map_ext_eq_prefix in H9; cleanup.
      eapply commit_finished_not_crashed; eauto.
      eapply_fresh HC_map_ext_eq_prefix in H9; cleanup.
      eapply log_commit_finished_oracle_eq in H12; eauto; 
      simpl in *; cleanup.
      all: try rewrite e1; try rewrite e2.
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H13; cleanup.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        rewrite map_length; eauto.
      }
      {
        lia.
      }
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H13; cleanup.
        eapply_fresh Forall_forall in f0; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        2: rewrite map_length; eauto.
        eapply addr_list_to_blocks_length_nonzero; eauto.
      }
      {
        lia.
      }
      {
        unfold log_rep in *; cleanup.
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a1)).
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a2)).
      eapply commit_finished in H6; eauto.
      eapply commit_finished in H14; eauto.
      repeat split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *.
      eapply_fresh HC_map_ext_eq_prefix in H2; cleanup.
      eapply log_apply_log_finished_oracle_eq in H9; eauto; cleanup.
      eapply_fresh HC_map_ext_eq_prefix in H9; cleanup.
      eapply log_commit_finished_oracle_eq in H12; eauto; 
      simpl in *; cleanup.
      eapply write_batch_to_cache_finished_not_crashed; eauto.
      all: try rewrite e1; try rewrite e2.
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H3; cleanup.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        rewrite map_length; eauto.
      }
      {
        lia.
      }
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H3; cleanup.
        eapply_fresh Forall_forall in f0; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        2: rewrite map_length; eauto.
        eapply addr_list_to_blocks_length_nonzero; eauto.
      }
      {
        lia.
      }
    }
    }
  }
  {
    Transparent commit.
    repeat invert_exec; simpl in *; cleanup;
    repeat (split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *).
  }
  {
    repeat invert_exec; simpl in *; cleanup;
    repeat (split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *).
  }
  {
    repeat invert_exec; simpl in *; cleanup;
    repeat (split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *).
  }
  {
    repeat invert_exec; simpl in *; cleanup;
    repeat (split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *).
  }
  {
    repeat invert_exec; simpl in *; cleanup;
    repeat (split_ors; cleanup; try congruence;
      repeat invert_exec; simpl in *; cleanup;
      repeat rewrite <- app_assoc in *).
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; simpl in *; cleanup; try congruence.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; simpl in *; cleanup; try congruence.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; simpl in *; cleanup; try congruence.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; simpl in *; cleanup; try congruence.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; simpl in *; cleanup; try congruence.
  }
Qed.



(**** Crashed_oracle_eq ***)
Ltac unify_finished_oracles :=
  repeat rewrite <- app_assoc in *; 
  match goal with 
  [H1: exec _ _ ?o1 _ _ (Finished _ _),
  H0: exec _ _ ?o2 _ _(Finished _ _),
  H: ?o1 ++ _ = ?o2 ++ _ |- _] =>
  try ((eapply BatchOperations_encrypt_all_finished_oracle_eq in H1 ||
  eapply BatchOperations_hash_all_finished_oracle_eq in H1 ||
  eapply BatchOperations_write_batch_finished_oracle_eq in H1 ||
  eapply BatchOperations_read_consecutive_finished_oracle_eq in H1 ||
  eapply BatchOperations_decrypt_all_finished_oracle_eq in H1 ||
  eapply log_write_header_finished_oracle_eq in H1 ||
  eapply log_update_header_finished_oracle_eq in H1 ||
  eapply log_apply_log_finished_oracle_eq in H1 ||
  eapply log_apply_txn_finished_oracle_eq in H1 ||
  eapply log_apply_txns_finished_oracle_eq in H1 ||
  eapply log_check_hash_finished_oracle_eq in H1 ||
  eapply log_commit_finished_oracle_eq in H1 ||
  eapply log_commit_txn_finished_oracle_eq in H1 ||
  eapply log_decrypt_txn_finished_oracle_eq in H1 ||
  eapply log_decrypt_txns_finished_oracle_eq in H1 ||
  eapply log_flush_txns_finished_oracle_eq in H1 ||
  eapply log_init_finished_oracle_eq in H1 ||
  eapply_fresh log_read_encrypted_log_finished_oracle_eq in H1 ||
  eapply log_read_header_finished_oracle_eq in H1 ||
  eapply log_recover_finished_oracle_eq in H1 ||
  eapply write_batch_to_cache_finished_oracle_eq in H1 ||
  eapply write_lists_to_cache_finished_oracle_eq in H1); 
  eauto;
  subst; cleanup_no_match; 
  repeat rewrite <- app_assoc in *; cleanup_no_match)
end.


Ltac unify_finished_not_crashed_oracles :=
  repeat rewrite <- app_assoc in *; 
  try match goal with 
  [H1: exec _ _ ?o1 _ _ (Finished _ _),
  H0: exec _ _ ?o2 _ _(Crashed _),
  H: ?o2 ++ _ = ?o1 ++ _ |- _] =>
  symmetry in H
  end;
  try solve [
  match goal with 
  [H1: exec _ _ ?o1 _ _ (Finished _ _),
  H0: exec _ _ ?o2 _ _(Crashed _),
  H: ?o1 ++ _ = ?o2 ++ _ |- _] =>
  try ((eapply BatchOperations_encrypt_all_finished_not_crashed in H1 ||
  eapply BatchOperations_hash_all_finished_not_crashed in H1 ||
  eapply BatchOperations_write_batch_finished_not_crashed in H1 ||
  eapply BatchOperations_read_consecutive_finished_not_crashed in H1 ||
  eapply BatchOperations_decrypt_all_finished_not_crashed in H1 ||
  eapply log_write_header_finished_not_crashed in H1 ||
  eapply log_update_header_finished_not_crashed in H1 ||
  eapply log_apply_log_finished_not_crashed in H1 ||
  eapply apply_txn_finished_not_crashed in H1 ||
  eapply apply_txns_finished_not_crashed in H1 ||
  eapply log_check_hash_finished_not_crashed in H1 ||
  eapply commit_finished_not_crashed in H1 ||
  eapply commit_txn_finished_not_crashed in H1 ||
  eapply log_decrypt_txn_finished_not_crashed in H1 ||
  eapply log_decrypt_txns_finished_not_crashed in H1 ||
  eapply log_flush_txns_finished_not_crashed in H1 ||
  eapply log_init_finished_not_crashed in H1 ||
  eapply log_read_encrypted_log_finished_not_crashed in H1 ||
  eapply log_read_header_finished_not_crashed in H1||
  eapply log_recover_finished_not_crashed in H1 ||
  eapply write_batch_to_cache_finished_not_crashed in H1 ||
  eapply write_lists_to_cache_finished_not_crashed in H1); 
  eauto; exfalso; eauto) 
  end].

Lemma BatchOperations_encrypt_all_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.encrypt_all k1 l1)  (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.encrypt_all k2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHl1 in H2; eauto; subst; eauto.
Qed.

Lemma BatchOperations_hash_all_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.hash_all k1 l1)  (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(BatchOperations.hash_all k2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHl1 in H2; eauto; subst; eauto.
Qed.

Lemma BatchOperations_write_batch_crashed_oracle_eq:
forall u k1 k2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',

exec CryptoDiskLang u o1 s1
(BatchOperations.write_batch k1 l1)  (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(BatchOperations.write_batch k2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction k1; destruct k2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHk1 in H2; eauto; subst; eauto.
Qed.

Definition  BatchOperations_write_consecutive_crashed_oracle_eq := BatchOperations_write_batch_crashed_oracle_eq. 


Lemma BatchOperations_read_consecutive_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2' k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.read_consecutive k1 l1)  (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(BatchOperations.read_consecutive k2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHl1 in H2; eauto; subst; eauto.
Qed.

Lemma BatchOperations_decrypt_all_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2'   k1 k2,
exec CryptoDiskLang u o1 s1
(BatchOperations.decrypt_all k1 l1)  (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(BatchOperations.decrypt_all k2 l2) (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHl1 in H2; eauto; subst; eauto.
Qed.




Lemma log_read_header_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
read_header  (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
read_header (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent read_header.
  unfold read_header; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto).
  Opaque read_header.
Qed.

Lemma log_write_header_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' h1 h2,
exec CryptoDiskLang u o1 s1
(write_header h1) (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(write_header h2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent write_header.
  unfold write_header; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto).
  Opaque write_header.
Qed.

Lemma log_update_header_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' h1 h2,
exec CryptoDiskLang u o1 s1
(update_header h1) (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(update_header h2) (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent update_header.
  unfold update_header; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply log_read_header_crashed_oracle_eq in H; eauto.
  eapply log_write_header_crashed_oracle_eq in H4; eauto;
  subst; eauto.
  Opaque update_header.
Qed.


Lemma log_commit_txn_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit_txn a1 v1)  (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(commit_txn a2 v2) (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold commit_txn; intros.

  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply log_read_header_crashed_oracle_eq in H1; eauto.
  eapply BatchOperations_encrypt_all_crashed_oracle_eq  in H5; eauto; subst; eauto.
  eapply BatchOperations_hash_all_crashed_oracle_eq  in H6; eauto; subst; eauto.
  eapply BatchOperations_write_consecutive_crashed_oracle_eq  in H7; eauto; subst; eauto.
  eapply log_update_header_crashed_oracle_eq in H9; eauto; subst; eauto.
  Opaque commit_txn.
Qed.

Lemma log_commit_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' a1 a2 v1 v2,
exec CryptoDiskLang u o1 s1
(commit a1 v1)  (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(commit a2 v2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent commit.
  unfold commit; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply log_read_header_crashed_oracle_eq in H1; eauto.
  {
    Transparent commit_txn read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
    Opaque commit_txn read_header.
  }
  {
    Transparent commit_txn read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup.
    simpl in *; congruence.
    Opaque commit_txn read_header.
  }
  {
    Transparent commit_txn read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
    Opaque commit_txn read_header.
  }
  {
    Transparent commit_txn read_header.
    unfold commit_txn, read_header in *.
    repeat invert_exec; cleanup.
    simpl in *; congruence.
    Opaque commit_txn read_header.
  }
  eapply log_commit_txn_crashed_oracle_eq  in H1; eauto; subst; eauto.
  Opaque commit.
Qed.

Lemma log_check_hash_crashed_oracle_eq:
forall u l1 l2 h1 h2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(check_hash l1 h1) (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(check_hash l2 h2) (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent check_hash.
  unfold check_hash; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  try eapply_fresh BatchOperations_hash_all_crashed_oracle_eq in H; eauto;
  subst; eauto; cleanup.
Qed.

Lemma log_read_encrypted_log_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' vp txns1 txns2 hdr1 hdr2,

exec CryptoDiskLang u o1 s1
read_encrypted_log (Crashed s1') ->
exec CryptoDiskLang u o2 s2
read_encrypted_log (Crashed s2') ->

log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->

o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent read_encrypted_log.
  unfold read_encrypted_log; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  eapply log_read_header_crashed_oracle_eq in H; eauto; subst; eauto; cleanup.

  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  eapply BatchOperations_read_consecutive_crashed_oracle_eq in H3; eauto; subst; eauto.
  
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  eapply log_check_hash_crashed_oracle_eq in H3; eauto; subst; eauto.
  
  unfold check_hash in *; repeat invert_exec; try congruence.

  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  destruct (count (old_part x4)); simpl in *;
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  destruct (count (old_part x4)); simpl in *;
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.

  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  destruct (count (old_part x0)); simpl in *;
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  destruct (count (old_part x0)); simpl in *;
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.

  repeat split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles;
  try unify_finished_not_crashed_oracles.
  eapply BatchOperations_read_consecutive_crashed_oracle_eq in H3; eauto; subst; eauto.
  eauto.
  Opaque read_encrypted_log.
Qed.

Lemma log_decrypt_txn_crashed_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(decrypt_txn txn_rec1 l1) (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(decrypt_txn txn_rec2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold decrypt_txn; simpl; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  try eapply_fresh BatchOperations_decrypt_all_crashed_oracle_eq in H; eauto;
  subst; eauto; cleanup.
Qed.


Lemma log_apply_txn_crashed_oracle_eq:
forall u txn_rec1 txn_rec2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(apply_txn txn_rec1 l1) (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(apply_txn txn_rec2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent apply_txn.
  unfold apply_txn; simpl; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  try eapply_fresh log_decrypt_txn_crashed_oracle_eq in H1; eauto;
  subst; eauto; cleanup.
  eapply BatchOperations_write_batch_crashed_oracle_eq in H1; eauto;
  cleanup; eauto.
Qed.


Lemma log_apply_txns_crashed_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(apply_txns txn_recs1 l1) (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(apply_txns txn_recs2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Transparent apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; simpl in *; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count t + data_count t) (skipn (start t) l2)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count t + data_count t) (skipn (start t) l2)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count a + data_count a) (skipn (start a) l1)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count a + data_count a) (skipn (start a) l1)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  eapply log_apply_txn_crashed_oracle_eq in H; eauto.
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  repeat rewrite <- app_assoc in *.
  eapply IHtxn_recs1 in H7; eauto.
  cleanup; eauto.
Qed.

Lemma log_decrypt_txns_crashed_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(decrypt_txns txn_recs1 l1) (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(decrypt_txns txn_recs2 l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Opaque apply_txns.
  induction txn_recs1; destruct txn_recs2; simpl; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto); 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles.

  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count t + data_count t) (skipn (start t) l2)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count t + data_count t) (skipn (start t) l2)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count t + data_count t) (skipn (start t) l2)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }

  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count a + data_count a) (skipn (start a) l1)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count a + data_count a) (skipn (start a) l1)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    unfold apply_txn, decrypt_txn in *.
    repeat invert_exec; eauto.
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles);
  destruct (firstn (addr_count a + data_count a) (skipn (start a) l1)); simpl in *;
  repeat invert_exec; eauto;
    repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }

  eapply log_decrypt_txn_crashed_oracle_eq in H; eauto.
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  repeat rewrite <- app_assoc in *.
  eapply IHtxn_recs1 in H0; eauto.
  cleanup; eauto.

  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  unify_finished_not_crashed_oracles.
  inversion H2; subst;
  inversion H3; subst;
  inversion H4; subst;
  inversion H5; subst;
  unify_finished_not_crashed_oracles.
  exfalso; eapply log_decrypt_txns_finished_not_crashed.
   eauto.
   6: eauto.
   all: eauto.

   inversion H2; subst;
   inversion H3; subst;
   inversion H4; subst;
   inversion H5; subst;
   unify_finished_oracles; eauto.
Qed.


Lemma log_flush_txns_crashed_oracle_eq:
forall u txn_recs1 txn_recs2 l1 l2 o1 o2 o3 o4 s1 s2 s1' s2'  ,
exec CryptoDiskLang u o1 s1
(flush_txns txn_recs1 l1) (Crashed s1' ) ->
exec CryptoDiskLang u o2 s2
(flush_txns txn_recs2 l2) (Crashed s2' ) ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun rec => addr_count rec > 0) txn_recs1 ->
Forall (fun rec => addr_count rec > 0) txn_recs2 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l1) 
txn_recs1 ->
Forall (fun txn_rec1 => 
start txn_rec1 +
addr_count txn_rec1 +
data_count txn_rec1 <=
length l2) 
txn_recs2 ->
o1 = o2.
Proof.
  Transparent flush_txns.
  unfold flush_txns; intros;

  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).

  eapply log_apply_txns_crashed_oracle_eq in H0; only 2: apply H; eauto.
  exfalso; eapply apply_txns_finished_not_crashed. 
  eauto.
  6: eauto.
  all: eauto.

  exfalso; eapply apply_txns_finished_not_crashed. 
  eauto.
  6: eauto.
  all: eauto.
  eapply log_update_header_crashed_oracle_eq in H7; eauto.
  cleanup; eauto.

  exfalso; eapply apply_txns_finished_not_crashed. 
  eauto.
  6: eauto.
  all: eauto.
Qed.

Lemma log_apply_log_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' hdr1 hdr2 txns1 txns2,
exec CryptoDiskLang u o1 s1
apply_log (Crashed s1') ->
exec CryptoDiskLang u o2 s2
apply_log (Crashed s2') ->

log_header_rep hdr1 txns1 s1 ->
log_header_rep hdr2 txns2 s2 ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent apply_log.
  unfold apply_log; intros.
  unfold log_header_rep, log_rep_general in *; cleanup.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto); 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles.
  eapply_fresh log_read_encrypted_log_crashed_oracle_eq in H0; eauto.
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  exfalso;
  eapply_fresh log_read_encrypted_log_finished_not_crashed in H0; eauto.
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  exfalso;
  eapply_fresh log_read_encrypted_log_finished_not_crashed in H; eauto.
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }

  eapply read_encrypted_log_finished in H0; eauto.
  eapply read_encrypted_log_finished in H4; eauto.
  cleanup; simpl in *.
  all: intros; try congruence.
  eapply log_flush_txns_crashed_oracle_eq in H3; simpl; eauto.
  subst; eauto.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    eapply Forall_forall in H28; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    eapply Forall_forall in H20; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H28; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    rewrite map_length; setoid_rewrite H23. lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H19, <- H27 in *.
    apply in_map_iff in H.
    cleanup.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H20; 
    unfold txn_well_formed, record_is_valid in *; cleanup; eauto.
    lia.
    rewrite map_length; setoid_rewrite H15. lia.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  {
    unfold log_reboot_rep_explicit_part, log_header_rep, log_rep_general in *.
    do 2 eexists; intuition eauto.
    congruence.
  }
  Unshelve.
  all: repeat constructor; exact key0.
  Qed.


Lemma log_recover_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' vp hdr1 hdr2 txns1 txns2,
exec CryptoDiskLang u o1 s1
Log.recover (Crashed s1') ->
exec CryptoDiskLang u o2 s2
Log.recover (Crashed s2') ->
log_reboot_rep_explicit_part  hdr1 txns1 vp s1 ->
log_reboot_rep_explicit_part  hdr2 txns2 vp s2 ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent Log.recover.
  unfold Log.recover; intros;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto); 
  repeat unify_finished_oracles; try unify_finished_not_crashed_oracles.
  eapply_fresh log_read_encrypted_log_crashed_oracle_eq in H0; eauto.
  eapply_fresh log_read_encrypted_log_finished_not_crashed in H; eauto; intuition. 
  eapply_fresh log_write_header_crashed_oracle_eq in H3; eauto; subst; eauto.
  eapply_fresh log_read_encrypted_log_finished_not_crashed in H; eauto; intuition.
  eauto.
  simpl in *; cleanup.
  eapply_fresh log_read_encrypted_log_finished_not_crashed in H; eauto; intuition.
  simpl in *; cleanup.
  simpl in *; cleanup.
  
  unfold log_reboot_rep_explicit_part, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished in H4; eauto.
  eapply read_encrypted_log_finished in H0; eauto.
  cleanup_no_match; simpl in *.
  all: intros; try congruence.
  eapply log_decrypt_txns_crashed_oracle_eq in H6. 
  3: eauto.
  all: eauto.
  cleanup; eauto.
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H30 in *.
    apply in_map_iff in H0.
    cleanup_no_match.
    eapply Forall_forall in H31; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H30, <- H22 in *.
    apply in_map_iff in H0.
    cleanup_no_match.
    eapply Forall_forall in H23; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H30, <- H22 in *.
    apply in_map_iff in H0.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H31; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
    rewrite map_length; setoid_rewrite H26. cleanup; lia.
  }
  {
    eapply Forall_forall; intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H30, <- H22 in *.
    apply in_map_iff in H0.
    cleanup_no_match.
    rewrite firstn_length_l; eauto.
    eapply Forall_forall in H23; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    lia.
    rewrite map_length; setoid_rewrite H18. 
    cleanup; lia.
  }
Qed.

Lemma log_init_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CryptoDiskLang u o1 s1
(Log.init l1)  (Crashed s1') ->
exec CryptoDiskLang u o2 s2
(Log.init l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Transparent Log.init.
  unfold Log.init; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply_fresh log_write_header_crashed_oracle_eq in H0; eauto.
  eapply_fresh BatchOperations_write_batch_crashed_oracle_eq in H1; eauto; subst; eauto.
Qed.


Lemma read_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' a1 a2,
exec CachedDiskLang u o1 s1
(read a1)  (Crashed s1') ->
exec CachedDiskLang u o2 s2
(read a2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  unfold read; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
Qed.



Lemma write_batch_to_cache_crashed_oracle_eq:
forall u l1 l2 l3 l4 o1 o2 o3 o4 s1 s2 s1' s2',
exec CachedDiskLang u o1 s1
(LogCache.write_batch_to_cache l1 l3)  (Crashed s1') ->
exec CachedDiskLang u o2 s2
(LogCache.write_batch_to_cache l2 l4) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  eapply IHl1 in H3; eauto.
  cleanup; eauto.
Qed.

Lemma write_lists_to_cache_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CachedDiskLang u o1 s1
(LogCache.write_lists_to_cache l1)  (Crashed s1') ->
exec CachedDiskLang u o2 s2
(LogCache.write_lists_to_cache l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) l1 -> 
Forall (fun a => length (fst a) > 0 /\ length (snd a) > 0) l2 -> 
o1 = o2.
Proof.
  induction l1; destruct l2; simpl in *; intros;  simpl in *; try lia;
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  {
    destruct (fst p); simpl in *;
    repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }

  {
    destruct (fst p); simpl in *;
    repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    destruct (fst a); simpl in *;
    repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  {
    destruct (fst a); simpl in *;
    repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles; try unify_finished_not_crashed_oracles).
  }
  eapply_fresh write_batch_to_cache_crashed_oracle_eq in H1; eauto.
  inversion H2; subst;
  inversion H3; subst;
  cleanup.
  eapply IHl1 in H5; eauto.
  cleanup; eauto.
Qed.


Lemma recover_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' vp hdr1 hdr2 txns1 txns2,
exec CachedDiskLang u o1 s1
recover  (Crashed s1') ->
exec CachedDiskLang u o2 s2
recover (Crashed s2') ->
log_reboot_rep_explicit_part  hdr1 txns1 vp (snd s1) ->
log_reboot_rep_explicit_part  hdr2 txns2 vp (snd s2) ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Opaque Log.recover.
  unfold recover; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  eapply_fresh HC_map_ext_eq_prefix in H5; cleanup.
  eapply_fresh log_recover_crashed_oracle_eq in H; eauto; subst; eauto.
  eapply_fresh HC_map_ext_eq_prefix in H5; cleanup.
  exfalso; eapply log_recover_finished_not_crashed; eauto; subst; eauto.
  eapply_fresh HC_map_ext_eq_prefix in H5; cleanup.
  symmetry in H.
  exfalso; eapply log_recover_finished_not_crashed.
  eauto.
  4: eauto.
  all: eauto.
  eapply_fresh HC_map_ext_eq_prefix in H5; cleanup.  
  eapply_fresh Specs.recover_finished in H8; eauto.
  eapply_fresh Specs.recover_finished in H10; eauto.
  unify_finished_oracles.
  cleanup; eauto.
  eapply write_lists_to_cache_crashed_oracle_eq in H5; eauto; subst; eauto. 
  shelve.
  shelve.
  unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  unfold log_reboot_rep, log_reboot_rep_explicit_part in *; eauto.
  Unshelve.
  all: try solve [repeat constructor; exact key0].
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H.
    apply in_map_iff in H; cleanup; simpl in *.
    apply in_combine_same in H13; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H21; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
  }
  {
    eapply Forall_forall; intros.
    rewrite <- combine_map' in H.
    apply in_map_iff in H; cleanup; simpl in *.
    apply in_combine_same in H13; cleanup. 
    unfold log_rep, log_rep_general, log_rep_explicit, 
    log_rep_inner, txns_valid in *; logic_clean.
    eapply Forall_forall in H29; 
    unfold txn_well_formed, record_is_valid in *; 
    cleanup_no_match; eauto.
    split; cleanup; try lia.
    rewrite firstn_length_l; eauto. 
  }
Qed.


Lemma init_crashed_oracle_eq:
forall u l1 l2 o1 o2 o3 o4 s1 s2 s1' s2',
exec CachedDiskLang u o1 s1
(init l1)  (Crashed s1') ->
exec CachedDiskLang u o2 s2
(init l2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
o1 = o2.
Proof.
  Opaque Log.init.
  unfold init; intros.
  repeat invert_exec; eauto;
  repeat invert_exec; cleanup; eauto;
  repeat (try split_ors; cleanup;
  repeat invert_exec; simpl in *; cleanup; eauto; 
  try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  apply HC_map_ext_eq_prefix in H7; eauto; cleanup.
  eapply log_init_crashed_oracle_eq in H; eauto.
  subst; eauto.
Qed.


Lemma write_crashed_oracle_eq:
forall u o1 o2 o3 o4 s1 s2 s1' s2' a1 a2 v1 v2 hdr1 hdr2 txns1 txns2,
log_header_rep hdr1 txns1 (snd s1) ->
log_header_rep hdr2 txns2 (snd s2) ->
(NoDup a1 <-> NoDup a2) ->
(Forall (fun a => a < data_length) a1 <->
Forall (fun a => a < data_length) a2) -> 
exec CachedDiskLang u o1 s1
(write a1 v1)  (Crashed s1') ->
exec CachedDiskLang u o2 s2
(write a2 v2) (Crashed s2') ->
o1 ++ o3 = o2 ++ o4 ->
length a1 = length a2 ->
o1 = o2.
Proof.
  Opaque apply_log Log.commit commit LogCache.write_batch_to_cache.
  unfold write; intros.
  cleanup; try solve [intuition eauto; lia].
  all: try match goal with
  | [H: exec _ _ _ _ (Ret _) (Crashed _),
  H0: exec _ _ _ _ (Ret _) (Crashed _) |- _ ] =>
  repeat invert_exec; eauto
  end.
  all: try solve [intuition].
  {
    repeat invert_exec; eauto;
    repeat invert_exec; cleanup; eauto;
    repeat split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup; eauto; 
    try unify_finished_oracles; try unify_finished_not_crashed_oracles;
    eapply_fresh HC_map_ext_eq_prefix in H5; eauto; cleanup.
    {
      eapply log_commit_crashed_oracle_eq in H3; eauto.
      subst; eauto.
    }
    {
      repeat split_ors; cleanup;
      repeat invert_exec; simpl in *; cleanup; eauto; 
      try unify_finished_oracles; try unify_finished_not_crashed_oracles.
    }
    {
      exfalso; eapply commit_finished_not_crashed; eauto.
    }
    {
      symmetry in H3; exfalso; eapply commit_finished_not_crashed; eauto.
    }
    {
      symmetry in H3; exfalso; eapply commit_finished_not_crashed; eauto.
    }
    {
      eapply log_commit_finished_oracle_eq in H12; eauto; cleanup.
      repeat split_ors; cleanup;
      repeat invert_exec; simpl in *; cleanup; eauto; 
      try unify_finished_oracles; try unify_finished_not_crashed_oracles.
      eapply write_batch_to_cache_crashed_oracle_eq in H8; eauto.
      subst; eauto.
    }
    {
      eapply_fresh log_commit_finished_oracle_eq in H12; eauto; cleanup.
      repeat split_ors; cleanup;
      repeat invert_exec; simpl in *; cleanup; eauto; 
      try unify_finished_oracles; try unify_finished_not_crashed_oracles.
      {
        repeat split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles; try unify_finished_not_crashed_oracles.
        Transparent apply_log read_encrypted_log read_header.
        {
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        {
          clear H9.
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        Transparent apply_log read_encrypted_log read_header.
        unfold apply_log, read_encrypted_log, read_header in *.
        repeat invert_exec; cleanup; eauto;
        repeat (try split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        repeat split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles; try unify_finished_not_crashed_oracles.
        Transparent apply_log read_encrypted_log read_header.
        {
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        {
          clear H9.
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        Transparent apply_log read_encrypted_log read_header.
        unfold apply_log, read_encrypted_log, read_header in *.
        repeat invert_exec; cleanup; eauto;
        repeat (try split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        Opaque apply_log read_encrypted_log read_header.
      }
    }
    {
      eapply_fresh log_commit_finished_oracle_eq in H12; eauto; cleanup.
      repeat split_ors; cleanup;
      repeat invert_exec; simpl in *; cleanup; eauto; 
      try unify_finished_oracles; try unify_finished_not_crashed_oracles.
      {
        repeat split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles; try unify_finished_not_crashed_oracles.
        Transparent apply_log read_encrypted_log read_header.
        {
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        {
          clear H9.
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        Transparent apply_log read_encrypted_log read_header.
        unfold apply_log, read_encrypted_log, read_header in *.
        repeat invert_exec; cleanup; eauto;
        repeat (try split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        repeat split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles; try unify_finished_not_crashed_oracles.
        Transparent apply_log read_encrypted_log read_header.
        {
          unfold apply_log, read_encrypted_log, read_header in *.
          repeat invert_exec; cleanup; eauto;
          repeat (try split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        }
        Opaque apply_log read_encrypted_log read_header.
      }
      {
        Transparent apply_log read_encrypted_log read_header.
        unfold apply_log, read_encrypted_log, read_header in *.
        repeat invert_exec; cleanup; eauto;
        repeat (try split_ors; cleanup;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles); try unify_finished_not_crashed_oracles.
        Opaque apply_log read_encrypted_log read_header.
      }
    }
    {
      eapply_fresh log_commit_finished_oracle_eq in H12; eauto; cleanup.
      unfold log_rep in *; cleanup.
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a1)).
      destruct_fresh (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) a2)).
      eapply Specs.commit_finished in H7; eauto.
      eapply Specs.commit_finished in H12; eauto.
      {
        repeat invert_exec; cleanup; eauto;
        repeat split_ors; cleanup; try congruence;
        repeat invert_exec; simpl in *; cleanup; eauto; 
        try unify_finished_oracles; try unify_finished_not_crashed_oracles.
        {
          repeat invert_exec; cleanup; eauto;
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles; try unify_finished_not_crashed_oracles;
          eapply_fresh HC_map_ext_eq_prefix in H5; eauto; cleanup.
          {
            eapply log_apply_log_crashed_oracle_eq in H3; eauto; cleanup; eauto.
          }
          {
            unfold log_header_rep, log_rep_general in *; cleanup.
            exfalso; eapply log_apply_log_finished_not_crashed; eauto.
            all: unfold log_reboot_rep_explicit_part; do 2 eexists; intuition eauto; try congruence.
          }
          {
            symmetry in H3.
            unfold log_header_rep, log_rep_general in *; cleanup.
            exfalso; eapply log_apply_log_finished_not_crashed; eauto.
            all: unfold log_reboot_rep_explicit_part; do 2 eexists; intuition eauto; try congruence.
          }
          {
            eapply log_apply_log_finished_oracle_eq in H3; eauto; cleanup; eauto.
            repeat invert_exec; cleanup; eauto;
            repeat (try split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto; 
            try unify_finished_oracles); try unify_finished_not_crashed_oracles;
            eapply_fresh HC_map_ext_eq_prefix in H16; eauto; cleanup.
            {
              eapply log_commit_crashed_oracle_eq in H3; eauto.
              subst; eauto.
            }
            {
              repeat split_ors; cleanup;
              repeat invert_exec; simpl in *; cleanup; eauto; 
              try unify_finished_oracles; try unify_finished_not_crashed_oracles.
            }
            {
              symmetry in H3; exfalso; eapply commit_finished_not_crashed; eauto.
            }
            {
              eapply log_commit_finished_oracle_eq in H19; eauto; cleanup; eauto.
            }
          }
        }
        {
          repeat invert_exec; cleanup; eauto;
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles; try unify_finished_not_crashed_oracles;
          eapply_fresh HC_map_ext_eq_prefix in H5; eauto; cleanup.
          {
            unfold log_header_rep, log_rep_general in *; cleanup.
            exfalso; eapply log_apply_log_finished_not_crashed; eauto.
            all: unfold log_reboot_rep_explicit_part; do 2 eexists; intuition eauto; try congruence.
          }
          {
            eapply log_apply_log_finished_oracle_eq in H3; eauto; cleanup; eauto.
            repeat invert_exec; cleanup; eauto;
            repeat (try split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto; 
            try unify_finished_oracles); try unify_finished_not_crashed_oracles;
            eapply_fresh HC_map_ext_eq_prefix in H18; eauto; cleanup.
            {
              exfalso; eapply commit_finished_not_crashed; eauto.
            }
            {
              eapply log_commit_finished_oracle_eq in H3; eauto; simpl in *; 
              cleanup; eauto.
            }
          }
        }
        {
          repeat invert_exec; cleanup; eauto;
          repeat split_ors; cleanup;
          repeat invert_exec; simpl in *; cleanup; eauto; 
          try unify_finished_oracles; try unify_finished_not_crashed_oracles;
          eapply_fresh HC_map_ext_eq_prefix in H5; eauto; cleanup.
          {
            symmetry in H3.
            unfold log_header_rep, log_rep_general in *; cleanup.
            exfalso; eapply log_apply_log_finished_not_crashed; eauto.
            all: unfold log_reboot_rep_explicit_part; do 2 eexists; intuition eauto; try congruence.
          }
          {
            eapply log_apply_log_finished_oracle_eq in H3; eauto; cleanup; eauto.
            repeat invert_exec; cleanup; eauto;
            repeat (try split_ors; cleanup;
            repeat invert_exec; simpl in *; cleanup; eauto; 
            try unify_finished_oracles); try unify_finished_not_crashed_oracles;
            eapply_fresh HC_map_ext_eq_prefix in H18; eauto; cleanup.
            {
              symmetry in H3.
              exfalso; eapply commit_finished_not_crashed; eauto.
            }
            {
              eapply log_commit_finished_oracle_eq in H3; eauto; simpl in *; 
              cleanup; eauto.
            }
          }
        }
        {
          eapply_fresh HC_map_ext_eq_prefix in H5; eauto; cleanup.
          repeat unify_finished_oracles.
          simpl in *; cleanup; eauto.
          repeat rewrite <- app_assoc in *;
          eapply_fresh HC_map_ext_eq_prefix in H20; eauto; cleanup.
          unify_finished_oracles.
          eapply write_batch_to_cache_crashed_oracle_eq in H20; 
          eauto; simpl in *; 
          cleanup; eauto.
        }
      }
      all: try rewrite e1; try rewrite e2.
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
        lia.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H3; cleanup.
        eapply_fresh Forall_forall in f0; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
        lia.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        rewrite map_length; eauto.
        setoid_rewrite e. lia.
      }
      {
        lia.
      }
      {
        rewrite firstn_app2; eauto.
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
        rewrite map_length; eauto.
      }
      {
        rewrite firstn_app2; eauto.    
        apply Forall_forall; intros.
        apply in_map_iff in H3; cleanup.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
        rewrite map_length; eauto.
      }    
      {
        rewrite app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        2: rewrite map_length; eauto.
        eapply addr_list_to_blocks_length_nonzero; eauto.
      }
      {
        lia.
      }
    }
  }
  Transparent commit read_header.
  {
    unfold commit, read_header in *; 
    repeat invert_exec; cleanup; eauto;
    repeat (try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup; eauto; 
    try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; cleanup; eauto;
    repeat (try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup; eauto; 
    try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; cleanup; eauto;
    repeat (try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup; eauto; 
    try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  }
  {
    unfold commit, read_header in *; 
    repeat invert_exec; cleanup; eauto;
    repeat (try split_ors; cleanup;
    repeat invert_exec; simpl in *; cleanup; eauto; 
    try unify_finished_oracles); try unify_finished_not_crashed_oracles.
  }
Qed.
