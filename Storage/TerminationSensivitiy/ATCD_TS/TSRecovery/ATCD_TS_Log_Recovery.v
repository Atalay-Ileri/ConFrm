Require Import Eqdep Lia Framework FSParameters CryptoDiskLayer.
Require Import BatchOperations Log Specs ATCD_TS_BatchOperations_Recovery.

Set Nested Proofs Allowed.

Lemma Log_TS_read_header:
forall u s1 s2 o s1' t,
exec (CryptoDiskLang) u o s1 
read_header
     (Finished s1' t) ->
exists s2' t,
exec (CryptoDiskLang) u o s2 
read_header
     (Finished s2' t).
Proof.
unfold read_header in *.
simpl in *; intros;
cleanup; repeat invert_exec.
do 2 eexists; repeat econstructor; eauto.
Qed.


Lemma Log_TS_write_header:
forall u s1 s2 o s1' t hdr1 hdr2,
exec (CryptoDiskLang) u o s1 
(write_header hdr1)
     (Finished s1' t) ->
exists s2' t,
exec (CryptoDiskLang) u o s2 
(write_header hdr2)
     (Finished s2' t).
Proof.
unfold write_header in *.
simpl in *; intros;
cleanup; repeat invert_exec.
do 2 eexists; repeat econstructor; eauto.
Qed.



Lemma Log_TS_check_hash:
forall u l1 l2 s1 s2 o s1' t h1 h2,
exec (CryptoDiskLang) u o s1 
(check_hash l1 h1)
     (Finished s1' t) ->
     length l1 = length l2 ->
consistent_with_upds (snd (fst (fst s2))) (rolling_hash_list hash0 l2)
(combine (hash0 :: rolling_hash_list hash0 l2) l2) ->
exists s2' t,
exec (CryptoDiskLang) u o s2 
(check_hash l2 h2)
     (Finished s2' t).
Proof.
unfold check_hash in *.
simpl in *; intros;
cleanup_no_match; repeat invert_exec_no_match.
eapply BatchOperations_TS_hash_all with 
(s2 := s2) (l2:= l2)in H; cleanup_no_match.
destruct (hash_dec x2 h1);
repeat invert_exec_no_match;
destruct (hash_dec x4 h2);
do 2 eexists; repeat econstructor; eauto;
destruct (hash_dec x4 h2); try congruence; try econstructor.
all: eauto.
Qed.



Lemma Log_read_header_finished:
forall u s1 o s1' t hdr1 txns1 valid_part1 hdr_blockset1 log_blocksets1,

exec (CryptoDiskLang) u o s1 
read_header (Finished s1' t) ->

log_rep_explicit Log.Hdr_Synced Log.Synced valid_part1 hdr1 txns1
hdr_blockset1 log_blocksets1 s1 -> 

s1' = s1 /\ t = hdr1.
Proof.
     intros; unfold read_header in *; repeat invert_exec.
     unfold log_header_rep, log_rep_general, 
     log_rep_explicit, log_header_block_rep in *; cleanup.
     repeat cleanup_pairs; eauto.
Qed.

Lemma Log_read_log: 
forall u o s s' r hdr txns hdr_blockset log_blocksets valid_part n,
log_rep_explicit Hdr_Synced Synced valid_part hdr txns hdr_blockset
        log_blocksets s ->
exec CryptoDiskLang u o s
(read_consecutive log_start n) 
(Finished s' r) ->
n <= log_length ->
s' = s /\
r = firstn n (map fst log_blocksets).
Proof.
     intros.
eapply_fresh read_consecutive_finished in H0; cleanup.
unfold log_rep_explicit, log_data_blocks_rep in *; cleanup.
split; eauto.
eapply Forall2_eq, forall_forall2.
eapply Forall_forall; intros.
eapply in_seln_exists in H; cleanup.
rewrite combine_length_eq in H.
erewrite seln_combine in H11.
destruct x; simpl in *; cleanup.
edestruct H3; eauto; cleanup.
rewrite seln_firstn in H14.
erewrite seln_map in H14; eauto. 
erewrite <- H4 in H14; eauto.
rewrite H13 in H12; eauto.
rewrite <- H12, <- H14; eauto.
all: try lia.
setoid_rewrite H5; simpl in *; lia.
all: rewrite firstn_length_l; eauto.
all: rewrite map_length; setoid_rewrite H5; destruct valid_part; simpl in *; eauto.
Unshelve.
exact value0.
Qed.

Lemma Log_check_hash_finished:
forall u o s s' r h l,
exec CryptoDiskLang u o s
(check_hash l h) 
(Finished s' r) ->
(r = true /\ 
h = rolling_hash hash0 l) \/
(r = false /\ 
h <> rolling_hash hash0 l).
Proof.
     unfold check_hash; intros; repeat invert_exec; eauto;
     eapply hash_all_finished in H; cleanup; eauto.
Qed.


Lemma Log_check_hash_true:
forall u o s s' r hdr txns hdr_blockset log_blocksets,
log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset
        log_blocksets s ->
exec CryptoDiskLang u o s
(check_hash (firstn (count (current_part hdr)) (map fst log_blocksets)) (hash (current_part hdr))) 
(Finished s' r) ->
r = true.
Proof.
     unfold check_hash; intros; repeat invert_exec; eauto.
     unfold  log_rep_explicit, log_rep_inner, header_part_is_valid in *; cleanup.
     eapply hash_all_finished in H0; cleanup.
     clear D. rewrite H6 in n; eauto.
Qed.

Lemma hashes_in_hashmap_consistent_with_upds:
forall l m h,
hashes_in_hashmap m h l ->
consistent_with_upds m (rolling_hash_list h l)
  (combine (h :: rolling_hash_list h l) l).
Proof.
     induction l; simpl; intros; 
     cleanup; eauto.
     unfold consistent; split; eauto.
     rewrite Mem.upd_nop; eauto; eapply IHl.
Qed.

Lemma in_map_consistent_with_upds:
forall A AEQ V l1 l2 (m: @mem A AEQ V),
Forall2 (fun a v => m a = Some v) l1 l2 ->
consistent_with_upds m l1 l2.
Proof.
     induction l1; destruct l2; simpl; intros; 
     cleanup; eauto; inversion H; cleanup.
     unfold consistent; split; eauto.
     rewrite Mem.upd_nop; eauto; eapply IHl.
Qed.

Lemma Log_TS_read_encrypted_log:
forall u s1 s2 o s1' t hdr1 hdr2 txns1 txns2
valid_part hdr_blockset1 hdr_blockset2 
log_blocksets1 log_blocksets2,

exec (CryptoDiskLang) u o s1 
read_encrypted_log
     (Finished s1' t) ->

log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 txns1
hdr_blockset1 log_blocksets1 s1 -> 
log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 txns2
hdr_blockset2 log_blocksets2 s2 -> 

(Log.hash (Log.current_part hdr1) <>
rolling_hash hash0
     (firstn (Log.count (Log.current_part hdr1)) (map fst log_blocksets1)) <->
Log.hash (Log.current_part hdr2) <>
     rolling_hash hash0
          (firstn (Log.count (Log.current_part hdr2)) (map fst log_blocksets2))) ->

Forall2
(fun rec1 rec2 : Log.txn_record =>
     Log.start rec1 = Log.start rec2 /\
     Log.addr_count rec1 = Log.addr_count rec2 /\
     Log.data_count rec1 = Log.data_count rec2)
(map Log.record txns1)
(map Log.record txns2) ->

consistent_with_upds (snd (fst (fst s2)))
  (rolling_hash_list hash0
     (firstn (count (current_part hdr2)) (map fst log_blocksets2)))
  (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (current_part hdr2)) (map fst log_blocksets2)))
     (firstn (count (current_part hdr2)) (map fst log_blocksets2))) ->

consistent_with_upds (snd (fst (fst s2)))
  (rolling_hash_list hash0
     (firstn (count (old_part hdr2)) (map fst log_blocksets2)))
  (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (old_part hdr2)) (map fst log_blocksets2)))
     (firstn (count (old_part hdr2)) (map fst log_blocksets2))) ->

(valid_part = Old_Part -> count (current_part hdr1) = count (current_part hdr2)) ->

exists s2' t,
exec (CryptoDiskLang) u o s2 
read_encrypted_log
     (Finished s2' t).
Proof.
unfold read_encrypted_log in *.
simpl in *; intros;
cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh Log_TS_read_header with (s2:= s2) in H; cleanup_no_match.
eapply_fresh Log_read_header_finished in H; eauto.
eapply_fresh Log_read_header_finished in H10; eauto.
cleanup_no_match.

assume (A: (count (current_part hdr1) = count (current_part hdr2))).

eapply_fresh BatchOperations_TS_read_consecutive with (s2:= s2) in H7; cleanup_no_match.
unfold log_header_rep, log_rep_general in *; cleanup_no_match.
eapply_fresh Log_read_log in H7; eauto.
eapply_fresh Log_read_log in H11; eauto.
2: eauto.
cleanup_no_match.

eapply_fresh Log_TS_check_hash with (s2 := s2) in H8; cleanup_no_match.

eapply_fresh Log_check_hash_finished in H8; eauto; cleanup_no_match.
eapply_fresh Log_check_hash_finished in H12; eauto; cleanup_no_match.

repeat split_ors; logic_clean; subst; try congruence.

do 2 eexists; repeat econstructor; eauto.
simpl; repeat invert_exec_no_match; repeat econstructor.

exfalso; destruct H2; apply H2; eauto.
exfalso; apply H2; eauto.

repeat invert_exec_no_match.
assume (A0: (count (old_part hdr1) = count (old_part hdr2))).
eapply_fresh BatchOperations_TS_read_consecutive with (s2:= x1) in H9; cleanup_no_match.

do 2 eexists; repeat econstructor; eauto.
simpl.
repeat econstructor; eauto.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

repeat rewrite firstn_length_l; eauto.
rewrite map_length.
unfold  log_rep_explicit in *; logic_clean.
setoid_rewrite H14; eauto.

rewrite map_length.
unfold  log_rep_explicit in *; logic_clean.
setoid_rewrite H20; eauto.

eauto.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.
}
Unshelve.
{
     unfold log_rep_explicit, log_rep_inner, header_part_is_valid, txns_valid in *; logic_clean.
     rewrite <- H17, <- H29 in *; clear H17 H29.
     rewrite map_map in *.
     destruct valid_part; eauto.
     admit. (* Needs lemma *)
}
{
     unfold log_rep_explicit, log_rep_inner, header_part_is_valid, txns_valid in *; logic_clean.
     rewrite <- H21, <- H33 in *; clear H21 H33.
     rewrite map_map in *.
     destruct valid_part; eauto.
     rewrite <- A in *; clear A.
     eapply Log_check_hash_true in H8; try congruence.
     admit. (* Needs lemma *)
}
Admitted.




Lemma Log_TS_decrypt_txn:
forall u record1 record2 s1 s2 o s1' t log1 log2,

exec (CryptoDiskLang) u o s1 
(decrypt_txn record1 log1)
     (Finished s1' t) ->

length
     (firstn (addr_count record1 + data_count record1)
        (skipn (start record1) log1)) =
length
     (firstn (addr_count record2 + data_count record2)
        (skipn (start record2) log2)) ->
   
consistent_with_upds (snd (fst s2))
     (firstn (addr_count record2 + data_count record2)
        (skipn (start record2) log2))
     (map (fun ev : value => (key record2, decrypt (key record2) ev))
        (firstn (addr_count record2 + data_count record2)
           (skipn (start record2) log2))) ->

exists s2' t,
exec (CryptoDiskLang) u o s2 (decrypt_txn record2 log2) (Finished s2' t).
Proof.
     unfold decrypt_txn; intros; repeat invert_exec.
     eapply BatchOperations_TS_decrypt_all with (s2:= s2) (k2:= (key record2)) 
     (l2 := firstn (addr_count record2 + data_count record2)
     (skipn (start record2) log2)) in H; cleanup.
     do 2 eexists; repeat econstructor; eauto.
     all: eauto.
Qed.


Lemma Log_TS_decrypt_txns:
forall u records1 records2 s1 s2 o s1' t log1 log2,

exec (CryptoDiskLang) u o s1 
(decrypt_txns records1 log1)
     (Finished s1' t) ->

length records1 = length records2 ->

Forall2 (fun a t => length (firstn (addr_count a + data_count a) (skipn (start a) log1)) =
length (firstn (addr_count t + data_count t) (skipn (start t) log2))) records1 records2 ->

Forall (fun record2 => Forall2 (fun a v => (snd (fst s2)) a = Some v)
(firstn (addr_count record2 + data_count record2)
(skipn (start record2) log2))
(map (fun ev : value => (key record2, decrypt (key record2) ev))
(firstn (addr_count record2 + data_count record2)
   (skipn (start record2) log2)))) records2 ->

Forall (fun t => length (firstn (data_count t) (blocks_to_addr_list (firstn (addr_count t) (map (decrypt (key t)) (firstn (addr_count t + data_count t) (skipn (start t) log2)))))) =
length (skipn (addr_count t) (map (decrypt (key t)) (firstn (addr_count t + data_count t) (skipn (start t) log2))))) records2 ->

exists s2' t,
exec (CryptoDiskLang) u o s2 (decrypt_txns records2 log2) (Finished s2' t).
Proof.
     induction records1; 
     destruct records2; simpl; intros; 
     try lia;repeat invert_exec.
     repeat econstructor.
     inversion H1; inversion H2; inversion H3; cleanup.
     eapply Log_TS_decrypt_txn with (s2:= s2) (record2:= t) (log2:= log2) in H; cleanup.
     eapply IHrecords1 in H4; cleanup.

     do 2 eexists; repeat econstructor; eauto.
     all: eauto.
     {
          eapply decrypt_txn_finished in H; cleanup.
          eapply Forall_forall; intros.
          eapply Forall_forall in H14; eauto.
          eapply forall2_impl; eauto.
          eapply forall_forall2.
          rewrite combine_map_r.
          eapply Forall_forall; intros.
          apply in_map_iff in H11; cleanup; simpl in *.
          apply in_combine_same in H15; cleanup.
          eapply upd_batch_consistent_some in H12; eauto.
          eapply FunctionalExtensionality.equal_f in H6.
          rewrite H6; eauto.

          rewrite map_length; eauto.
          eauto.
     }
     eapply in_map_consistent_with_upds; eauto.
Qed.

Lemma Log_TS_recover:
forall u s1 s2 o s1' t hdr1 hdr2 txns1 txns2 
valid_part hdr_blockset1 hdr_blockset2 
log_blocksets1 log_blocksets2,

exec (CryptoDiskLang) u o s1 Log.recover
     (Finished s1' t) ->


log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 txns1
hdr_blockset1 log_blocksets1 s1 -> 
log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 txns2
hdr_blockset2 log_blocksets2 s2 -> 

(valid_part = Log.Old_Part ->
Log.hash (Log.current_part hdr1) <>
rolling_hash hash0
     (firstn (Log.count (Log.current_part hdr1)) (map fst log_blocksets1))) ->

(valid_part = Log.Old_Part ->
     Log.hash (Log.current_part hdr2) <>
     rolling_hash hash0
          (firstn (Log.count (Log.current_part hdr2)) (map fst log_blocksets2))) ->

(valid_part = Old_Part -> count (current_part hdr1) = count (current_part hdr2)) ->

Forall2
  (fun rec1 rec2 => 
  start rec1 = start rec2 /\
  addr_count rec1 = addr_count rec2 /\
  data_count rec1 = data_count rec2)
  (map record txns1) (map record txns2) ->

exists s2' t,
exec (CryptoDiskLang) u o s2 Log.recover
     (Finished s2' t).
Proof.
Transparent Log.recover.
unfold Log.recover in *.
simpl in *; intros;
cleanup; repeat invert_exec.
eapply_fresh Log_TS_read_encrypted_log in H; eauto; cleanup.
eapply_fresh Log_TS_write_header in H6; cleanup.

unfold log_header_rep, log_rep_general in *; cleanup.
eapply read_encrypted_log_finished in H; eauto; intros; try congruence.
eapply_fresh read_encrypted_log_finished in H7; eauto; intros; try congruence.
simpl in *; cleanup_no_match; simpl in *.

eapply Log_TS_decrypt_txns in H8; cleanup_no_match.
do 2 eexists; repeat econstructor; eauto.
rewrite cons_app.
repeat econstructor; eauto.

Admitted.
(* cleanup; eapply forall2_length; eauto. 
all: simpl; eauto.
2: {
     eapply forall2_impl; eauto.
     eapply forall_forall2.
     eapply Forall_forall; intros; cleanup; eauto.
     repeat rewrite firstn_length_l; eauto.
     
     rewrite skipn_length.
     destruct x2; eapply in_combine_r in H; simpl in *.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H28 in *; clear H28.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H29; eauto.
     unfold txn_well_formed, record_is_valid in H29; cleanup.
     rewrite firstn_length_l.
     lia.
     rewrite map_length; eauto.
     setoid_rewrite H24; eauto.

     rewrite skipn_length.
     destruct x2; eapply in_combine_l in H; simpl in *.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H36 in *; clear H36.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H37; eauto.
     unfold txn_well_formed, record_is_valid in H37; cleanup.
     rewrite firstn_length_l.
     lia.
     rewrite map_length; eauto.
     setoid_rewrite H32; eauto.
     eapply forall2_length; eauto.
}
{
     unfold write_header in *; repeat invert_exec.
     repeat cleanup_pairs; cleanup.
     eapply Forall_forall; intros; cleanup; eauto.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H16 in *; clear H16.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H17; eauto.
     unfold txn_well_formed, record_is_valid in H17; cleanup.
     eapply forall_forall2.
     rewrite combine_map_r.
     eapply Forall_forall; intros.
     apply in_map_iff in H34; cleanup; simpl in *.
     apply in_combine_same in H35; cleanup.
     rewrite <- skipn_firstn_comm in H34.
     rewrite firstn_firstn in H34.
     rewrite min_l in H34 by lia.
     rewrite skipn_firstn_comm in H34.
     rewrite firstn_sum_split in H34.
     apply in_app_iff in H34.
     split_ors.

     rewrite <- H1 in H34.
     apply in_map_iff in H34; cleanup.
     eapply in_seln_exists in H36; cleanup.
     rewrite <- H34, <- H37; eauto.
     rewrite encrypt_decrypt.
     apply H31; eauto.
     
     rewrite skipn_skipn in H34.
     rewrite <- H12 in H34.
     apply in_map_iff in H34; cleanup.
     eapply in_seln_exists in H36; cleanup.
     rewrite <- H34, <- H37; eauto.
     rewrite encrypt_decrypt.
     apply H32; eauto.
     rewrite map_length; eauto.
}
{
     repeat cleanup_pairs; cleanup.
     eapply Forall_forall; intros; cleanup; eauto.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H19 in *; clear H19.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H20; eauto.
     unfold txn_well_formed, record_is_valid in H20; cleanup.
     rewrite firstn_length_l.
     rewrite skipn_length, map_length.
     rewrite firstn_length_l.
     lia.
     rewrite skipn_length.
     rewrite firstn_length_l.
     lia.
     rewrite map_length. 
     setoid_rewrite H13; eauto.

     eapply PeanoNat.Nat.le_trans.
     eauto.
     apply blocks_to_addr_list_length_le_preserve.
     rewrite firstn_length_l; eauto.
     rewrite map_length.
     rewrite firstn_length_l.
     lia.
     rewrite skipn_length.
     rewrite firstn_length_l.
     lia.
     rewrite map_length. 
     setoid_rewrite H13; eauto.
}
Qed.
*)





(***** Crashed TS *****)
Lemma Log_TS_read_header_crashed:
forall u s1 s2 o s1' ,
exec (CryptoDiskLang) u o s1 read_header (Crashed s1') ->
exists s2',
exec (CryptoDiskLang) u o s2 read_header (Crashed s2').
Proof.
unfold read_header in *.
simpl in *; intros;
cleanup; repeat invert_exec.
split_ors; cleanup; repeat invert_exec.
eexists; repeat econstructor; eauto.
eexists; repeat econstructor; eauto.
Qed.


Lemma Log_TS_write_header_crashed:
forall u s1 s2 o s1' hdr1 hdr2,
exec (CryptoDiskLang) u o s1 
(write_header hdr1) (Crashed s1') ->
exists s2',
exec (CryptoDiskLang) u o s2 
(write_header hdr2) (Crashed s2').
Proof.
unfold write_header in *.
simpl in *; intros;
cleanup; repeat invert_exec.
eexists; repeat econstructor; eauto.
Qed.



Lemma Log_TS_check_hash_crashed:
forall u l1 l2 s1 s2 o s1' h1 h2,
exec (CryptoDiskLang) u o s1 
(check_hash l1 h1)
     (Crashed s1') ->
length l1 = length l2 ->
(forall x : nat,
consistent_with_upds (snd (fst (fst s1)))
  (firstn x (rolling_hash_list hash0 l1))
  (firstn x (combine (hash0 :: rolling_hash_list hash0 l1) l1)) ->
consistent_with_upds (snd (fst (fst s2)))
  (firstn x (rolling_hash_list hash0 l2))
  (firstn x (combine (hash0 :: rolling_hash_list hash0 l2) l2))) ->
exists s2',
exec (CryptoDiskLang) u o s2 
(check_hash l2 h2)
     (Crashed s2').
Proof.
Opaque combine.
unfold check_hash in *.
simpl in *; intros;
cleanup_no_match; repeat invert_exec_no_match.
split_ors; cleanup_no_match.
eapply BatchOperations_TS_hash_all_crashed with 
(s2 := s2) (l2:= l2)in H; cleanup_no_match.
eexists; repeat econstructor; eauto.
all: eauto.

eapply BatchOperations_TS_hash_all with 
(s2 := s2) (l2:= l2)in H2; cleanup_no_match.
destruct (hash_dec x0 h1);
repeat invert_exec_no_match;
destruct (hash_dec x4 h2);
eexists; repeat econstructor; eauto;
destruct (hash_dec x4 h2); try congruence; try econstructor.
all: eauto.
{
     eapply hash_all_finished in H2; cleanup_no_match.
     specialize (H1 (length l1)).
     do 4 rewrite firstn_oob in H1.
     eauto.
     all: repeat rewrite combine_length; try lia.
     all: repeat rewrite rolling_hash_list_length; try lia.
}
Qed.


Lemma Log_TS_read_encrypted_log_crashed:
forall u s1 s2 o s1' hdr1 hdr2 txns1 txns2
valid_part hdr_blockset1 hdr_blockset2 
log_blocksets1 log_blocksets2,

exec (CryptoDiskLang) u o s1 read_encrypted_log (Crashed s1') ->

log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 txns1
hdr_blockset1 log_blocksets1 s1 -> 
log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 txns2
hdr_blockset2 log_blocksets2 s2 -> 

(Log.hash (Log.current_part hdr1) <>
rolling_hash hash0
     (firstn (Log.count (Log.current_part hdr1)) (map fst log_blocksets1)) <->
Log.hash (Log.current_part hdr2) <>
     rolling_hash hash0
          (firstn (Log.count (Log.current_part hdr2)) (map fst log_blocksets2))) ->

Forall2
(fun rec1 rec2 : Log.txn_record =>
     Log.start rec1 = Log.start rec2 /\
     Log.addr_count rec1 = Log.addr_count rec2 /\
     Log.data_count rec1 = Log.data_count rec2)
(map Log.record txns1)
(map Log.record txns2) ->
( forall x, 
consistent_with_upds (snd (fst (fst s1)))
(firstn x (rolling_hash_list hash0
     (firstn (count (current_part hdr1)) (map fst log_blocksets1))))
(firstn x (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (current_part hdr1)) (map fst log_blocksets1)))
     (firstn (count (current_part hdr1)) (map fst log_blocksets1)))) ->

consistent_with_upds (snd (fst (fst s2)))
(firstn x (rolling_hash_list hash0
     (firstn (count (current_part hdr2)) (map fst log_blocksets2))))
(firstn x (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (current_part hdr2)) (map fst log_blocksets2)))
     (firstn (count (current_part hdr2)) (map fst log_blocksets2))))) ->

(forall x,
consistent_with_upds (snd (fst (fst s1)))
(firstn x (rolling_hash_list hash0
     (firstn (count (old_part hdr1)) (map fst log_blocksets1))))
(firstn x (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (old_part hdr1)) (map fst log_blocksets1)))
     (firstn (count (old_part hdr1)) (map fst log_blocksets1)))) ->

consistent_with_upds (snd (fst (fst s2)))
(firstn x (rolling_hash_list hash0
     (firstn (count (old_part hdr2)) (map fst log_blocksets2))))
(firstn x (combine
     (hash0
      :: rolling_hash_list hash0
           (firstn (count (old_part hdr2)) (map fst log_blocksets2)))
     (firstn (count (old_part hdr2)) (map fst log_blocksets2))))) ->

(valid_part = Old_Part -> count (current_part hdr1) = count (current_part hdr2)) ->

exists s2',
exec (CryptoDiskLang) u o s2 read_encrypted_log (Crashed s2').
Proof.
Opaque read_header check_hash.
unfold read_encrypted_log in *.
simpl in *; intros;
cleanup_no_match; repeat invert_exec_no_match.
split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh Log_TS_read_header_crashed with (s2:= s2) in H; cleanup_no_match.
     eexists; repeat econstructor; eauto.
}

eapply_fresh Log_TS_read_header with (s2:= s2) in H7; cleanup_no_match.
eapply_fresh Log_read_header_finished in H; eauto.
eapply_fresh Log_read_header_finished in H7; eauto.
cleanup_no_match.
assume (A: (count (current_part hdr1) = count (current_part hdr2))).
split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh BatchOperations_TS_read_consecutive_crashed with (s2:= s2) in H8; cleanup_no_match.
     eexists; repeat econstructor; eauto.

     pose proof data_fits_in_disk.
     pose proof data_start_where_log_ends.
     pose proof all_fits_to_data_region.
     unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
     lia.
}

eapply_fresh BatchOperations_TS_read_consecutive with (s2:= s2) in H9; cleanup_no_match.
unfold log_header_rep, log_rep_general in *; cleanup_no_match.
eapply_fresh Log_read_log in H9; eauto.
eapply_fresh Log_read_log in H8; eauto.
2: eauto.
cleanup_no_match.

split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh Log_TS_check_hash_crashed with (s2 := s2) in H10; cleanup_no_match.
     eexists; repeat econstructor; eauto.
     repeat rewrite firstn_length_l; eauto.

     rewrite map_length.
     unfold  log_rep_explicit in *; logic_clean.
     setoid_rewrite H13; eauto.

     rewrite map_length.
     unfold  log_rep_explicit in *; logic_clean.
     setoid_rewrite H19; eauto.

     eauto.
}

eapply_fresh Log_TS_check_hash with (s2 := s2) in H11; cleanup_no_match.

eapply_fresh Log_check_hash_finished in H11; eauto; cleanup_no_match.
eapply_fresh Log_check_hash_finished in H10; eauto; cleanup_no_match.
repeat split_ors; logic_clean; subst; try congruence.
{
     eexists; repeat econstructor; eauto.
     simpl; repeat invert_exec_no_match; repeat econstructor.
}
{
     exfalso; destruct H2; apply H2; eauto.
}
{
     exfalso; apply H2; eauto.
}

repeat invert_exec_no_match.
assume (A0: (count (old_part hdr1) = count (old_part hdr2))).
split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh BatchOperations_TS_read_consecutive_crashed with (s2:= x4) in H12; cleanup_no_match.
     eexists; repeat econstructor; eauto.
     simpl; repeat econstructor; eauto.

     pose proof data_fits_in_disk.
     pose proof data_start_where_log_ends.
     pose proof all_fits_to_data_region.
     unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
     lia.
}
{
     eapply_fresh BatchOperations_TS_read_consecutive with (s2:= x4) in H13; cleanup_no_match.
     eexists; repeat econstructor; eauto.
     simpl; repeat econstructor; eauto.

     pose proof data_fits_in_disk.
     pose proof data_start_where_log_ends.
     pose proof all_fits_to_data_region.
     unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
     lia.
}

repeat rewrite firstn_length_l; eauto.
rewrite map_length.
unfold  log_rep_explicit in *; logic_clean.
setoid_rewrite H14; eauto.

rewrite map_length.
unfold  log_rep_explicit in *; logic_clean.
setoid_rewrite H20; eauto.

{
     specialize (H4 (length ((firstn (count (current_part hdr2)) (map fst log_blocksets1))))).
     do 4 rewrite firstn_oob with (n:= (length
     (firstn (count (current_part hdr2)) (map fst log_blocksets1)))) in H4.
     Transparent check_hash.
     unfold check_hash in *.
     invert_exec'' H11.
     eapply BatchOperations.hash_all_finished in H18.
     cleanup; eauto.
     all: repeat rewrite combine_length;
     simpl length;
     repeat rewrite rolling_hash_list_length;
     repeat rewrite firstn_length;
     repeat rewrite map_length;
     try lia.
     all: unfold log_rep_explicit in *; logic_clean;
     setoid_rewrite H14; setoid_rewrite H20;
     lia.
}

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

pose proof data_fits_in_disk.
pose proof data_start_where_log_ends.
pose proof all_fits_to_data_region.
unfold log_header_rep, log_rep_general,  log_rep_explicit in *; logic_clean.
lia.

Unshelve.
all: admit.
Admitted.



Lemma Log_TS_decrypt_txn_crashed:
forall u record1 record2 s1 s2 o s1' log1 log2,

exec (CryptoDiskLang) u o s1 
(decrypt_txn record1 log1)
     (Crashed s1') ->

length
     (firstn (addr_count record1 + data_count record1)
        (skipn (start record1) log1)) =
length
     (firstn (addr_count record2 + data_count record2)
        (skipn (start record2) log2)) ->
   
consistent_with_upds (snd (fst s2))
     (firstn (addr_count record2 + data_count record2)
        (skipn (start record2) log2))
     (map (fun ev : value => (key record2, decrypt (key record2) ev))
        (firstn (addr_count record2 + data_count record2)
           (skipn (start record2) log2))) ->

exists s2',
exec (CryptoDiskLang) u o s2 (decrypt_txn record2 log2) (Crashed s2').
Proof.
     unfold decrypt_txn; intros; repeat invert_exec.
     split_ors; cleanup; repeat invert_exec.
     {
          eapply BatchOperations_TS_decrypt_all_crashed in H; eauto.
          cleanup.
          eexists; repeat constructor; eauto.
     }

     eapply BatchOperations_TS_decrypt_all with (s2:= s2) (k2:= (key record2)) 
     (l2 := firstn (addr_count record2 + data_count record2)
     (skipn (start record2) log2)) in H2; cleanup.
     eexists; repeat econstructor; eauto.
     all: eauto.
Qed.


Lemma Log_TS_decrypt_txns_crashed:
forall u records1 records2 s1 s2 o s1' log1 log2,

exec (CryptoDiskLang) u o s1 
(decrypt_txns records1 log1)
     (Crashed s1') ->

length records1 = length records2 ->

Forall2 (fun a t => length (firstn (addr_count a + data_count a) (skipn (start a) log1)) =
length (firstn (addr_count t + data_count t) (skipn (start t) log2))) records1 records2 ->

Forall (fun record2 => Forall2 (fun a v => (snd (fst s2)) a = Some v)
(firstn (addr_count record2 + data_count record2)
(skipn (start record2) log2))
(map (fun ev : value => (key record2, decrypt (key record2) ev))
(firstn (addr_count record2 + data_count record2)
   (skipn (start record2) log2)))) records2 ->

Forall (fun t => length (firstn (data_count t) (blocks_to_addr_list (firstn (addr_count t) (map (decrypt (key t)) (firstn (addr_count t + data_count t) (skipn (start t) log2)))))) =
length (skipn (addr_count t) (map (decrypt (key t)) (firstn (addr_count t + data_count t) (skipn (start t) log2))))) records2 ->

exists s2',
exec (CryptoDiskLang) u o s2 (decrypt_txns records2 log2) (Crashed s2').
Proof.
     induction records1; 
     destruct records2; simpl; intros; 
     try lia;repeat invert_exec.
     repeat econstructor.

     inversion H1; inversion H2; inversion H3; cleanup.
     split_ors; cleanup; repeat invert_exec.
     {
          eapply Log_TS_decrypt_txn_crashed with (s2:= s2) (record2:= t) (log2:= log2) in H; cleanup.
          eexists; econstructor; eauto.
          all: eauto.
          eapply in_map_consistent_with_upds; eauto.
     }
eapply Log_TS_decrypt_txn with (s2:= s2) (record2:= t) (log2:= log2) in H4; cleanup.
split_ors; cleanup; repeat invert_exec.
{
     eapply IHrecords1 in H4; cleanup.

     eexists; repeat econstructor; eauto.
     all: eauto.
     {
          eapply decrypt_txn_finished in H; cleanup.
          eapply Forall_forall; intros.
          eapply Forall_forall in H13; eauto.
          eapply forall2_impl; eauto.
          eapply forall_forall2.
          rewrite combine_map_r.
          eapply Forall_forall; intros.
          apply in_map_iff in H11; cleanup; simpl in *.
          apply in_combine_same in H15; cleanup.
          eapply upd_batch_consistent_some in H10; eauto.
          eapply FunctionalExtensionality.equal_f in H6.
          rewrite H6; eauto.

          rewrite map_length; eauto.
          eauto.
     }
}
{
     eapply Log_TS_decrypt_txns in H5; cleanup.
     eexists; repeat econstructor; eauto.
     all: eauto.
     {
          eapply decrypt_txn_finished in H; cleanup.
          eapply Forall_forall; intros.
          eapply Forall_forall in H13; eauto.
          eapply forall2_impl; eauto.
          eapply forall_forall2.
          rewrite combine_map_r.
          eapply Forall_forall; intros.
          apply in_map_iff in H11; cleanup; simpl in *.
          apply in_combine_same in H15; cleanup.
          eapply upd_batch_consistent_some in H10; eauto.
          eapply FunctionalExtensionality.equal_f in H6.
          rewrite H6; eauto.

          rewrite map_length; eauto.
          eauto.
     }
}
all: eauto.
eapply in_map_consistent_with_upds; eauto.
Qed.

Lemma Log_TS_recover_crashed:
forall u s1 s2 o s1' hdr1 hdr2 txns1 txns2 
valid_part hdr_blockset1 hdr_blockset2 
log_blocksets1 log_blocksets2,

exec (CryptoDiskLang) u o s1 Log.recover (Crashed s1') ->


log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 txns1
hdr_blockset1 log_blocksets1 s1 -> 
log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 txns2
hdr_blockset2 log_blocksets2 s2 -> 

(valid_part = Log.Old_Part ->
Log.hash (Log.current_part hdr1) <>
rolling_hash hash0
     (firstn (Log.count (Log.current_part hdr1)) (map fst log_blocksets1))) ->

(valid_part = Log.Old_Part ->
     Log.hash (Log.current_part hdr2) <>
     rolling_hash hash0
          (firstn (Log.count (Log.current_part hdr2)) (map fst log_blocksets2))) ->

(valid_part = Old_Part -> count (current_part hdr1) = count (current_part hdr2)) ->

Forall2
  (fun rec1 rec2 => 
  start rec1 = start rec2 /\
  addr_count rec1 = addr_count rec2 /\
  data_count rec1 = data_count rec2)
  (map record txns1) (map record txns2) ->

exists s2',
exec (CryptoDiskLang) u o s2 Log.recover (Crashed s2').
Proof.
Opaque Log.read_encrypted_log.
Transparent Log.recover.
unfold Log.recover in *.
simpl in *; intros;
cleanup; repeat invert_exec.
split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh Log_TS_read_encrypted_log_crashed in H; eauto; cleanup.
     eexists; repeat econstructor; eauto.
     all: eauto.
     all: admit.
}
eapply_fresh Log_TS_read_encrypted_log in H6; eauto; cleanup.
unfold log_header_rep, log_rep_general in *; cleanup.
eapply_fresh read_encrypted_log_finished in H; eauto; intros; try congruence.
eapply_fresh read_encrypted_log_finished in H6; eauto; intros; try congruence.
simpl in *; cleanup_no_match; simpl in *.

split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eapply_fresh Log_TS_write_header_crashed in H7; cleanup_no_match.
     eexists; repeat econstructor; eauto.
}
eapply_fresh Log_TS_write_header in H8; cleanup_no_match.
split_ors; cleanup_no_match; repeat invert_exec_no_match.
{
     eexists; repeat econstructor; eauto.
}
(*
unfold log_header_rep, log_rep_general in *; cleanup.
eapply read_encrypted_log_finished in H; eauto; intros; try congruence.
eapply_fresh read_encrypted_log_finished in H7; eauto; intros; try congruence.
simpl in *; cleanup_no_match; simpl in *.
*)
eapply Log_TS_decrypt_txns_crashed in e1; cleanup_no_match.
eexists; repeat econstructor; eauto.
all: simpl; eauto.

Admitted.
(* cleanup; eapply forall2_length; eauto. 
all: simpl; eauto.
2: {
     eapply forall2_impl; eauto.
     eapply forall_forall2.
     eapply Forall_forall; intros; cleanup; eauto.
     repeat rewrite firstn_length_l; eauto.
     
     rewrite skipn_length.
     destruct x2; eapply in_combine_r in H; simpl in *.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H28 in *; clear H28.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H29; eauto.
     unfold txn_well_formed, record_is_valid in H29; cleanup.
     rewrite firstn_length_l.
     lia.
     rewrite map_length; eauto.
     setoid_rewrite H24; eauto.

     rewrite skipn_length.
     destruct x2; eapply in_combine_l in H; simpl in *.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H36 in *; clear H36.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H37; eauto.
     unfold txn_well_formed, record_is_valid in H37; cleanup.
     rewrite firstn_length_l.
     lia.
     rewrite map_length; eauto.
     setoid_rewrite H32; eauto.
     eapply forall2_length; eauto.
}
{
     unfold write_header in *; repeat invert_exec.
     repeat cleanup_pairs; cleanup.
     eapply Forall_forall; intros; cleanup; eauto.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H16 in *; clear H16.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H17; eauto.
     unfold txn_well_formed, record_is_valid in H17; cleanup.
     eapply forall_forall2.
     rewrite combine_map_r.
     eapply Forall_forall; intros.
     apply in_map_iff in H34; cleanup; simpl in *.
     apply in_combine_same in H35; cleanup.
     rewrite <- skipn_firstn_comm in H34.
     rewrite firstn_firstn in H34.
     rewrite min_l in H34 by lia.
     rewrite skipn_firstn_comm in H34.
     rewrite firstn_sum_split in H34.
     apply in_app_iff in H34.
     split_ors.

     rewrite <- H1 in H34.
     apply in_map_iff in H34; cleanup.
     eapply in_seln_exists in H36; cleanup.
     rewrite <- H34, <- H37; eauto.
     rewrite encrypt_decrypt.
     apply H31; eauto.
     
     rewrite skipn_skipn in H34.
     rewrite <- H12 in H34.
     apply in_map_iff in H34; cleanup.
     eapply in_seln_exists in H36; cleanup.
     rewrite <- H34, <- H37; eauto.
     rewrite encrypt_decrypt.
     apply H32; eauto.
     rewrite map_length; eauto.
}
{
     repeat cleanup_pairs; cleanup.
     eapply Forall_forall; intros; cleanup; eauto.
     unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
     rewrite <- H19 in *; clear H19.
     apply in_map_iff in H; cleanup; simpl in *.
     eapply Forall_forall in H20; eauto.
     unfold txn_well_formed, record_is_valid in H20; cleanup.
     rewrite firstn_length_l.
     rewrite skipn_length, map_length.
     rewrite firstn_length_l.
     lia.
     rewrite skipn_length.
     rewrite firstn_length_l.
     lia.
     rewrite map_length. 
     setoid_rewrite H13; eauto.

     eapply PeanoNat.Nat.le_trans.
     eauto.
     apply blocks_to_addr_list_length_le_preserve.
     rewrite firstn_length_l; eauto.
     rewrite map_length.
     rewrite firstn_length_l.
     lia.
     rewrite skipn_length.
     rewrite firstn_length_l.
     lia.
     rewrite map_length. 
     setoid_rewrite H13; eauto.
}

Qed.
*)