Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE.
Require Import Not_Init HSS ATCD_ORS.
Require Import ATCD_TS_Recovery ATCD_TS_Common ATCD_TS_Operations  ATCD_TS_BatchOperations.

Import FileDiskLayer.
Set Nested Proofs Allowed.
Opaque File.recover.

Lemma ATCD_TS_Log_read_header:
forall n u txns1 txns2 hdr1 hdr2,
 Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.read_header)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.read_header)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
 unfold Log.read_header; intros; simpl.
 eapply ATCD_TS_compositional.
 intros; apply ATCD_TS_Disk_read; eauto.
 intuition.
 intros; apply ATCD_TS_ret.
 simpl; intros; eauto.
 repeat invert_exec; eauto.
 Opaque Log.read_header.
Qed.



Lemma ATCD_TS_Log_update_header:
forall n u h1 h2 txns1 txns2 hdr1 hdr2,
Termination_Sensitive u
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.update_header h1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.update_header h2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(equivalent_for_recovery txns1 txns2
Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
 intros; simpl.
 eapply ATCD_TS_compositional.
 intros; apply ATCD_TS_Log_read_header.
 2: shelve.
 intros.
 eapply ATCD_TS_Disk_write; intuition.
 Unshelve.
 intros.
 repeat invert_lift2; cleanup.
 Transparent Log.read_header.
 unfold Log.read_header in *; repeat invert_exec; eauto.
 repeat cleanup_pairs; simpl in *; eauto.
 Opaque Log.read_header Log.update_header.
Qed.



Definition equivalent_for_commit o l_a1 l_v1 l_a2 l_v2 := 
 fun s1 s2 : state ATCDLang =>
(forall t : key,
  In (OpToken ATCDCore (Token2 AuthenticationOperation TCDCore
     (Token2 (ListOperation (addr * value)) (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation) 
  (Token2 (CacheOperation addr_dec value) CryptoDiskOperation 
  (Token1 CryptoOperation 
  (DiskOperation addr_dec value (fun a => a < disk_size)) (Key t)))))) 
  o ->
~ In t (fst (fst (fst (snd (snd (snd s1)))))) ->
~ In t (fst (fst (fst (snd (snd (snd s2))))))) /\
(forall r2 : key,
In (OpToken ATCDCore (Token2 AuthenticationOperation TCDCore
   (Token2 (ListOperation (addr * value)) (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation) 
(Token2 (CacheOperation addr_dec value) CryptoDiskOperation 
(Token1 CryptoOperation 
(DiskOperation addr_dec value (fun a => a < disk_size)) (Key r2)))))) 
o -> 
(forall x,
consistent_with_upds (snd (fst (fst (snd (snd (snd s1)))))) 
(firstn x (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s1))) hdr_block_num))))) 
(map (encrypt r2) ((addr_list_to_blocks
(map (Nat.add data_start)
   l_a1)) ++ l_v1))))
(firstn x (combine ((Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s1))) hdr_block_num))))) 
:: rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s1))) hdr_block_num))))) (map (encrypt r2) 
((addr_list_to_blocks
(map (Nat.add data_start)
   l_a1)) ++ l_v1))) 
   (map (encrypt r2)((addr_list_to_blocks
   (map (Nat.add data_start)
      l_a1)) ++ l_v1)))) ->
consistent_with_upds (snd (fst (fst (snd (snd (snd s2)))))) 
(firstn x (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s2))) hdr_block_num))))) 
(map (encrypt r2) ((addr_list_to_blocks
(map (Nat.add data_start)
   l_a2)) ++ l_v2))))
(firstn x (combine ((Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s2))) hdr_block_num))))) :: 
rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s2))) hdr_block_num))))) 
(map (encrypt r2) ((addr_list_to_blocks
(map (Nat.add data_start)
   l_a2)) ++ l_v2))) 
   (map
   (encrypt r2) ((addr_list_to_blocks
   (map (Nat.add data_start)
      l_a2)) ++ l_v2)))))) /\
      (forall r : key,
      In (OpToken ATCDCore (Token2 AuthenticationOperation TCDCore
         (Token2 (ListOperation (addr * value)) (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation) 
      (Token2 (CacheOperation addr_dec value) CryptoDiskOperation 
      (Token1 CryptoOperation 
      (DiskOperation addr_dec value (fun a => a < disk_size)) (Key r)))))) 
      o ->
(forall x : nat,
consistent_with_upds
 (snd (fst (snd (snd (snd s1)))))
 (firstn x
    (map (encrypt r)
       (addr_list_to_blocks
          (map (Nat.add data_start)
             l_a1) ++ l_v1)))
 (firstn x
    (map (fun v : value => (r, v))
       (addr_list_to_blocks
          (map (Nat.add data_start)
             l_a1) ++ l_v1))) ->
consistent_with_upds
 (snd (fst (snd (snd (snd s2)))))
 (firstn x
    (map (encrypt r)
       (addr_list_to_blocks
          (map (Nat.add data_start)
             l_a2) ++ l_v2)))
 (firstn x
    (map (fun v : value => (r, v))
       (addr_list_to_blocks
          (map (Nat.add data_start)
             l_a2) ++ l_v2))))).



Lemma ATCD_TS_Log_commit_txn:
forall n u l_a1 l_a2 l_v1 l_v2 txns1 txns2 hdr1 hdr2 lo s1 s2,
length (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1) =
length (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2) ->
Log.count (Log.current_part hdr2) +(length
   (addr_list_to_blocks
      (map (Nat.add data_start) l_a2)) +
 length l_v2) <= log_length ->

Termination_Sensitive_explicit u lo s1 s2
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.commit_txn
                (addr_list_to_blocks
                   (map (Nat.add data_start)
                      l_a1)) l_v1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.commit_txn
                (addr_list_to_blocks
                   (map (Nat.add data_start)
                      l_a2)) l_v2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => 
equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
equivalent_for_commit (seln lo 0 []) l_a1 l_v1 l_a2 l_v2 s1 s2)
(ATCD_reboot_list n).
Proof.
 Transparent Log.commit_txn.
 Opaque Log.update_header.
 unfold Log.commit_txn; intros; simpl.
 eapply ATCD_TS_explicit_compositional.
 intros; eapply TS_explicit_eqv_impl.
 intros; eapply TS_explicit_to_TS.
 intros; apply ATCD_TS_Log_read_header.
 intros; cleanup; eauto.
 2: shelve.

 intros. 
 repeat invert_lift2; cleanup_no_match.
 unfold equivalent_for_recovery in *; cleanup_no_match.
 eapply Log_read_header_finished in H17; eauto.
 eapply Log_read_header_finished in H11; eauto.
 cleanup_no_match.
 repeat cleanup_pairs; simpl in *.
 eapply ATCD_TS_explicit_compositional.
 intros. eapply TS_explicit_eqv_impl.
 intros; apply ATCD_TS_Crypto_getkey.
 shelve.
 2: shelve.

 simpl; intros.
 repeat invert_exec; cleanup_no_match.
 intros; eapply TS_explicit_to_TS.
 eapply ATCD_TS_compositional.
 intros; eapply TS_eqv_impl.
 apply ATCD_TS_BatchOperations_encrypt_all; eauto.
 simpl; shelve.
 2: shelve.

 intros.
 repeat invert_lift2; cleanup_no_match.
 eapply BatchOperations.encrypt_all_finished in H32; eauto.
 eapply BatchOperations.encrypt_all_finished in H20; eauto.
 cleanup_no_match.
 repeat cleanup_pairs; simpl in *.
 eapply ATCD_TS_compositional.
 intros; eapply TS_eqv_impl.
 intros; apply ATCD_TS_BatchOperations_hash_all; eauto.
 repeat rewrite map_length; eauto.
 shelve.
 2: shelve.

 simpl; intros.
 repeat invert_lift2; cleanup_no_match.
 eapply BatchOperations.hash_all_finished in H36; eauto.
 eapply BatchOperations.hash_all_finished in H29; eauto.
 repeat cleanup_pairs; simpl in *.
 eapply ATCD_TS_compositional.
 intros; eapply TS_eqv_impl.
 intros; apply ATCD_TS_BatchOperations_write_batch; eauto.
 all: repeat rewrite seq_length; repeat rewrite map_length; eauto.
 {
    eapply Forall_forall; intros.
    apply in_seq in H2.
    rewrite app_length in H2.
    rewrite data_fits_in_disk.
    rewrite data_start_where_log_ends.
    lia.
 }
 shelve.
 2: shelve.

 simpl; intros.
 repeat invert_lift2; cleanup_no_match.
 eapply BatchOperations.write_consecutive_finished in H40; eauto.
 eapply BatchOperations.write_consecutive_finished in H33; eauto.
 all: repeat rewrite seq_length; repeat rewrite  map_length; eauto.
 repeat cleanup_pairs; simpl in *.
 cleanup_no_match.
 eapply ATCD_TS_compositional.
 intros; apply ATCD_TS_Log_update_header; eauto.
 intros; apply ATCD_TS_Disk_sync; eauto.
 simpl; shelve.

 Unshelve.
 {
    instantiate (1:= fun r1 r2 s1 s2 =>
    equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
    equivalent_for_commit (seln lo 0 []) l_a1 l_v1 l_a2 l_v2 s1 s2).
    simpl; intros.
    repeat invert_lift2; cleanup_no_match.
    unfold equivalent_for_recovery in *; cleanup_no_match.
    eapply Log_read_header_finished in H17; eauto.
    eapply Log_read_header_finished in H11; eauto.
    cleanup_no_match; intuition eauto.
    do 2 eexists; intuition eauto.
    repeat cleanup_pairs; eauto.
 }
 5:{
    simpl; intuition eauto.
    unfold equivalent_for_commit in *; cleanup_no_match.
    repeat cleanup_pairs; eauto.
    simpl in *.
    setoid_rewrite H1 in H8.
    eapply H8; eauto.
 }
 {
    instantiate (1:= fun r1 r2 s6 s7 =>
    equivalent_for_recovery txns1 
txns2 Log.Current_Part hdr1 
hdr2 s6 s7 /\
(forall r5 : key,
In
  (OpToken ATCDCore
     (Token2 AuthenticationOperation TCDCore
        (Token2 (ListOperation (addr * value))
           (HorizontalComposition (CacheOperation addr_dec value)
              CryptoDiskOperation)
           (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
              (Token1 CryptoOperation
                 (DiskOperation addr_dec value (fun a : addr => a < disk_size))
                 (Key r5)))))) (seln lo 0 []) ->
forall x : nat,
consistent_with_upds (snd (fst (fst (snd (snd (snd s6))))))
  (firstn x
     (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s6))) hdr_block_num)))))
        (map (encrypt r5)
           (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1))))
  (firstn x
     match
       map (encrypt r5)
         (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1)
     with
     | [] => []
     | y :: tl' =>
         (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s6))) hdr_block_num)))), y)
         :: combine
              (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s6))) hdr_block_num)))))
                 (map (encrypt r5)
                    (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1)))
              tl'
     end) ->
consistent_with_upds (snd (fst (fst (snd (snd (snd s7))))))
  (firstn x
     (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s7))) hdr_block_num)))))
        (map (encrypt r5)
           (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2))))
  (firstn x
     match
       map (encrypt r5)
         (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2)
     with
     | [] => []
     | y :: tl' =>
         (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s7))) hdr_block_num)))), y)
         :: combine
              (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s7))) hdr_block_num)))))
                 (map (encrypt r5)
                    (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2)))
              tl'
     end)) /\
(forall r : key,
        In
          (OpToken ATCDCore
             (Token2 AuthenticationOperation TCDCore
                (Token2 (ListOperation (addr * value))
                   (HorizontalComposition (CacheOperation addr_dec value)
                      CryptoDiskOperation)
                   (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
                      (Token1 CryptoOperation
                         (DiskOperation addr_dec value
                            (fun a : addr => a < disk_size)) 
                         (Key r)))))) (seln lo 0 []) ->
        forall x : nat,
        consistent_with_upds (snd (fst (snd (snd (snd s6)))))
          (firstn x
             (map (encrypt r)
                (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1)))
          (firstn x
             (map (fun v : value => (r, v))
                (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1))) ->
        consistent_with_upds (snd (fst (snd (snd (snd s7)))))
          (firstn x
             (map (encrypt r)
                (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2)))
          (firstn x
             (map (fun v : value => (r, v))
                (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2))))).

    simpl; eauto.
    intros; repeat invert_exec.
    cleanup_no_match; simpl in *.
    intuition eauto.

    repeat cleanup_pairs; simpl in *.
    unfold equivalent_for_recovery in *; cleanup_no_match.
    simpl in *; do 2 eexists; intuition eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_new_key; eauto.
    eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_new_key; eauto.
    eauto.

    all: unfold equivalent_for_commit in *; 
    cleanup_no_match; simpl in *;
    intuition.
 }
 5: {
    simpl; intros; eauto.
    cleanup_no_match; intuition eauto.
    setoid_rewrite H1 in H6; simpl in *;
    eapply H6; intuition eauto.
    simpl; intuition.
 }
 7: {
    instantiate (5:= fun _ _ s19 s20 =>
    equivalent_for_recovery txns1 
      txns2 Log.Current_Part 
      hdr1 hdr2 s19 s20 /\
      (forall x : nat,
      consistent_with_upds (snd (fst (fst (snd (snd (snd s19))))))
        (firstn x
           (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s19))) hdr_block_num)))))
              (map (encrypt r2) (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1))))
        (firstn x
           match
             map (encrypt r2) (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1)
           with
           | [] => []
           | y :: tl' =>
               (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s19))) hdr_block_num)))), y)
               :: combine
                    (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s19))) hdr_block_num)))))
                       (map (encrypt r2)
                          (addr_list_to_blocks (map (Nat.add data_start) l_a1) ++ l_v1))) tl'
           end) ->
      consistent_with_upds (snd (fst (fst (snd (snd (snd s20))))))
        (firstn x
           (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s20))) hdr_block_num)))))
              (map (encrypt r2) (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2))))
        (firstn x
           match
             map (encrypt r2) (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2)
           with
           | [] => []
           | y :: tl' =>
               (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s20))) hdr_block_num)))), y)
               :: combine
                    (rolling_hash_list (Log.hash (Log.current_part (Log.decode_header (fst (snd (snd (snd (snd s20))) hdr_block_num)))))
                       (map (encrypt r2)
                          (addr_list_to_blocks (map (Nat.add data_start) l_a2) ++ l_v2))) tl'
           end))).
    simpl; eauto.
    intros; intuition eauto.
    unfold equivalent_for_recovery, Log.log_rep_explicit,
    Log.log_header_block_rep in H10; cleanup_no_match; intuition.
 }
 {
    simpl; eauto.
    intros;
    repeat invert_lift2; cleanup_no_match.
    eapply BatchOperations.encrypt_all_finished in H26.
    eapply BatchOperations.encrypt_all_finished in H34.
    cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    intuition eauto.

    repeat cleanup_pairs; simpl in *.
    unfold equivalent_for_recovery in *; cleanup_no_match.
    simpl in *; do 2 eexists; intuition eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
    eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
    eauto.

    setoid_rewrite H1 in H10; 
    simpl in *. 
    eapply H10; eauto.
    simpl; intuition.
 }
 7: {
    simpl; eauto.
    instantiate (5:= fun _ _ s19 s20 =>
    equivalent_for_recovery txns1 
      txns2 Log.Current_Part 
      hdr1 hdr2 s19 s20).
    simpl; eauto.
 }
 {
    simpl; intros;
    repeat invert_lift2; cleanup_no_match.
    eapply BatchOperations.hash_all_finished in H30.
    eapply BatchOperations.hash_all_finished in H37.
    cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    unfold equivalent_for_recovery in *; cleanup_no_match.
    simpl in *; do 2 eexists; intuition eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
    eauto.
    do 2 eexists; split.
    eapply RepImplications.log_rep_explicit_consistent_with_upds_hashmap; eauto.
    eauto.
 }
 {
    simpl; intros;
    repeat invert_lift2; cleanup_no_match.
    eapply BatchOperations.write_consecutive_finished in H33.
    eapply BatchOperations.write_consecutive_finished in H40.
    all: try solve [rewrite seq_length; eauto].
    cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    admit.
 }
 9: {
    simpl; intros;
    repeat invert_lift2; cleanup_no_match.
    eapply Specs.update_header_finished in H38; eauto.
    eapply Specs.update_header_finished in H44; eauto.
    cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    admit.
 }
 Opaque Log.commit_txn.
Admitted.

Lemma consistent_with_upds_firstn:
forall A AEQ V l1 l2 (m: @mem A AEQ V),
consistent_with_upds m l1 l2 ->
forall n, consistent_with_upds m (firstn n l1) (firstn n l2).
Proof.
 induction l1; destruct n;
 simpl; intros; 
 destruct l2; eauto.
 simpl in *; cleanup; intuition eauto.
Qed.

Lemma ATCD_TS_Log_read_encrypted_log:
forall n u txns1 txns2 hdr1 hdr2,
Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.read_encrypted_log)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.read_encrypted_log)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
 Opaque Log.read_encrypted_log.
 unfold Termination_Sensitive, ATCD_reboot_list; destruct n; intros; repeat invert_exec.
 {
    repeat invert_lift2; cleanup.
    unfold equivalent_for_recovery in *; cleanup.
    eapply Log_TS_read_encrypted_log in H8; eauto; cleanup.

    destruct s2, s0, s2.
    eexists (RFinished _ _); repeat econstructor; eauto.
    repeat apply lift2_exec_step; eauto.

    exact ATCDLang.
    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    rewrite <- H6 at 1; clear H6.
    rewrite H27, H38.
    intuition.

    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    eapply hashes_in_hashmap_consistent_with_upds; eauto.

    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    eapply hashes_in_hashmap_consistent_with_upds; eauto.

    (** Check this. Does alld count hashes are always in hashmap? Does it have to be? **)
    admit.
 }
 {
    repeat invert_lift2; cleanup.
    unfold equivalent_for_recovery in *; cleanup.
    eapply_fresh Specs.read_encrypted_log_crashed in H8; eauto.
    cleanup.
    eapply Log_TS_read_encrypted_log_crashed in H8; eauto; cleanup.
    eapply_fresh Specs.read_encrypted_log_crashed in H8; eauto.
    cleanup.

    destruct s2, s0, s2.
    edestruct ATCD_TS_recovery.
    3: eauto.
    3: eapply equivalent_for_recovery_after_reboot.
    all: try solve [unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto].
    shelve.

    eexists (Recovered _); econstructor; eauto.
    repeat eapply lift2_exec_step_crashed; eauto.

    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    rewrite <- H6 at 1; clear H6.
    rewrite H32, H43.
    intuition.

    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    intros.
    eapply consistent_with_upds_firstn; eapply hashes_in_hashmap_consistent_with_upds; eauto.

    unfold Log.log_rep_explicit,
    Log.log_rep_inner,
    Log.header_part_is_valid  in *; logic_clean.
    intros.
    eapply consistent_with_upds_firstn; eapply hashes_in_hashmap_consistent_with_upds; eauto.

    (** Check this. Does alld count hashes are always in hashmap? Does it have to be? **)
    admit.

    intuition congruence.
 }
 Unshelve.
 all: try solve [exact ATCDLang].
 5:{
    repeat cleanup_pairs.
    instantiate (1:= hdr2).
    instantiate (1:= hdr1).
    instantiate (1:= txns2).
    instantiate (1:= txns1).
    unfold equivalent_for_recovery; simpl; eexists (_, (_, _)), (_, (_, _));
    simpl; intuition eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_subset_hashmap; eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_subset_hashmap; eauto.
 }
Admitted.



Lemma ATCD_TS_Log_decrypt_txn:
forall rec1 log1 rec2 log2 n u txns1 txns2 hdr1 hdr2,
length
(firstn (Log.addr_count rec1 + Log.data_count rec1)
   (skipn (Log.start rec1) log1)) =
length
(firstn (Log.addr_count rec2 + Log.data_count rec2)
   (skipn (Log.start rec2) log2))  -> 
Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.decrypt_txn rec1 log1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.decrypt_txn rec2 log2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
consistent_with_upds (snd (fst (snd (snd (snd s2)))))
(firstn (Log.addr_count rec2 + Log.data_count rec2)
 (skipn (Log.start rec2) log2))
(map (fun ev : value => (Log.key rec2, decrypt (Log.key rec2) ev))
 (firstn (Log.addr_count rec2 + Log.data_count rec2)
    (skipn (Log.start rec2) log2))))
(ATCD_reboot_list n).
Proof.
 Opaque Log.decrypt_txn.
 unfold Termination_Sensitive, ATCD_reboot_list; destruct n; intros; repeat invert_exec.
 {
    repeat invert_lift2; cleanup.
    unfold equivalent_for_recovery in *; cleanup.
    destruct s2, s0, s2.
    eapply Log_TS_decrypt_txn with (record2:= rec2) (log2:= log2) in H8; eauto; cleanup.

    eexists (RFinished _ _); repeat econstructor; eauto.
    repeat apply lift2_exec_step; eauto.
    exact ATCDLang.
 }
 {
    repeat invert_lift2; cleanup.
    unfold equivalent_for_recovery in *; cleanup.
    eapply_fresh Specs.decrypt_txn_crashed in H8; eauto.
    cleanup.
    eapply Log_TS_decrypt_txn_crashed in H8; eauto; cleanup.
    eapply_fresh Specs.decrypt_txn_crashed in H8; eauto.
    cleanup.

    destruct s2, s0, s2.
    edestruct ATCD_TS_recovery.
    3: eauto.
    3: eapply equivalent_for_recovery_after_reboot.
    all: try solve [unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto].
    shelve.

    eexists (Recovered _); econstructor; eauto.
    repeat eapply lift2_exec_step_crashed; eauto.
 }
 Unshelve.
 all: try solve [exact ATCDLang].
 5:{
    repeat cleanup_pairs.
    instantiate (1:= hdr2).
    instantiate (1:= hdr1).
    instantiate (1:= txns2).
    instantiate (1:= txns1).
    unfold equivalent_for_recovery; simpl; eexists (_, (_, _)), (_, (_, _));
    simpl; intuition eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
 }
Qed.

Definition apply_txn_precondition log1 log2 rec1 rec2 :=
 length
 (firstn (Log.addr_count rec1 + Log.data_count rec1)
    (skipn (Log.start rec1) log1)) =
length
 (firstn (Log.addr_count rec2 + Log.data_count rec2)
    (skipn (Log.start rec2) log2))  /\

length
 (firstn (Log.data_count rec1)
    (blocks_to_addr_list
       (firstn (Log.addr_count rec1)
          (map (decrypt (Log.key rec1))
             (firstn (Log.addr_count rec1 + Log.data_count rec1)
                (skipn (Log.start rec1) log1)))))) =
length
 (firstn (Log.data_count rec2)
    (blocks_to_addr_list
       (firstn (Log.addr_count rec2)
          (map (decrypt (Log.key rec2))
             (firstn (Log.addr_count rec2 + Log.data_count rec2)
                (skipn (Log.start rec2) log2)))))) /\
length
 (skipn (Log.addr_count rec1)
    (map (decrypt (Log.key rec1))
       (firstn (Log.addr_count rec1 + Log.data_count rec1)
          (skipn (Log.start rec1) log1)))) =
length
 (skipn (Log.addr_count rec2)
    (map (decrypt (Log.key rec2))
       (firstn (Log.addr_count rec2 + Log.data_count rec2)
          (skipn (Log.start rec2) log2)))) /\

length
  (firstn (Log.data_count rec1)
     (blocks_to_addr_list
        (firstn (Log.addr_count rec1)
           (map (decrypt (Log.key rec1))
              (firstn (Log.addr_count rec1 + Log.data_count rec1)
                 (skipn (Log.start rec1) log1)))))) =
length
  (skipn (Log.addr_count rec1)
     (map (decrypt (Log.key rec1))
        (firstn (Log.addr_count rec1 + Log.data_count rec1)
           (skipn (Log.start rec1) log1)))) /\

length
 (firstn (Log.data_count rec2)
    (blocks_to_addr_list
       (firstn (Log.addr_count rec2)
          (map (decrypt (Log.key rec2))
             (firstn (Log.addr_count rec2 + Log.data_count rec2)
                (skipn (Log.start rec2) log2)))))) =
length
 (skipn (Log.addr_count rec2)
    (map (decrypt (Log.key rec2))
       (firstn (Log.addr_count rec2 + Log.data_count rec2)
          (skipn (Log.start rec2) log2)))) /\

Forall (fun a : nat => a < disk_size)
 (firstn (Log.data_count rec2)
    (blocks_to_addr_list
       (firstn (Log.addr_count rec2)
          (map (decrypt (Log.key rec2))
             (firstn (Log.addr_count rec2 + Log.data_count rec2)
                (skipn (Log.start rec2) log2)))))).

Lemma ATCD_TS_Log_apply_txn:
forall rec1 log1 rec2 log2 n u txns1 txns2 hdr1 hdr2,
apply_txn_precondition log1 log2 rec1 rec2 ->

Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.apply_txn rec1 log1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.apply_txn rec2 log2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
consistent_with_upds (snd (fst (snd (snd (snd s2)))))
(firstn (Log.addr_count rec2 + Log.data_count rec2)
 (skipn (Log.start rec2) log2))
(map (fun ev : value => (Log.key rec2, decrypt (Log.key rec2) ev))
 (firstn (Log.addr_count rec2 + Log.data_count rec2)
    (skipn (Log.start rec2) log2))))
(ATCD_reboot_list n).
Proof.
 Transparent Log.apply_txn.
 unfold Log.apply_txn, apply_txn_precondition; simpl; intros.
 logic_clean.
 simpl; eapply ATCD_TS_compositional; 
 simpl; intros; eauto.
 
 eapply ATCD_TS_Log_decrypt_txn; eauto.
 {
    repeat invert_lift2.
    unfold equivalent_for_recovery in *; logic_clean.
    eapply Specs.decrypt_txn_finished in H14; eauto.
    eapply Specs.decrypt_txn_finished in H20; eauto.

    eapply TS_eqv_impl.
    eapply ATCD_TS_BatchOperations_write_batch; eauto.
    all: try solve [logic_clean; subst; simpl in *; eauto].
    instantiate (5:= fun _ _ s0 s3 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s0 s3).
    simpl; eauto.
 }
 {
    simpl.
    repeat invert_lift2.
    unfold equivalent_for_recovery in *; logic_clean.
    eapply Specs.decrypt_txn_finished in H14; eauto.
    eapply Specs.decrypt_txn_finished in H20; eauto.
    cleanup.
    repeat cleanup_pairs; simpl in *.
    eexists (_, (_, _)), (_, (_, _));
    simpl; intuition eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
    do 2 eexists; intuition eauto; try congruence.
    eapply RepImplications.log_rep_explicit_consistent_with_upds; eauto.
 }
Qed.


Definition record0 := Log.Build_txn_record key0 0 0 0.

Fixpoint consistent_with_upds_list {A AEQ V} (m: @mem A AEQ V) l_l_a l_l_v :=
 match l_l_a, l_l_v with
 |l_a :: l_l_a', l_v :: l_l_v' =>
    consistent_with_upds m l_a l_v /\
    consistent_with_upds_list (Mem.upd_batch m l_a l_v) l_l_a' l_l_v'
 |_, _ => True
 end.

Lemma ATCD_TS_Log_apply_txns:
forall recs1 log1 recs2 log2 n u txns1 txns2 hdr1 hdr2,
length recs1 = length recs2 ->
 Forall2 (apply_txn_precondition log1 log2) recs1 recs2 ->
Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.apply_txns recs1 log1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.apply_txns recs2 log2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
(consistent_with_upds_list (snd (fst (snd (snd (snd s2))))) 
(map (fun rec2 => (firstn (Log.addr_count rec2 + Log.data_count rec2)
(skipn (Log.start rec2) log2))) recs2)
(map (fun rec2 => (map 
(fun ev : value => (Log.key rec2, decrypt (Log.key rec2) ev))
(firstn (Log.addr_count rec2 + Log.data_count rec2)
   (skipn (Log.start rec2) log2)))) recs2)))
(ATCD_reboot_list n).
Proof.
 Transparent Log.apply_txns.
 Opaque Log.apply_txn.
 induction recs1; destruct recs2; simpl; 
 intros; try lia.
 eapply TS_eqv_impl.
 apply ATCD_TS_ret.
 intuition eauto.

 simpl; eapply ATCD_TS_compositional; 
 simpl; intros; eauto.
 2: eapply IHrecs1; eauto.
 eapply TS_eqv_impl.
 eapply ATCD_TS_Log_apply_txn.
 inversion H0; eauto.
 intuition eauto.
 inversion H0; eauto.

 repeat invert_lift2; cleanup.
 inversion H0; eauto; cleanup.
 unfold apply_txn_precondition in H13; logic_clean.
 eapply Specs.apply_txn_finished in H11; eauto.
 eapply Specs.apply_txn_finished in H17; eauto.
 cleanup; repeat cleanup_pairs.
 simpl in *; intros; intuition eauto.
 admit.
 repeat rewrite map_map; simpl.
 rewrite map_ext at 1.
 rewrite map_id; eauto.
 simpl; intros; apply decrypt_encrypt.
Admitted.

Lemma ATCD_TS_Log_flush_txns:
forall n u recs1 recs2 log1 log2 txns1 txns2 hdr1 hdr2,
length recs1 = length recs2 ->
 Forall2 (apply_txn_precondition log1 log2) recs1 recs2 ->

Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.flush_txns recs1 log1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.flush_txns recs2 log2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
(consistent_with_upds_list (snd (fst (snd (snd (snd s2))))) 
(map (fun rec2 => (firstn (Log.addr_count rec2 + Log.data_count rec2)
(skipn (Log.start rec2) log2))) recs2)
(map (fun rec2 => (map 
(fun ev : value => (Log.key rec2, decrypt (Log.key rec2) ev))
(firstn (Log.addr_count rec2 + Log.data_count rec2)
   (skipn (Log.start rec2) log2)))) recs2)))
(ATCD_reboot_list n).
Proof.
 unfold Log.flush_txns.
 intros; simpl.
 eapply ATCD_TS_compositional.
 intros; apply ATCD_TS_Log_apply_txns; eauto.
 simpl; intros.
 
 eapply ATCD_TS_compositional.
 intros; eapply ATCD_TS_Disk_sync.

 simpl; intros.
 eapply ATCD_TS_compositional.
 intros; eapply ATCD_TS_Log_update_header.
 intros; eapply ATCD_TS_Disk_sync.
 
 all: admit. (* Make lemmas *)
 Opaque Log.flush_txns.
Admitted.


Lemma ATCD_TS_Log_apply_log:
forall n u txns1 txns2 hdr1 hdr2,
Termination_Sensitive u 
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.apply_log)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.apply_log)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
 Transparent Log.apply_log.
 unfold Log.apply_log; intros.
 simpl. eapply ATCD_TS_compositional.
 intros; apply ATCD_TS_Log_read_encrypted_log.
 
 intros; cleanup; eauto.
 repeat invert_lift2; cleanup.
 unfold equivalent_for_recovery in *; logic_clean.
 eapply Specs.read_encrypted_log_finished in H7; eauto.
 eapply Specs.read_encrypted_log_finished in H13; eauto.
 simpl in *; cleanup; simpl in *.
 eapply TS_eqv_impl.
 eapply ATCD_TS_Log_flush_txns; eauto.
 shelve.
 shelve.
 shelve.
 shelve.
 Opaque Log.apply_log.
Admitted.

Lemma ATCD_TS_Log_commit:
forall n u lo s1 s2 l_a1 l_a2 l_v1 l_v2 txns1 txns2 hdr1 hdr2,
length ((addr_list_to_blocks (map (Nat.add data_start) l_a1)) ++ l_v1) = 
length ((addr_list_to_blocks (map (Nat.add data_start) l_a2)) ++ l_v2) ->
(log_length < (Log.count (Log.current_part hdr1) +
    (length (addr_list_to_blocks (map (Nat.add data_start) l_a1)) + length l_v1)) <-> 
  log_length < (Log.count (Log.current_part hdr2) +
    (length (addr_list_to_blocks (map (Nat.add data_start) l_a2)) + length l_v2))) ->
Termination_Sensitive_explicit u lo s1 s2
(@lift_L2 AuthenticationOperation _ TCDLang _
(@lift_L2 _ _ CachedDiskLang _
   (|CDDP| Log.commit (addr_list_to_blocks (map (Nat.add data_start) l_a1)) l_v1)))
(@lift_L2 AuthenticationOperation _ TCDLang _
   (@lift_L2 _ _ CachedDiskLang _
      (|CDDP| Log.commit (addr_list_to_blocks (map (Nat.add data_start) l_a2)) l_v2)))
 (Simulation.Definitions.compile
   ATCD_Refinement
   (Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |))))
(refines_valid ATCD_Refinement
(refines_valid ATC_Refinement AD_valid_state)) 
(fun s1 s2 => equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 /\
 equivalent_for_commit (seln lo 0 []) l_a1 l_v1 l_a2 l_v2 s1 s2)
(ATCD_reboot_list n).
Proof.
 Transparent Log.commit.
 unfold Log.commit; intros; simpl.
 eapply ATCD_TS_explicit_compositional.

 intros; eapply TS_explicit_to_TS.
 intros; eapply TS_eqv_impl.
 apply ATCD_TS_Log_read_header.
 intros; cleanup; eauto.

 Transparent Log.read_header.
 intros; unfold Log.read_header in *; repeat invert_exec.
 repeat cleanup_pairs; simpl in *.
 destruct_fresh (PeanoNat.Nat.ltb log_length
 (Log.count
    (Log.current_part
       (Log.decode_header (fst (s6 hdr_block_num)))) +
  (length
     (addr_list_to_blocks (map (Nat.add data_start) l_a1)) +
   length l_v1)));
 
 destruct_fresh (PeanoNat.Nat.ltb log_length
 (Log.count
    (Log.current_part
       (Log.decode_header (fst (s3 hdr_block_num)))) +
  (length
     (addr_list_to_blocks (map (Nat.add data_start) l_a2)) +
   length l_v2)));
 try eapply_fresh PeanoNat.Nat.ltb_lt in D;
 try eapply_fresh PeanoNat.Nat.ltb_lt in D0;
 try eapply_fresh PeanoNat.Nat.ltb_nlt in D;
 try eapply_fresh PeanoNat.Nat.ltb_nlt in D0;
 intuition.
 intros; eapply TS_explicit_to_TS.
 eapply TS_eqv_impl.
 apply ATCD_TS_ret.
 shelve.
 
 unfold equivalent_for_recovery, Log.log_rep_explicit,
 Log.log_header_block_rep in *; simpl in *; cleanup; lia.

 unfold equivalent_for_recovery, Log.log_rep_explicit,
 Log.log_header_block_rep in *; simpl in *; cleanup; lia.
 
 simpl.
 eapply  ATCD_TS_explicit_compositional.
 intros; eapply TS_explicit_eqv_impl.
 intros; eapply ATCD_TS_Log_commit_txn; eauto.
 
 instantiate (1:= Log.decode_header (fst (s3 hdr_block_num))); lia.
 
 simpl; eauto.
 instantiate (4:= fun _ _ s9 s10 => 
 equivalent_for_recovery txns1 
 txns2 Log.Current_Part hdr1 hdr2 s9 s10 /\
equivalent_for_commit (seln lo 0 []) l_a1 l_v1
 l_a2 l_v2 s9 s10).

 simpl; intros; simpl in *; cleanup.
 shelve.
 
 simpl; intros; eapply TS_explicit_to_TS; apply ATCD_TS_ret.
 simpl.
 simpl; intros;
 repeat invert_lift2; cleanup_no_match.
 simpl in *; cleanup_no_match.
 (*
 eapply Specs.commit_txn_finished in H15; eauto.
 eapply Specs.commit_txn_finished in H22; eauto.
 cleanup_no_match.
 repeat cleanup_pairs; simpl in *.
 *)
 shelve.

 simpl; intros; unfold Log.read_header in *; repeat invert_exec.
 repeat cleanup_pairs; simpl in *.
 eauto.

 Unshelve.
 5: simpl; intros; intuition eauto.
 Opaque Log.commit.
Admitted.
 

 Lemma Log_commit_ret_eq:
 forall u l_a1 l_v1 l_a2 l_v2 o s1 s2 s1' s2' r1 r2,
 exec CryptoDisk u o s1 (Log.commit l_a1 l_v1) (Finished s1' r1) ->

 exec CryptoDisk u o s2 (Log.commit l_a2 l_v2) (Finished s2' r2) ->
 (log_length <
 (Log.count
    (Log.current_part (Log.decode_header (fst (snd s1 hdr_block_num)))) +
  (length l_a1 + length l_v1)) <-> 
  log_length <
    (Log.count
       (Log.current_part (Log.decode_header (fst (snd s2 hdr_block_num)))) +
     (length l_a2 + length l_v2))) ->
 r1 = r2.
 Proof.
    Transparent Log.commit.
    unfold Log.commit, Log.read_header.
    intros; repeat invert_exec; eauto; 
    repeat cleanup_pairs;
    try eapply_fresh PeanoNat.Nat.ltb_lt in D;
    try eapply_fresh PeanoNat.Nat.ltb_lt in D0;
    try eapply_fresh PeanoNat.Nat.ltb_nlt in D;
    try eapply_fresh PeanoNat.Nat.ltb_nlt in D0;
    lia.
    Opaque Log.commit.
 Qed.

