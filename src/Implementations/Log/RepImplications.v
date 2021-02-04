Require Import EquivDec Framework TotalMem CryptoDiskLayer BatchOperations Log.Log.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Nested Proofs Allowed.

Lemma header_part0_valid:
  forall log_blocksets hm,
    header_part_is_valid log_blocksets hm header_part0.
Proof.
  unfold header_part_is_valid; simpl; intros; intuition eauto.
  lia.
Qed.

Lemma txns_valid_nil:
  forall log_blocks kl em s,
    txns_valid header_part0 log_blocks kl em s [].
Proof.
  unfold txns_valid; simpl; intros; intuition eauto.
Qed.



Definition to_plain_addr_list txn plain_addr_blocks :=
  let data_count := data_count txn in          

  firstn data_count (blocks_to_addr_list plain_addr_blocks).

Definition get_addr_blocks (log_blocks: list value) (txn: txn_record) :=
  let key := key txn in
  let start := start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in

  firstn addr_count txn_blocks.

Definition get_addr_list txn plain_addr_blocks :=
  firstn (data_count txn) (blocks_to_addr_list plain_addr_blocks).

Definition get_data_blocks (log_blocks: list value) (txn: txn_record) :=
  let key := key txn in
  let start := start txn in
  let addr_count := addr_count txn in
  let data_count := data_count txn in
  let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in

  skipn addr_count txn_blocks.

Definition plain_addr_blocks_valid log_blocks plain_addr_blocks txn :=
  let key := key txn in
  
  get_addr_blocks log_blocks txn = map (encrypt key) plain_addr_blocks.

Definition plain_data_blocks_valid log_blocks plain_data_blocks txn :=
  let key := key txn in
  
  get_data_blocks log_blocks txn = map (encrypt key) plain_data_blocks.


Lemma bimap_get_addr_list:
  forall txns header_part log_blocks kl em d,
    count header_part <= log_length ->
    length log_blocks = log_length ->
    Forall (txn_well_formed header_part log_blocks kl em d) txns ->
    bimap get_addr_list (map record txns) (map addr_blocks txns) = map addr_list txns.
Proof.
  induction txns; simpl; intros; eauto.
  inversion H1; cleanup.
  unfold txn_well_formed in H4; cleanup.
  unfold record_is_valid in H2; cleanup.
  unfold get_addr_list in *; simpl; eauto.
  erewrite <- map_length, H4.
  rewrite firstn_length_l; eauto.
  erewrite IHtxns; eauto.
  rewrite <- H10; eauto.
  rewrite skipn_length.
  setoid_rewrite H0; lia.
Qed.


Lemma log_rep_explicit_implies_decrypt_txns_pre:
  forall header_state log_state valid_part hdr txns hdr_blockset log_blocksets state,
    let valid_hdr_part := match valid_part with |Current_Part => current_part hdr |Old_Part => old_part hdr end in
    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets state ->
    Forall2 (plain_addr_blocks_valid (firstn (count valid_hdr_part) (map fst log_blocksets)))
            (map addr_blocks txns) (records valid_hdr_part) /\

    Forall2 (plain_data_blocks_valid (firstn (count valid_hdr_part) (map fst log_blocksets)))
            (map data_blocks txns) (records valid_hdr_part) /\
    
    Forall2 (fun (l1 : list addr) (l2 : list value) => length l1 = length l2)
            (bimap get_addr_list (records valid_hdr_part)
                   (map addr_blocks txns)) (map data_blocks txns) /\
    
    Forall (fun txn_record0 : txn_record =>
              start txn_record0 + addr_count txn_record0 + data_count txn_record0 <=
              length (firstn (count valid_hdr_part) (map fst log_blocksets))) (records valid_hdr_part).
Proof.
  intros.
  unfold log_rep_explicit, log_rep_inner,
  header_part_is_valid, txns_valid in *; logic_clean.
  subst valid_hdr_part.
  rewrite <- H6.
  repeat split.
  
  {
    unfold plain_addr_blocks_valid, get_addr_blocks.
    eapply selN_Forall2; intros.
    repeat rewrite map_length; auto.
    {
      rewrite map_length in H12.
      repeat erewrite selN_map; eauto.
      rewrite firstn_firstn, min_l by lia.
      rewrite <- skipn_firstn_comm.
      rewrite firstn_firstn, min_l.
      rewrite skipn_firstn_comm.
      eapply_fresh in_selN in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed in *; logic_clean; eauto.

      eapply_fresh in_selN in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed, record_is_valid in *; logic_clean; eauto.
      eapply Nat.le_trans.
      2: eauto.
      apply Nat.le_add_r.
    }
  }

  {
    unfold plain_data_blocks_valid, get_data_blocks.
    eapply selN_Forall2; intros.
    repeat rewrite map_length; auto.

    {
      rewrite map_length in H12.
      repeat erewrite selN_map; eauto.
      rewrite <- skipn_firstn_comm.
      rewrite firstn_firstn, min_l.
      repeat rewrite skipn_firstn_comm.
      rewrite skipn_skipn.
      eapply_fresh in_selN in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed in *; logic_clean; eauto.

      eapply_fresh in_selN in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed, record_is_valid in *; logic_clean; eauto.
      rewrite Nat.add_assoc; eauto.
    }
  }

  {
    unfold get_addr_list.
    
    eapply selN_Forall2; intros.
    rewrite bimap_length.
    repeat rewrite map_length; auto.
    rewrite min_l; eauto.

    {
      rewrite bimap_length, map_length, min_l in H12; eauto.
      rewrite bimap_combine_map.
      repeat erewrite selN_map; eauto.
      rewrite firstn_length.
      rewrite selN_combine; eauto; simpl.      
      repeat erewrite selN_map; eauto.
      
      eapply_fresh in_selN in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed in *; logic_clean; eauto.
      rewrite min_l; eauto.
      all: repeat rewrite map_length; eauto.
      rewrite combine_length, min_l; eauto.
      rewrite map_length; eauto.
      repeat rewrite map_length; eauto.
    }
  }
  {
    rewrite <- H6 in *.
    apply Forall_forall; intros.
    rewrite firstn_length_l.
    apply in_map_iff in H12; logic_clean.
    eapply Forall_forall in H7; eauto.
    unfold txn_well_formed, record_is_valid in *; logic_clean; subst; eauto.
    rewrite map_length; setoid_rewrite H2; eauto.
  }
  Unshelve.
  all: repeat econstructor; eauto.
  all: exact key0.
Qed.


Lemma record_is_valid_new_key:
  forall kl k records count,
    Forall (record_is_valid kl count) records ->
    Forall (record_is_valid (k :: kl) count) records.
Proof.
  intros; eapply Forall_impl.
  2: eauto.
  unfold record_is_valid ; simpl; intros.
  cleanup; intuition eauto.
Qed.

Lemma upd_batch_rolling_hash_list:
  forall l l' h hm,
    hashes_in_hashmap hm h l ->
    consistent_with_upds hm (rolling_hash_list h l) l' ->
    Mem.upd_batch hm (rolling_hash_list h l) l' = hm.
Proof.
  induction l; simpl; intros; eauto.
  destruct l'; simpl in *; intuition.
  rewrite IHl; eauto.
  unfold consistent in *; intuition; try congruence.
  rewrite Mem.upd_nop; eauto.
  unfold consistent in *; intuition; try congruence.
  rewrite Mem.upd_nop; eauto.
Qed.

Lemma hashes_in_hashmap_subset:
  forall l h hm hm',
    hashes_in_hashmap hm h l ->
    subset hm hm' ->
    hashes_in_hashmap hm' h l.
Proof.
  induction l; simpl; intros; cleanup; intuition eauto.
  eapply subset_some; eauto.
Qed.

Lemma header_part_is_valid_subset:
  forall a hm hm' hdr_part,
    header_part_is_valid a hm hdr_part ->
    subset hm hm' ->
    header_part_is_valid a hm' hdr_part.
Proof.
  unfold header_part_is_valid; intros; cleanup.
  intuition eauto.
  eapply hashes_in_hashmap_subset; eauto.
Qed.

Lemma txns_valid_subset:
  forall log_blocks em em' hdr_part kl d txns,    
    txns_valid hdr_part log_blocks kl em d txns ->
    subset em em' ->    
    txns_valid hdr_part log_blocks kl em' d txns.
Proof.
  unfold txns_valid; intros; cleanup.
  intuition eauto.
  eapply Forall_impl; [| eauto].
  unfold txn_well_formed; intros.
  cleanup; intuition eauto.
  specialize (H0 (encrypt (key (record a)) (selN (addr_blocks a) i value0))); cleanup; eauto.
  specialize (H0 (encrypt (key (record a)) (selN (data_blocks a) i value0))); cleanup; eauto.
Qed.

Lemma log_rep_explicit_hash_map_subset:
  forall hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s s',
    log_rep_explicit hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s ->
    subset (snd (fst (fst s))) (snd (fst (fst s'))) ->
    fst (fst (fst s')) = fst (fst (fst s)) ->
    snd (fst s') = snd (fst s) ->
    snd s' = snd s ->
    log_rep_explicit hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s'.
Proof.      
  intros; repeat cleanup_pairs; simpl in *.
  unfold log_rep_explicit in *; logic_clean; simpl in *.
  intuition eauto.
  unfold log_rep_inner in *; logic_clean; intuition eauto.  
  eapply header_part_is_valid_subset; eauto.
Qed.

Lemma log_rep_explicit_encryption_map_subset:
  forall hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s s',
    log_rep_explicit hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s ->
    subset (snd (fst s)) (snd (fst s')) ->
    fst (fst s') = fst (fst s) ->
    snd s' = snd s ->
    log_rep_explicit hdr_state log_state valid_part hdr txns hdr_blockset log_blecksets s'.
Proof.      
  intros; repeat cleanup_pairs; simpl in *.
  unfold log_rep_explicit in *; logic_clean; simpl in *.
  intuition eauto.
  unfold log_rep_inner in *; logic_clean; intuition eauto.  
  eapply txns_valid_subset; eauto.
Qed.

Lemma record_is_valid_new_count:
  forall l count n kl,
    Forall (record_is_valid kl count) l ->
    Forall (record_is_valid kl (count + n)) l.
Proof.
  induction l; simpl; intros; eauto.
  inversion H; subst.
  constructor; eauto.
  unfold record_is_valid in *; intuition.
Qed.


Lemma log_rep_sync_preserves:
  forall txns s,
    log_rep txns s ->
    log_rep txns (fst s, sync (snd s)).
Proof.
  unfold log_rep, log_rep_general, log_rep_explicit;
  simpl; intros; cleanup.
  do 3 eexists; split; eauto.
  split.
  {
    unfold sync, log_header_block_rep in *; cleanup.
    simpl; split; cleanup.
    simpl; eauto.
    simpl ;eauto.
  }
  split.
  {
    unfold log_data_blocks_rep in *; cleanup.
    simpl; repeat split; intros; cleanup.
    unfold sync.
    rewrite <- e; simpl; eauto.
    destruct (snd s (log_start + i)) eqn:D.
    setoid_rewrite D; simpl.
    rewrite e in D; eauto.
    eapply in_selN in H; eauto.
    apply e0 in H.
    rewrite D in H; simpl in *; cleanup; eauto.
    all: try lia.
    eauto.
  }
  unfold log_header_block_rep in *; cleanup; simpl; intuition eauto.  
Qed.

Lemma log_rep_update_disk_preserves:
  forall txns hdr n m s s',
    log_header_rep hdr txns s ->
    fst s' = fst s ->
    snd s' =
    upd_batch_set
      (list_upd_batch_set (snd s)
                          (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                          (firstn n (map data_blocks txns)))
      (firstn m (selN (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
      (firstn m (selN (map data_blocks txns) n [])) ->
    log_rep txns s'.
Proof.
  
  unfold log_rep, log_header_rep, log_rep_general, log_rep_explicit in *; intros; cleanup.
  do 3 eexists; intuition eauto.
  {
    unfold log_header_block_rep in *; cleanup; intuition eauto.
    eapply equal_f in H1.
    rewrite H1.
    rewrite upd_batch_set_ne, list_upd_batch_set_not_in; eauto.
    {
      intros.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H8 in *.
      erewrite bimap_get_addr_list in H; [ | | | eauto]; eauto.
      apply in_firstn_in in H.
      apply in_map_iff in H; cleanup.
      eapply Forall_forall in H9; eauto.
      unfold txn_well_formed in H9; cleanup.
      intuition.
      eapply Forall_forall in H14; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.      
      rewrite map_length; eauto.
    }
    {
      intuition.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H8 in *.
      erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
      apply in_firstn_in in H.

      destruct (lt_dec n (length txns)).        
      erewrite selN_map in H; eauto.
      eapply Forall_forall in H9; eauto.
      2: eapply in_selN; eauto.
      unfold txn_well_formed in H9; logic_clean.
      eapply Forall_forall in H14; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.
      rewrite selN_oob in H.
      intuition.
      rewrite map_length; lia.
      rewrite map_length; eauto.
    }
  }
  {
    unfold log_data_blocks_rep in *; cleanup; intuition.
    eapply equal_f in H1.
    rewrite H1.
    rewrite upd_batch_set_ne.
    rewrite list_upd_batch_set_not_in; eauto.
    {
      intros.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H11 in *.
      erewrite bimap_get_addr_list in H10.
      4: eauto.
      apply in_firstn_in in H10.
      apply in_map_iff in H10; cleanup.
      eapply Forall_forall in H12; eauto.
      unfold txn_well_formed in H12; cleanup.
      intuition.
      eapply Forall_forall in H17; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.
      apply H5.
      rewrite map_length; eauto.
    }
    {
      intuition.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H11 in *.
      erewrite bimap_get_addr_list in H10.
      apply in_firstn_in in H10.

      destruct (lt_dec n (length txns)).        
      erewrite selN_map in H10; eauto.
      eapply Forall_forall in H12; eauto.
      2: eapply in_selN; eauto.
      unfold txn_well_formed in H12; logic_clean.
      eapply Forall_forall in H17; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.
      rewrite selN_oob in H10.
      intuition.
      rewrite map_length; lia.
      apply H5.
      rewrite map_length; eauto.
      unfold header_part_is_valid in *; cleanup; eauto.
    }        
  }
  {
    unfold log_rep_inner in *; cleanup; intuition eauto.
    setoid_rewrite H0; eauto.
    {
      unfold txns_valid in *; simpl in *; logic_clean; intuition eauto.
      eapply Forall_impl; [| eauto].
      setoid_rewrite H0.
      setoid_rewrite H1.
      unfold txn_well_formed; simpl; intuition.
    }
  }
  Unshelve.
  all: repeat econstructor.
  all: exact key0.
Qed.

Lemma log_rep_update_disk_subset:
  forall txns hdr n m s s',
    log_header_rep hdr txns s ->
    fst (fst s') = fst (fst s) ->
    subset (snd (fst s)) (snd (fst s')) ->
    snd s' =
    upd_batch_set
      (list_upd_batch_set (snd s)
                          (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                          (firstn n (map data_blocks txns)))
      (firstn m (selN (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
      (firstn m (selN (map data_blocks txns) n [])) ->
    log_rep txns s'.
Proof.
  intros.
  unfold log_header_rep, log_rep_general in *; cleanup.
  eapply log_rep_update_disk_preserves.
  instantiate (1:= (fst s', snd s)).
  all: eauto.
  
  eapply log_rep_explicit_encryption_map_subset in H.
  instantiate (1:= (fst s', snd s)) in H.
  unfold log_header_rep, log_rep_general; eauto.
  all: simpl; eauto.
Qed.
 

Lemma crash_rep_header_write_to_reboot_rep :
  forall s old_txns new_txns selector,
    log_crash_rep (During_Commit_Header_Write old_txns new_txns) s ->
    
    non_colliding_selector selector s ->
    
    log_reboot_rep old_txns (fst s, select_total_mem selector (snd s)) \/
    log_reboot_rep new_txns (fst s, select_total_mem selector (snd s)).
Proof. 
  unfold non_colliding_selector, log_crash_rep, log_header_rep,
  log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.

  unfold log_header_block_rep in *; cleanup.
  simpl in *.
  cleanup.
  
  destruct (Nat.eq_dec (selector hdr_block_num) 1).
  {(** Selector rolled back to old header **)
    left.
    eexists ?[hdr].
    exists Current_Part.
    exists (select_for_addr selector hdr_block_num (x0,[x]), nil).
    exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).
    simpl; intuition eauto.
    {
      unfold select_total_mem, select_for_addr; simpl; cleanup.
      destruct_fresh (hdr_block_num =? hdr_block_num); simpl; intuition eauto.      
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      {
        match goal with
        | [H: _ < length (map _ _) |- _] =>
          rewrite map_length in H
        end.
        erewrite selN_map; eauto.
        
        match goal with
        | [H: _ < length (select_list_shifted _ _ _) |- _] =>
          rewrite select_list_shifted_length in H
        end.
        
        match goal with
        | [H: forall _, _ -> snd _ (_ + _) = selN _ _ _ |- _] =>
          rewrite H
        end.   
        erewrite select_list_shifted_selN; eauto.
        all: repeat constructor; eauto.
        match goal with
        | [H: length _ = log_length |- _] =>
          setoid_rewrite <- H
        end; eauto.
      }
      {        
        match goal with
        | [H: In _ (map _ _) |- _] =>
          apply in_map_iff in H
        end; cleanup_no_match; eauto.
      }
      {
        rewrite map_length, select_list_shifted_length; eauto.
        match goal with
        | [H: length _ = log_length |- _] =>
          setoid_rewrite <- H
        end; eauto.
      }
    }
    { 
      rewrite map_length, select_list_shifted_length; eauto.
    }
    {
      unfold select_for_addr.
      cleanup; simpl; eauto.          
      match goal with
      | [H: current_part _ = old_part _ |- _] =>
        rewrite H
      end; eauto.
    }
    {
      unfold log_rep_inner in *; simpl in *.
      unfold select_for_addr.
      cleanup; simpl; eauto.
    }
    {      
      unfold log_rep_inner in *; simpl in *.
      rewrite map_map, map_id; simpl.
      unfold select_for_addr; cleanup; simpl.
      
      intuition eauto.
      {
        match goal with
        | [H: current_part _ = old_part _ |- _] =>
          rewrite H
        end.
        unfold header_part_is_valid in *; logic_clean; intuition eauto.
        rewrite select_list_shifted_app.
        rewrite firstn_app_l; eauto.
        rewrite select_list_shifted_synced; eauto.
        match goal with
        | [H: hash (old_part _) = _ |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        eauto.
        rewrite select_list_shifted_length; eauto.

        rewrite select_list_shifted_app.
        rewrite firstn_app_l; eauto.
        rewrite select_list_shifted_synced; eauto.
        match goal with
        | [H: hashes_in_hashmap _ _ (firstn (count (old_part _)) _) |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        rewrite select_list_shifted_length; eauto.            
      }
      {
        match goal with
        | [H: current_part _ = old_part _ |- _] =>
          rewrite H
        end.
        clear H9 H12.
        unfold txns_valid in *; cleanup; intuition eauto.
        eapply Forall_impl; [|eauto].
        
        unfold txn_well_formed, record_is_valid; simpl; intros; cleanup; intuition eauto.
        {
          rewrite select_list_shifted_app, map_app.
          repeat rewrite <- skipn_firstn_comm.
          repeat rewrite firstn_app_l.
          rewrite select_list_shifted_synced; eauto.

          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          eapply Nat.le_trans.
          2: eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          lia.
        }
        
        {
          rewrite select_list_shifted_app, map_app.
          repeat rewrite <- skipn_firstn_comm.
          repeat rewrite firstn_app_l.
          rewrite select_list_shifted_synced; eauto.
          
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          eapply Nat.le_trans.
          2: eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          lia.
        }
      }
    }
    { congruence. }
  }
  { (** Selected the new header **)
    destruct (hash_dec (hash (current_part (decode_header x0)))
                       (rolling_hash hash0
                                     (firstn (count (current_part (decode_header x0)))
                                             (select_list_shifted log_start selector (x1++x2))))).
    
    {(** Selector selected all the new blocks. What a miracle! **)
      assert (A: firstn (count (current_part (decode_header x0)))
                        (select_list_shifted log_start selector (x1 ++ x2)) =
                 firstn (count (current_part (decode_header x0))) (map fst (x1 ++ x2))). {
        
        unfold log_rep_inner, header_part_is_valid in H9; simpl in *; logic_clean.
        rewrite H9 in e.
        rewrite firstn_map_comm in e.
        apply H0 in e.
        rewrite <- firstn_map_comm in e; eauto.
        repeat rewrite firstn_length_l; eauto.
        rewrite select_list_shifted_length.
        setoid_rewrite H4; eauto.
        setoid_rewrite H4; eauto.
        rewrite firstn_length_l; eauto.
        setoid_rewrite H4; eauto.

        {
          rewrite firstn_length_l; eauto.
          intros.
          unfold log_data_blocks_rep in H3; logic_clean.
          rewrite H3.
          repeat erewrite selN_selNopt; eauto.
          rewrite selN_firstn; eauto.
          lia.
          setoid_rewrite H4.
          eauto.
        }
        {
          rewrite firstn_length_l; eauto.
          intros.
          unfold select_total_mem.
          unfold log_data_blocks_rep in H3; logic_clean.
          rewrite H3.
          repeat erewrite selN_selNopt; eauto.
          erewrite selN_map.
          rewrite selN_firstn; eauto.
          erewrite select_list_shifted_selN; eauto.
          setoid_rewrite H4; lia.
          repeat rewrite firstn_length_l; eauto.
          rewrite select_list_shifted_length.
          setoid_rewrite H4; eauto. 
          lia.
          rewrite select_list_shifted_length.
          setoid_rewrite H4; eauto.
        }
      }
      
      rewrite A in *.
      right.
      eexists ?[hdr].
      exists Current_Part.
      exists (select_for_addr selector hdr_block_num (x0,[x]), nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).

      rewrite select_for_addr_not_1_latest in *; eauto.
      
      simpl; intuition eauto.
      {
        unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
        unfold select_total_mem; simpl.
        setoid_rewrite H1; eauto.
        rewrite select_for_addr_not_1_latest in *; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.             
        intuition eauto.
        {
          rewrite map_length in H15.
          erewrite selN_map; eauto.
          rewrite select_list_shifted_length in H15.
          rewrite H3.    
          erewrite select_list_shifted_selN; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H4; eauto.
        }
        {
          apply in_map_iff in H15; cleanup_no_match; eauto.
        }
        {
          rewrite map_length, select_list_shifted_length; eauto.
          setoid_rewrite <- H4; eauto.
        }
      }
      {
        rewrite map_length, select_list_shifted_length; eauto.
      }
      {
        rewrite map_map, map_id.
        unfold log_rep_inner in *; simpl in *.
        intuition.
        
        {
          unfold header_part_is_valid in *;
          rewrite A; logic_clean; intuition eauto.
        }
        
        {
          clear H9 H13.
          unfold txns_valid in *; logic_clean; intuition eauto.
          eapply Forall_impl; [|eauto].
          
          unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean; intuition eauto.
          {
            repeat rewrite <- skipn_firstn_comm.
            replace (start (record a) + addr_count (record a)) with
                (min (start (record a) + addr_count (record a))
                     (count (current_part (decode_header x0)))) by lia.
            rewrite <- firstn_firstn, A.
            rewrite firstn_firstn, min_l by lia.
            rewrite skipn_firstn_comm; eauto.
          }
          
          {
            repeat rewrite <- skipn_firstn_comm.
            replace (addr_count (record a) + start (record a) + data_count (record a)) with
                (min (addr_count (record a) + start (record a) + data_count (record a))
                     (count (current_part (decode_header x0)))) by lia.
            rewrite <- firstn_firstn, A.
            rewrite firstn_firstn, min_l by lia.
            rewrite skipn_firstn_comm; eauto.
          }
        }
      }
      { congruence. }
    }
    {(** Selector rolled back to old header **)
      left.
      eexists ?[hdr].
      exists Old_Part.
      exists (select_for_addr selector hdr_block_num (x0,[x]), nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).
      repeat rewrite select_for_addr_not_1_latest; eauto.
      simpl; intuition eauto.
      {
        unfold select_total_mem; simpl; cleanup.
        rewrite select_for_addr_not_1_latest; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
        intuition eauto.
        {
          rewrite map_length in H15.
          erewrite selN_map; eauto.
          rewrite select_list_shifted_length in H15.
          rewrite H3.    
          erewrite select_list_shifted_selN; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H4; eauto.
        }
        {
          apply in_map_iff in H15; cleanup_no_match; eauto.
        }
        {
          rewrite map_length, select_list_shifted_length; eauto.
          rewrite <- H4; eauto.
        }
      }
      { 
        rewrite map_length, select_list_shifted_length; eauto.
      }
      
      {      
        unfold log_rep_inner in *; simpl in *.
        rewrite map_map, map_id; simpl.
        
        intuition eauto.
        {
          unfold header_part_is_valid in *; logic_clean; intuition eauto.
          rewrite select_list_shifted_app.
          rewrite firstn_app_l; eauto.
          rewrite select_list_shifted_synced; eauto.
          rewrite map_app, firstn_app_l in H9; eauto.
          rewrite map_length; eauto.
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          
          rewrite select_list_shifted_app.
          rewrite firstn_app_l; eauto.
          rewrite select_list_shifted_synced; eauto.
          rewrite map_app, firstn_app_l in H10; eauto.
          rewrite map_length; eauto.
          unfold log_data_blocks_rep in *; logic_clean; eauto.
          rewrite select_list_shifted_length; eauto.
        }


        {
          clear H11 H12.
          unfold txns_valid in *; logic_clean; intuition eauto.
          eapply Forall_impl; [|eauto].
          
          unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean; intuition eauto.              
          {
            rewrite H13.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            lia.
            
            rewrite map_length;
            eapply Nat.le_trans.
            2: eauto.
            lia.
          }
          
          {
            rewrite H14.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            lia.
            rewrite map_length;
            eapply Nat.le_trans.
            2: eauto.
            lia.
          }
        }
      }
      {
        rewrite map_map, map_id in *; eauto.
      }
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.


Lemma crash_rep_log_write_to_reboot_rep :
  forall s txns selector,
    log_crash_rep (During_Commit_Log_Write txns) s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)).
Proof. 
  unfold log_crash_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  
  cleanup.
  { (** new txns **)
    eexists ?[hdr].
    exists Current_Part.
    exists x.
    exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x0 ++ x1))).
    simpl; intuition eauto.
    {
      unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
      unfold select_total_mem; simpl.
      repeat rewrite select_for_addr_synced; simpl; eauto.
      destruct_fresh (snd s hdr_block_num); simpl in *; cleanup; simpl in *;
      subst; eauto.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      
      intuition eauto.
      {
        match goal with
        | [H: _ < length (map _ _) |- _] =>
          rewrite map_length in H
        end.
        erewrite selN_map; eauto.
        
        match goal with
        | [H: _ < length (select_list_shifted _ _ _) |- _] =>
          rewrite select_list_shifted_length in H
        end.
        
        match goal with
        | [H: forall _, _ -> snd _ (_ + _) = selN _ _ _ |- _] =>
          rewrite H
        end.   
        erewrite select_list_shifted_selN; eauto.
        all: repeat constructor; eauto.
        all: try exact value0.
        match goal with
        | [H: length _ = log_length |- _] =>
          setoid_rewrite <- H
        end; eauto.
      }
      {        
        match goal with
        | [H: In _ (map _ _) |- _] =>
          apply in_map_iff in H
        end; cleanup_no_match; eauto.
      }
      {
        rewrite map_length, select_list_shifted_length; eauto.
        match goal with
        | [H: length _ = log_length |- _] =>
          setoid_rewrite <- H
        end; eauto.
      }
    }
    {
      rewrite map_length, select_list_shifted_length; eauto.
    }
    {      
      unfold log_rep_inner in *; simpl in *.
      repeat rewrite select_for_addr_synced; eauto; simpl.
      rewrite map_map, map_id; simpl.
      unfold log_data_blocks_rep in *; cleanup.
      intuition.
      {
        unfold header_part_is_valid in *; logic_clean.
        rewrite select_list_shifted_app.
        rewrite firstn_app_l; eauto.
        rewrite select_list_shifted_synced; eauto.
        intuition eauto.
        match goal with
        | [H: hash (current_part _) = _ |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        match goal with
        | [H: hashes_in_hashmap _ _ (firstn (count (current_part _)) _) |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        rewrite select_list_shifted_length; eauto.
      }
      {
        unfold txns_valid in *; cleanup; intuition eauto.
        eapply Forall_impl; [|eauto].
        unfold txn_well_formed, record_is_valid; simpl; intros; cleanup; intuition eauto.
        {
          rewrite select_list_shifted_app, map_app.
          repeat rewrite <- skipn_firstn_comm.
          repeat rewrite firstn_app_l.
          rewrite select_list_shifted_synced; eauto.
          
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          eapply Nat.le_trans.
          2: eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          lia.
        }
        
        {
          rewrite select_list_shifted_app, map_app.
          repeat rewrite <- skipn_firstn_comm.
          repeat rewrite firstn_app_l.
          rewrite select_list_shifted_synced; eauto.
          
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          eapply Nat.le_trans.
          2: eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          lia.
        }
      }
    }
    { congruence. }
  }
  Unshelve.
  all: repeat econstructor; eauto.
  all: exact value0.
Qed.


Lemma crash_rep_apply_to_reboot_rep :
  forall s txns selector,
    log_crash_rep (During_Apply txns) s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)) \/
    log_reboot_rep [] (fst s, select_total_mem selector (snd s)).
Proof. 
   unfold non_colliding_selector, log_crash_rep, log_header_rep,
  log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.

  unfold log_header_block_rep in *; cleanup.
  simpl in *.
  cleanup.
  
  destruct (Nat.eq_dec (selector hdr_block_num) 1).
  {(** Selector rolled back to old header **)
    left.
    eexists ?[hdr].
    exists Current_Part.
    exists (x0, nil).
    exists (map (fun v => (v, nil)) (select_list_shifted log_start selector x1)).
    simpl.    
    repeat rewrite select_list_shifted_synced; simpl; eauto.
    rewrite map_map; simpl.
    repeat rewrite map_noop.
    simpl; intuition eauto.
    {
      unfold select_total_mem, select_for_addr; simpl; cleanup; simpl; eauto.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      {
        rewrite H0; eauto.
        rewrite select_for_addr_synced.
        rewrite <- H5 in H10.
        eapply in_selN in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (selN x1 i (value0,[])).        
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_selN; lia.
      }
    }
    {
      rewrite H; eauto.
    }
    { congruence. }
    {
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intros.
      apply H4 in H10; destruct a; simpl in *; cleanup; eauto.
    }
    {
      unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *; eauto.
    }
  }
  { (** Selected the new header **)
    right.
    eexists ?[hdr].
    exists Current_Part.
    exists (select_for_addr selector hdr_block_num (x,[x0]), nil).
    exists (x1).
    simpl.
    rewrite select_for_addr_not_1_latest in *; eauto.
    simpl; intuition eauto.
    {
      unfold select_total_mem; simpl; cleanup; simpl; eauto.
      erewrite select_for_addr_not_1_latest; eauto.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      {
        rewrite H0; eauto.
        rewrite select_for_addr_synced.
        rewrite <- H5 in H10.
        eapply in_selN in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (selN x1 i (value0,[])).
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_selN; lia.
      }
    } 
    { congruence. }
  }
Qed.



Lemma reboot_rep_to_reboot_rep_updated :
  forall s txns selector,
    log_reboot_rep [] (fst s, select_total_mem selector (snd s)) ->
    log_reboot_rep [] (fst s, select_total_mem selector (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns))).
Proof. 
  unfold log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  do 4 eexists; intuition eauto.
  {
    unfold log_header_block_rep in *; simpl in *; cleanup.
    (** Doable **)
    admit.
  }
  {
    unfold log_data_blocks_rep in *; simpl in *; cleanup.
    intuition eauto.
    (** Doable **)
    admit.
  }
Admitted.


Lemma crash_rep_recover_to_reboot_rep :
  forall s txns selector,
    log_crash_rep (During_Recovery txns) s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)).
Proof. 
   unfold non_colliding_selector, log_crash_rep, log_header_rep,
  log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
   
  unfold log_header_block_rep in *; cleanup.
  simpl in *.
  cleanup.
  
  destruct (Nat.eq_dec (selector hdr_block_num) 1).
  {(** Selector rolled back to old header **)
    split_ors; cleanup.
    {(** Current_Part of old header **)
      eexists ?[hdr].
      exists Current_Part.
      exists (x, nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector x1)).
      simpl.    
      repeat rewrite select_list_shifted_synced; simpl; eauto.
      rewrite map_map; simpl.
      repeat rewrite map_noop.
      simpl; intuition eauto.
      {
        unfold select_total_mem, select_for_addr; simpl; cleanup; simpl; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
        intuition eauto.
        {
          rewrite H0; eauto.
          rewrite select_for_addr_synced.
          rewrite <- H1 in H10.
          eapply in_selN in H10.
          apply H8 in H10.
          instantiate (1:= (value0, nil)) in H10.
          destruct_fresh (selN x1 i (value0,[])).
          simpl in *; subst; eauto.
          eapply H8.
          eapply in_selN; lia.
        }
      }
      {
        congruence.
      }
      {
        unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.
        intros.
        apply H8 in H10; destruct a; simpl in *; cleanup; eauto.
      }
      {
        unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *; eauto.
      }
    }
    {(** Old_Part of old header **)
      eexists ?[hdr].
      exists Old_Part.
      exists (x, nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector x1)).
      simpl.    
      repeat rewrite select_list_shifted_synced; simpl; eauto.
      rewrite map_map; simpl.
      repeat rewrite map_noop.
      simpl; intuition eauto.
      {
        unfold select_total_mem, select_for_addr; simpl; cleanup; simpl; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
        intuition eauto.
        {
          rewrite H0; eauto.
          rewrite select_for_addr_synced.
          rewrite <- H1 in H11.
          eapply in_selN in H11.
          apply H9 in H11.
          instantiate (1:= (value0, nil)) in H11.
          destruct_fresh (selN x1 i (value0,[])).
          simpl in *; subst; eauto.
          eapply H9.
          eapply in_selN; lia.
        }
      }
      {
        unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.
        intros.
        apply H9 in H11; destruct a; simpl in *; cleanup; eauto.
      }
      {
        unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *; eauto.
      }
    }
  }
  { (** Selected the new header **)
    clear H7.
    eexists ?[hdr].
    exists Current_Part.
    exists (select_for_addr selector hdr_block_num (x0,[x]), nil).
    exists (x1).
    simpl.
    rewrite select_for_addr_not_1_latest in *; eauto.
    simpl; intuition eauto.
    {
      unfold select_total_mem; simpl; cleanup; simpl; eauto.
      rewrite select_for_addr_not_1_latest in *; eauto.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      {
        rewrite H0; eauto.
        rewrite select_for_addr_synced.
        rewrite <- H1 in H9.
        eapply in_selN in H9.
        apply H7 in H9.
        instantiate (1:= (value0, nil)) in H9.
        destruct_fresh (selN x1 i (value0,[])).
        simpl in *; subst; eauto.
        eapply H7.
        eapply in_selN; lia.
      }
    }
    { congruence. }
  }
Qed.


Lemma log_rep_to_reboot_rep :
  forall s txns selector,
    log_rep txns s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)).
Proof. 
  unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  
  cleanup.
  { (** new txns **)
    eexists ?[hdr].
    exists Current_Part.
    exists x0.
    exists x1.
    simpl; intuition eauto.
    {
      unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
      unfold select_total_mem; simpl.
      repeat rewrite select_for_addr_synced; simpl; eauto.
      destruct_fresh (snd s hdr_block_num); simpl in *;
      cleanup; simpl in *; eauto.
      subst; eauto.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      
      intuition eauto.
      { 
        match goal with
        | [H: forall _, _ -> snd _ _ = selN _ _ _ |- _] =>
          rewrite H
        end.   
        rewrite select_for_addr_synced.
        all: repeat constructor; eauto.
        all: try exact value0.
        rewrite <- H2 in H7.
        eapply in_selN in H7.
        apply H1 in H7.
        instantiate (1:= (value0, [])) in H7.
        destruct_fresh (selN x1 i (value0, [])).
        simpl in *; subst; eauto.
        eapply H1.
        eapply in_selN; lia.       
      }
    }
    { congruence. }
  }
Qed.

Lemma log_rep_to_reboot_rep_same :
  forall s txns,
    log_rep txns s ->
    log_reboot_rep txns s.
Proof. 
  unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  
  cleanup.
  
  eexists ?[hdr].
  exists Current_Part.
  exists x0.
  exists x1.
  simpl; intuition eauto; congruence.
Qed.

Lemma reboot_rep_to_reboot_rep :
  forall s txns selector,
    log_reboot_rep txns s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)).
Proof. 
   unfold non_colliding_selector, log_crash_rep, log_header_rep,
  log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
   
  unfold log_header_block_rep in *; cleanup.
  simpl in *.
  cleanup.
  { (** new txns **)
    eexists ?[hdr].
    exists x0.
    eexists.
    exists x2.
    simpl; intuition eauto.
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      
      intuition eauto.
      { 
        match goal with
        | [H: forall _, _ -> snd _ _ = selN _ _ _ |- _] =>
          rewrite H
        end.   
        rewrite select_for_addr_synced.
        all: repeat constructor; eauto.
        all: try exact value0.
        rewrite <- H3 in H8.
        eapply in_selN in H8.
        apply H2 in H8.
        instantiate (1:= (value0, [])) in H8.
        destruct_fresh (selN x2 i (value0, [])).
        simpl in *; subst; eauto.
        eapply H2.
        eapply in_selN; lia.        
      }
    }
    all: simpl in *; try rewrite select_for_addr_synced in *; eauto.
  }
Qed.
