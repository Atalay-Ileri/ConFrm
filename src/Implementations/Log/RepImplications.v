Require Import EquivDec Framework TotalMem CryptoDiskLayer BatchOperations Log.Log.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Nested Proofs Allowed.


Lemma select_total_mem_upd_set_ne:
    forall (A : Type) (AEQ : EqDec A) (V : Type) (a : A)
    (v : V) selector m a',
    a <> a' ->
    select_total_mem selector (upd_set m a v) a' =
    select_total_mem selector m a'.
    Proof.
      unfold select_total_mem, 
      select_for_addr, upd_set; simpl; intros.
      destruct (AEQ a' a); try congruence.
    Qed.  

    Lemma select_total_mem_upd_batch_set_not_in:
    forall (A : Type) (AEQ : EqDec A) (V : Type) (l_a : list A)
    (l_v : list V) selector (m : @total_mem A AEQ (V * list V)) a,
    ~In a l_a -> 
    select_total_mem selector (upd_batch_set m l_a l_v) a =
    select_total_mem selector m a.
    Proof.
      induction l_a; simpl; intros; eauto.
      destruct l_v; simpl in *; cleanup; eauto.
      erewrite IHl_a; intuition.
      rewrite select_total_mem_upd_set_ne; eauto.
    Qed.

    Lemma select_total_mem_list_upd_batch_set_not_in:
    forall (A : Type) (AEQ : EqDec A) (V : Type) (l_l_a : list (list A))
    (l_l_v : list (list V)) selector m a,
    Forall (fun l_a => ~In a l_a) l_l_a ->
    select_total_mem selector (list_upd_batch_set m l_l_a l_l_v) a =
    select_total_mem selector m a.
    Proof.
      induction l_l_a; simpl; intros; eauto.
      destruct l_l_v; simpl in *; cleanup; eauto.
      inversion H; cleanup; rewrite IHl_l_a; eauto.
    rewrite select_total_mem_upd_batch_set_not_in; eauto.
    Qed.


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
    eapply seln_Forall2; intros.
    repeat rewrite map_length; auto.
    {
      rewrite map_length in H12.
      repeat erewrite seln_map; eauto.
      rewrite firstn_firstn, min_l by lia.
      rewrite <- skipn_firstn_comm.
      rewrite firstn_firstn, min_l.
      rewrite skipn_firstn_comm.
      eapply_fresh in_seln in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed in *; logic_clean; eauto.

      eapply_fresh in_seln in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed, record_is_valid in *; logic_clean; eauto.
      eapply Nat.le_trans.
      2: eauto.
      apply Nat.le_add_r.
    }
  }

  {
    unfold plain_data_blocks_valid, get_data_blocks.
    eapply seln_Forall2; intros.
    repeat rewrite map_length; auto.

    {
      rewrite map_length in H12.
      repeat erewrite seln_map; eauto.
      rewrite <- skipn_firstn_comm.
      rewrite firstn_firstn, min_l.
      repeat rewrite skipn_firstn_comm.
      rewrite skipn_skipn.
      eapply_fresh in_seln in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed in *; logic_clean; eauto.

      eapply_fresh in_seln in H12.
      eapply Forall_forall in H7; eauto.
      unfold txn_well_formed, record_is_valid in *; logic_clean; eauto.
      rewrite Nat.add_assoc; eauto.
    }
  }

  {
    unfold get_addr_list.
    
    eapply seln_Forall2; intros.
    rewrite bimap_length.
    repeat rewrite map_length; auto.
    rewrite min_l; eauto.

    {
      rewrite bimap_length, map_length, min_l in H12; eauto.
      rewrite bimap_combine_map.
      repeat erewrite seln_map; eauto.
      rewrite firstn_length.
      rewrite seln_combine; eauto; simpl.      
      repeat erewrite seln_map; eauto.
      
      eapply_fresh in_seln in H12.
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
  specialize (H0 (encrypt (key (record a)) (seln (addr_blocks a) i value0))); cleanup; eauto.
  specialize (H0 (encrypt (key (record a)) (seln (data_blocks a) i value0))); cleanup; eauto.
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
    eapply in_seln in H; eauto.
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
      (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
      (firstn m (seln (map data_blocks txns) n [])) ->
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
      erewrite seln_map in H; eauto.
      eapply Forall_forall in H9; eauto.
      2: eapply in_seln; eauto.
      unfold txn_well_formed in H9; logic_clean.
      eapply Forall_forall in H14; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.
      rewrite seln_oob in H.
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
      erewrite seln_map in H10; eauto.
      eapply Forall_forall in H12; eauto.
      2: eapply in_seln; eauto.
      unfold txn_well_formed in H12; logic_clean.
      eapply Forall_forall in H17; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.
      rewrite seln_oob in H10.
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
      (firstn m (seln (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
      (firstn m (seln (map data_blocks txns) n [])) ->
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
 

Lemma crash_rep_header_write_to_reboot_rep' :
  forall s old_txns new_txns selector new_hdr old_hdr,
    log_crash_rep (During_Commit_Header_Write 
    old_txns new_txns) s ->
    
    non_colliding_selector selector s ->
    (snd s) hdr_block_num =
      (Log.encode_header new_hdr,
      [Log.encode_header old_hdr]) ->
      new_hdr <> old_hdr ->
    (log_reboot_rep_explicit_part old_hdr old_txns 
    Current_Part (fst s, select_total_mem selector (snd s)) /\ 
    selector hdr_block_num = 1) \/
    (log_reboot_rep_explicit_part new_hdr old_txns 
    Old_Part (fst s, select_total_mem selector (snd s)) /\ 
    selector hdr_block_num <> 1 /\
    (exists i, i < count (current_part new_hdr) /\
    i >= count (current_part old_hdr) /\
    fst ((select_total_mem selector (snd s)) (log_start + i)) <> 
    fst ((snd s) (log_start + i)))) \/
    (log_reboot_rep_explicit_part new_hdr new_txns 
    Current_Part (fst s, select_total_mem selector (snd s)) /\ 
    selector hdr_block_num <> 1 /\
    (forall i, i < count (current_part new_hdr)  ->
    i >= count (current_part old_hdr) -> 
    fst ((select_total_mem selector (snd s)) (log_start + i)) = 
    fst ((snd s) (log_start + i)))).
Proof. 
  unfold non_colliding_selector, log_crash_rep, log_header_rep,
  log_reboot_rep_explicit_part, log_rep_general, log_rep_explicit; intros; cleanup.

  unfold log_header_block_rep in *; cleanup.
  simpl in *.
  cleanup.
  
  destruct (Nat.eq_dec (selector hdr_block_num) 1).
  {(** Selector rolled back to old header **)
    left.
    split; eauto.
    exists (select_for_addr selector hdr_block_num (encode_header new_hdr, [encode_header old_hdr]), nil).
    exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).
    simpl; intuition eauto.
    {
      unfold select_total_mem, select_for_addr; simpl; cleanup.
      rewrite encode_decode_header; eauto.
      (* destruct_fresh (hdr_block_num =? hdr_block_num); simpl; intuition eauto. *)     
    }
    {
      unfold select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
    }
    {    
      repeat rewrite encode_decode_header in *; eauto.         

      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      {
        match goal with
        | [H: _ < length (map _ _) |- _] =>
          rewrite map_length in H
        end.
        erewrite seln_map; eauto.
        
        match goal with
        | [H: _ < length (select_list_shifted _ _ _) |- _] =>
          rewrite select_list_shifted_length in H
        end.
        
        match goal with
        | [H: forall _, _ -> snd _ (_ + _) = seln _ _ _ |- _] =>
          rewrite H
        end.   
        erewrite select_list_shifted_seln; eauto.
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
      repeat rewrite encode_decode_header in *; eauto.         
      match goal with
      | [H: current_part _ = old_part _ |- _] =>
        rewrite H
      end; eauto.
    }
    {
      unfold log_rep_inner in *; simpl in *.
      unfold select_for_addr.
      repeat rewrite encode_decode_header in *; eauto.      
    }
    {      
      unfold log_rep_inner in *; simpl in *.
      rewrite map_map, map_id; simpl.
      unfold select_for_addr; cleanup; simpl.
      repeat rewrite encode_decode_header in *; eauto.         

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
        unfold log_data_blocks_rep in *; cleanup; eauto.
        eauto.
        rewrite select_list_shifted_length; eauto.
        setoid_rewrite H14; eauto.

        rewrite select_list_shifted_app.
        rewrite firstn_app_l; eauto.
        rewrite select_list_shifted_synced; eauto.
        match goal with
        | [H: hashes_in_hashmap _ _ (firstn (count (old_part _)) _) |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        rewrite select_list_shifted_length; eauto.
        setoid_rewrite H14; eauto.            
      }
      {
        match goal with
        | [H: current_part _ = old_part _ |- _] =>
          rewrite H
        end.
        clear H11 H15.
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
          setoid_rewrite H14; eauto.
          eapply Nat.le_trans.
          2: eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          setoid_rewrite H14; eauto.
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
          setoid_rewrite H14; eauto.
          lia.
          rewrite map_length;
          eapply Nat.le_trans.
          2: eauto.
          setoid_rewrite H14; eauto.
          lia.
        }
      }
    }
    { congruence. }
  }
  {
    repeat rewrite encode_decode_header in *; eauto.         
    (** Selected the new header **)
    destruct (hash_dec (hash (current_part new_hdr))
                       (rolling_hash hash0
                                     (firstn (count (current_part new_hdr))
                                             (select_list_shifted log_start selector (x1++x2))))).
    
    {(** Selector selected all the new blocks. What a miracle! **)
      assert (A: firstn (count (current_part new_hdr))
                        (select_list_shifted log_start selector (x1 ++ x2)) =
                 firstn (count (current_part new_hdr)) (map fst (x1 ++ x2))). {
        
        unfold log_rep_inner, header_part_is_valid in H11; simpl in *; logic_clean.
        rewrite H1 in e.
        rewrite firstn_map_comm in e.
        apply H0 in e.
        rewrite <- firstn_map_comm in e; eauto.
        repeat rewrite firstn_length_l; eauto.
        rewrite select_list_shifted_length.
        setoid_rewrite H6; eauto.
        setoid_rewrite H6; eauto.
        rewrite firstn_length_l; eauto.
        setoid_rewrite H6; eauto.

        {
          rewrite firstn_length_l; eauto.
          intros.
          unfold log_data_blocks_rep in H5; logic_clean.
          rewrite H5.
          repeat erewrite seln_nth_error; eauto.
          rewrite seln_firstn; eauto.
          lia.
          setoid_rewrite H6.
          eauto.
        }
        {
          rewrite firstn_length_l; eauto.
          intros.
          unfold select_total_mem.
          unfold log_data_blocks_rep in H5; logic_clean.
          rewrite H5.
          repeat erewrite seln_nth_error; eauto.
          erewrite seln_map.
          rewrite seln_firstn; eauto.
          erewrite select_list_shifted_seln; eauto.
          setoid_rewrite H6; lia.
          repeat rewrite firstn_length_l; eauto.
          rewrite select_list_shifted_length.
          setoid_rewrite H6; eauto. 
          lia.
          rewrite select_list_shifted_length.
          setoid_rewrite H6; eauto.
        }
      }
      
      rewrite A in *.
      right; right.
      split; eauto.
      exists (select_for_addr selector hdr_block_num (encode_header new_hdr,
      [encode_header old_hdr]), nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).

      rewrite select_for_addr_not_1_latest in *; eauto.
        
      
      simpl; repeat rewrite encode_decode_header in *; eauto; 
      intuition eauto.
      {
        unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
        unfold select_total_mem; simpl.
        setoid_rewrite H3; eauto.
        rewrite select_for_addr_not_1_latest in *; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.             
        intuition eauto.
        {
          rewrite map_length in H8.
          erewrite seln_map; eauto.
          rewrite select_list_shifted_length in H8.
          rewrite H1.    
          erewrite select_list_shifted_seln; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H6; eauto.
        }
        {
          apply in_map_iff in H8; cleanup_no_match; eauto.
        }
        {
          rewrite map_length, select_list_shifted_length; eauto.
          setoid_rewrite <- H6; eauto.
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
          clear H9 H16.
          unfold txns_valid in *; logic_clean; intuition eauto.
          eapply Forall_impl; [|eauto].
          
          unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean; intuition eauto.
          {
            repeat rewrite <- skipn_firstn_comm.
            replace (start (record a) + addr_count (record a)) with
                (min (start (record a) + addr_count (record a))
                     (count (current_part new_hdr))) by lia.
            rewrite <- firstn_firstn, A.
            rewrite firstn_firstn, min_l by lia.
            rewrite skipn_firstn_comm; eauto.
          }
          
          {
            repeat rewrite <- skipn_firstn_comm.
            replace (addr_count (record a) + start (record a) + data_count (record a)) with
                (min (addr_count (record a) + start (record a) + data_count (record a))
                     (count (current_part new_hdr))) by lia.
            rewrite <- firstn_firstn, A.
            rewrite firstn_firstn, min_l by lia.
            rewrite skipn_firstn_comm; eauto.
          }
        }
      }
      { congruence. }
      {
       split; eauto.
       intros.
       unfold log_data_blocks_rep in *; cleanup.
       rewrite H5; eauto.
       setoid_rewrite <- seln_map at 2.
       setoid_rewrite <- seln_firstn at 3; eauto.
       rewrite <- A.
       rewrite seln_firstn; eauto.
       erewrite select_list_shifted_seln; eauto.
       setoid_rewrite H6.
       lia.
       setoid_rewrite H6.
       lia.
       lia.
      }
    }
    {(** Selector rolled back to old header **)
      right; left.
      split; eauto.
      exists (select_for_addr selector hdr_block_num (encode_header new_hdr,
      [encode_header old_hdr]), nil).
      exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).
      repeat rewrite select_for_addr_not_1_latest; eauto.
      simpl; repeat rewrite encode_decode_header in *; eauto;
      intuition eauto.
      {
        unfold select_total_mem; simpl; cleanup.
        rewrite select_for_addr_not_1_latest; eauto.
      }
      {    
        unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
        intuition eauto.
        {
          rewrite map_length in H8.
          erewrite seln_map; eauto.
          rewrite select_list_shifted_length in H8.
          rewrite H1.    
          erewrite select_list_shifted_seln; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H6; eauto.
        }
        {
          apply in_map_iff in H8; cleanup_no_match; eauto.
        }
        {
          rewrite map_length, select_list_shifted_length; eauto.
          rewrite <- H6; eauto.
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
          rewrite map_app, firstn_app_l in H11; eauto.
          rewrite map_length; eauto.
          setoid_rewrite H14; eauto.
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          setoid_rewrite H14; eauto.
          
          rewrite select_list_shifted_app.
          rewrite firstn_app_l; eauto.
          rewrite select_list_shifted_synced; eauto.
          rewrite map_app, firstn_app_l in H12; eauto.
          rewrite map_length; eauto.
          setoid_rewrite H14; eauto.
          unfold log_data_blocks_rep in *; logic_clean; eauto.
          rewrite select_list_shifted_length; eauto.
          setoid_rewrite H14; eauto.
        }


        {
          clear H13 H15.
          unfold txns_valid in *; logic_clean; intuition eauto.
          eapply Forall_impl; [|eauto].
          
          unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean; intuition eauto.              
          {
            rewrite H16.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            setoid_rewrite H14; eauto.
            lia.
            
            rewrite map_length;
            eapply Nat.le_trans.
            2: eauto.
            setoid_rewrite H14; eauto.
            lia.
          }
          
          {
            rewrite H17.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            setoid_rewrite H14; eauto.
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
      {
        split; eauto.
        assert (A: (firstn (count (current_part new_hdr))
        (select_list_shifted log_start selector (x1 ++ x2))) <>
        (firstn (count (current_part new_hdr)) (map fst (x1 ++ x2)))). {
          intros Hnot.
          apply n0.
          rewrite Hnot.
          unfold log_rep_inner, header_part_is_valid in H11; cleanup; eauto.
        }
        Lemma seln_length_eq_ne_exists:
        forall T (TEQ: EqDec T) (l1 l2: list T) def,
        length l1 = length l2 ->
        l1 <> l2 ->
        exists i, i < length l1 /\
        seln l1 i def <> seln l2 i def /\
        (forall j, j < i -> seln l1 j def = seln l2 j def).
        Proof.
          induction l1; destruct l2; simpl in *; 
          intros; eauto; try lia; try congruence.
          destruct (TEQ a t); subst.
          assert (l1 <> l2).
          intros Hnot; congruence.
          eapply IHl1 in H1; try lia.
          cleanup.
          exists (S x); intuition eauto.
          lia.
          destruct j; eauto.
          eapply H3. lia.
          exists 0; simpl; intuition eauto.
          lia.
          lia.
        Qed.
        eapply seln_length_eq_ne_exists in A; eauto.
        rewrite firstn_length_l in A.
        cleanup.
        do 2 rewrite seln_firstn in H15.
        erewrite seln_map, select_list_shifted_seln in H15.
        unfold log_data_blocks_rep in *; cleanup.
        destruct (lt_dec x (count (old_part new_hdr))).
        {
          exfalso; apply H15.
          repeat rewrite seln_app.
          rewrite select_for_addr_synced; eauto.
          eapply e1.
          apply in_seln.
          all: lia.
        }
        exists x; intuition eauto.
        lia.
        erewrite e in H4; eauto.
        lia.
        all: try setoid_rewrite H6; try lia.
        rewrite select_list_shifted_length.
        try setoid_rewrite H6; try lia.
        apply value_dec.
        repeat rewrite firstn_length_l; eauto.
        rewrite map_length.
        setoid_rewrite H6; try lia.
        rewrite select_list_shifted_length.
        setoid_rewrite H6; try lia.
      }
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
  all: exact value0.
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
        erewrite seln_map; eauto.
        
        match goal with
        | [H: _ < length (select_list_shifted _ _ _) |- _] =>
          rewrite select_list_shifted_length in H
        end.
        
        match goal with
        | [H: forall _, _ -> snd _ (_ + _) = seln _ _ _ |- _] =>
          rewrite H
        end.   
        erewrite select_list_shifted_seln; eauto.
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
        unfold log_data_blocks_rep in *; cleanup; eauto.
        eauto.
        
        rewrite select_list_shifted_length; eauto.
        setoid_rewrite H12; eauto.

        rewrite select_list_shifted_app.
        rewrite firstn_app_l; eauto.
        rewrite select_list_shifted_synced; eauto.
        match goal with
        | [H: hashes_in_hashmap _ _ (firstn (count (old_part _)) _) |- _] =>
          rewrite map_app, firstn_app_l in H
        end; eauto.
        rewrite map_length; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        unfold log_data_blocks_rep in *; cleanup; eauto.
        rewrite select_list_shifted_length; eauto.
        setoid_rewrite H12; eauto.        
      }
      {
        match goal with
        | [H: current_part _ = old_part _ |- _] =>
          rewrite H
        end.
        unfold txns_valid in *; cleanup; intuition eauto.
        eapply Forall_impl; [|eauto].
        
        unfold txn_well_formed, record_is_valid; simpl; intros; cleanup; intuition eauto.
        {
          rewrite select_list_shifted_app, map_app.
          repeat rewrite <- skipn_firstn_comm.
          repeat rewrite firstn_app_l.
          rewrite select_list_shifted_synced; eauto.
          unfold log_data_blocks_rep in *; cleanup; eauto.

          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          eapply Nat.le_trans.
          2: eauto.
          setoid_rewrite H12.
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
          setoid_rewrite H12.
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
          repeat erewrite seln_nth_error; eauto.
          rewrite seln_firstn; eauto.
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
          repeat erewrite seln_nth_error; eauto.
          erewrite seln_map.
          rewrite seln_firstn; eauto.
          erewrite select_list_shifted_seln; eauto.
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
          rewrite map_length in H6.
          erewrite seln_map; eauto.
          rewrite select_list_shifted_length in H6.
          rewrite H3.    
          erewrite select_list_shifted_seln; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H4; eauto.
        }
        {
          apply in_map_iff in H6; cleanup_no_match; eauto.
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
          rewrite map_length in H6.
          erewrite seln_map; eauto.
          rewrite select_list_shifted_length in H6.
          rewrite H3.    
          erewrite select_list_shifted_seln; eauto.
          all: repeat constructor; eauto.
          setoid_rewrite <- H4; eauto.
        }
        {
          apply in_map_iff in H6; cleanup_no_match; eauto.
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
          unfold log_data_blocks_rep in *; cleanup; eauto.
          rewrite select_list_shifted_length; eauto.
          setoid_rewrite H12; eauto.

          rewrite select_list_shifted_app.
          rewrite firstn_app_l; eauto.
          rewrite select_list_shifted_synced; eauto.
          rewrite map_app, firstn_app_l in H10; eauto.
          rewrite map_length; eauto.
          setoid_rewrite H12; eauto.
          unfold log_data_blocks_rep in *; logic_clean; eauto.
          rewrite select_list_shifted_length; eauto.
          setoid_rewrite H12; eauto.
        }


        {
          unfold txns_valid in *; logic_clean; intuition eauto.
          eapply Forall_impl; [|eauto].
          
          unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean; intuition eauto.              
          {
            rewrite H18.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            setoid_rewrite H12.
            lia.
            
            rewrite map_length;
            eapply Nat.le_trans.
            2: eauto.
            lia.
          }
          
          {
            rewrite H19.
            rewrite select_list_shifted_app, map_app.
            repeat rewrite <- skipn_firstn_comm.
            repeat rewrite firstn_app_l.
            rewrite select_list_shifted_synced; eauto.
            
            unfold log_data_blocks_rep in *; logic_clean; eauto.
            rewrite select_list_shifted_length; eauto.
            eapply Nat.le_trans.
            2: eauto.
            setoid_rewrite H12.
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
        erewrite seln_map; eauto.
        
        match goal with
        | [H: _ < length (select_list_shifted _ _ _) |- _] =>
          rewrite select_list_shifted_length in H
        end.
        
        match goal with
        | [H: forall _, _ -> snd _ (_ + _) = seln _ _ _ |- _] =>
          rewrite H
        end.   
        erewrite select_list_shifted_seln; eauto.
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
        eapply in_seln in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (seln x1 i (value0,[])).        
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_seln; lia.
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
        eapply in_seln in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (seln x1 i (value0,[])).
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_seln; lia.
      }
    } 
    { congruence. }
  }
Qed.

(*
Lemma crash_rep_apply_to_reboot_rep_2 :
  forall s txns selector,
    log_crash_rep (During_Apply txns) s ->
    log_reboot_rep txns (fst s, select_total_mem selector (snd s)) \/
    log_reboot_rep [] (fst s, select_total_mem selector (list_upd_batch_set (snd s) (map Log.addr_list txns)
    (map data_blocks txns))).
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
        eapply in_seln in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (seln x1 i (value0,[])).        
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_seln; lia.
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
      rewrite list_upd_batch_set_not_in.
      rewrite H3.
      erewrite select_for_addr_not_1_latest; eauto.
      unfold not; intros.
      apply in_map_iff in H0; cleanup.
      unfold log_rep_explicit, log_rep_inner,
      txns_valid in *; logic_clean.
      eapply Forall_forall in H11; eauto.
      unfold txn_well_formed in H11; logic_clean; eauto.
      eapply Forall_forall in H18; eauto.
      pose proof hdr_before_log.
      pose proof data_start_where_log_ends; cleanup;
      lia.
    }
    {    
      unfold log_data_blocks_rep, select_total_mem in *; cleanup_no_match; simpl in *.
      intuition eauto.
      rewrite list_upd_batch_set_not_in.
      {
        rewrite H0; eauto.
        rewrite select_for_addr_synced.
        rewrite <- H5 in H10.
        eapply in_seln in H10.
        apply H4 in H10.
        instantiate (1:= (value0, nil)) in H10.
        destruct_fresh (seln x1 i (value0,[])).
        simpl in *; subst; eauto.
        eapply H4.
        eapply in_seln; lia.
      }
      {
        unfold not; intros.
      apply in_map_iff in H11; cleanup.
      unfold log_rep_explicit, log_rep_inner,
      txns_valid in *; logic_clean.
      eapply Forall_forall in H14; eauto.
      unfold txn_well_formed in H11; logic_clean; eauto.
      eapply Forall_forall in H18; eauto.
      pose proof hdr_before_log.
      pose proof data_start_where_log_ends; cleanup;
      lia.
      }
    } 
    { congruence. }
  }
Qed.
*)

Lemma reboot_rep_to_reboot_rep_updated :
  forall s txns selector,
    Forall (Forall (fun a => a >= data_start)) (map addr_list txns) ->
    log_reboot_rep [] (fst s, select_total_mem selector (snd s)) ->
    log_reboot_rep [] (fst s, select_total_mem selector (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns))).
Proof. 
  unfold log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  do 4 eexists; intuition eauto.
  {
    unfold log_header_block_rep in *; simpl in *; cleanup.
    split; eauto.
    eapply select_total_mem_list_upd_batch_set_not_in; eauto.
    apply Forall_forall; intros.
    eapply Forall_forall in H; eauto.
    intros Hx; eapply Forall_forall in H; eauto.
    pose proof data_start_where_log_ends;
    pose proof hdr_before_log; lia.
  }
  {
    unfold log_data_blocks_rep in *; simpl in *; cleanup.
    intuition eauto.
    erewrite select_total_mem_list_upd_batch_set_not_in; eauto.
    apply Forall_forall; intros.
    eapply Forall_forall in H; eauto.
    intros Hx; eapply Forall_forall in H; eauto.
    pose proof data_start_where_log_ends; lia.
  }
Qed.


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
          eapply in_seln in H10.
          apply H8 in H10.
          instantiate (1:= (value0, nil)) in H10.
          destruct_fresh (seln x1 i (value0,[])).
          simpl in *; subst; eauto.
          eapply H8.
          eapply in_seln; lia.
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
          eapply in_seln in H11.
          apply H9 in H11.
          instantiate (1:= (value0, nil)) in H11.
          destruct_fresh (seln x1 i (value0,[])).
          simpl in *; subst; eauto.
          eapply H9.
          eapply in_seln; lia.
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
        eapply in_seln in H9.
        apply H7 in H9.
        instantiate (1:= (value0, nil)) in H9.
        destruct_fresh (seln x1 i (value0,[])).
        simpl in *; subst; eauto.
        eapply H7.
        eapply in_seln; lia.
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
        | [H: forall _, _ -> snd _ _ = seln _ _ _ |- _] =>
          rewrite H
        end.   
        rewrite select_for_addr_synced.
        all: repeat constructor; eauto.
        all: try exact value0.
        rewrite <- H2 in H7.
        eapply in_seln in H7.
        apply H1 in H7.
        instantiate (1:= (value0, [])) in H7.
        destruct_fresh (seln x1 i (value0, [])).
        simpl in *; subst; eauto.
        eapply H1.
        eapply in_seln; lia.       
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
        | [H: forall _, _ -> snd _ _ = seln _ _ _ |- _] =>
          rewrite H
        end.   
        rewrite select_for_addr_synced.
        all: repeat constructor; eauto.
        all: try exact value0.
        rewrite <- H3 in H8.
        eapply in_seln in H8.
        apply H2 in H8.
        instantiate (1:= (value0, [])) in H8.
        destruct_fresh (seln x2 i (value0, [])).
        simpl in *; subst; eauto.
        eapply H2.
        eapply in_seln; lia.        
      }
    }
    all: simpl in *; try rewrite select_for_addr_synced in *; eauto.
  }
Qed.


Lemma log_rep_explicit_after_reboot :
  forall s txns selector hdr hbs lbs,
    log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs s ->
    log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs (fst s, select_total_mem selector (snd s)).
Proof. 
  unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  
  cleanup.
  { (** new txns **)
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
        | [H: forall _, _ -> snd _ _ = seln _ _ _ |- _] =>
          rewrite H
        end.   
        rewrite select_for_addr_synced.
        all: repeat constructor; eauto.
        all: try exact value0.
        rewrite <- H2 in H7.
        eapply in_seln in H7.
        apply H1 in H7.
        instantiate (1:= (value0, [])) in H7.
        destruct_fresh (seln lbs i (value0, [])).
        simpl in *; subst; eauto.
        eapply H1.
        eapply in_seln; lia.       
      }
    }
  }
Qed.

Lemma log_rep_explicit_consistent_with_upds:
     
forall s1 s2 s3 txns hdr hbs lbs l1 l2,
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs  (s1, s2, s3) ->
  consistent_with_upds s2 l1 l2 ->
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs (s1, Mem.upd_batch s2 l1 l2, s3).
Proof. 
unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner; intros; cleanup.
cleanup.
simpl in *; intuition eauto.
eapply txns_valid_subset; eauto.
apply upd_batch_consistent_subset; eauto.
Qed.

Lemma log_rep_explicit_consistent_with_upds_hashmap:
     
forall s1 s2 s3 s4 txns hdr hbs lbs l1 l2,
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs  (s1, s2, s3, s4) ->
  consistent_with_upds s2 l1 l2 ->
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs (s1, Mem.upd_batch s2 l1 l2, s3, s4).
Proof. 
unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner; intros; cleanup.
cleanup.
simpl in *; intuition eauto.
eapply header_part_is_valid_subset; eauto.
apply upd_batch_consistent_subset; eauto.
Qed.

Lemma log_rep_explicit_subset_hashmap:
     
forall s1 s2 s2' s3 s4 txns hdr hbs lbs,
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs  (s1, s2, s3, s4) ->
  subset s2 s2' ->
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs (s1, s2', s3, s4).
Proof. 
unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner; intros; cleanup.
cleanup.
simpl in *; intuition eauto.
eapply header_part_is_valid_subset; eauto.
Qed.

Lemma log_rep_explicit_new_key:
forall s1 s2 s3 s4 k txns hdr hbs lbs,
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs  (s1, s2, s3, s4) ->
  ~In k s1 ->
  Log.log_rep_explicit Log.Hdr_Synced Log.Synced Current_Part hdr txns hbs lbs (k::s1, s2, s3, s4).
Proof. 
unfold log_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner; intros; cleanup.
cleanup.
simpl in *; intuition eauto.
unfold txns_valid in *; cleanup; intuition eauto.
eapply Forall_forall; intros.
eapply Forall_forall in H7; eauto.
unfold txn_well_formed in *; cleanup; 
intuition eauto.
unfold record_is_valid in *; cleanup; intuition eauto.
simpl; intuition.
Qed.