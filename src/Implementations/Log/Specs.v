Require Import EquivDec Framework TotalMem CryptoDiskLayer BatchOperations.
Require Import Log.Log Log.RepImplications.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Nested Proofs Allowed.
(** Specs **)

Theorem update_header_finished:
  forall header_part vs s' s o t,
    (snd s) hdr_block_num = vs ->
    exec CryptoDiskLang o s (update_header header_part) (Finished s' t) ->
    fst s' = fst s /\
    snd s' = upd (snd s) hdr_block_num (encode_header (update_hdr (decode_header (fst vs)) header_part), fst vs :: snd vs).
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  cleanup; eauto.
Qed.

Theorem update_header_crashed:
  forall header_part s' s o,
    exec CryptoDiskLang o s (update_header header_part) (Crashed s') ->
    s' = s.
Proof.
  unfold update_header, write_header, read_header; simpl; intros.
  repeat invert_exec; simpl in *; repeat cleanup.
  repeat (split_ors; repeat invert_exec; simpl in *;
          cleanup; simpl in *);
  repeat invert_exec;
  solve [ destruct s; simpl in *; eauto].
Qed.

Theorem decrypt_txn_finished:
  forall txn log_blocks plain_blocks t s' s o,
    let key := key txn in
    let start := start txn in
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
  repeat rewrite map_map, map_noop; eauto.
  intros; apply encrypt_decrypt.
Qed.


Theorem decrypt_txn_crashed:
  forall txn log_blocks s' s o,
    exec CryptoDiskLang o s (decrypt_txn txn log_blocks) (Crashed s') ->
    s' = s.
Proof.
  unfold decrypt_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  split_ors; cleanup; repeat invert_exec.
  eapply decrypt_all_crashed in H; eauto.
  eapply decrypt_all_finished in H; cleanup; eauto.
Qed.


Theorem apply_txn_finished:
  forall txn log_blocks plain_blocks t s' s o,
    let key := key txn in
    let start := start txn in
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
  unfold apply_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.
  eapply decrypt_txn_finished in H1; eauto; cleanup; simpl in *.
  
  eapply write_batch_finished in H2; eauto; cleanup.
  intuition eauto; cleanup.
Qed.

Theorem apply_txn_crashed:
  forall txn log_blocks plain_blocks s' s o,
    let key := key txn in
    let start := start txn in
    let addr_count := addr_count txn in
    let data_count := data_count txn in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let addr_blocks := firstn addr_count plain_blocks in
    let data_blocks := skipn addr_count plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list addr_blocks) in
    txn_blocks = map (encrypt key) plain_blocks ->
    length addr_list = length data_blocks ->
    exec CryptoDiskLang o s (apply_txn txn log_blocks) (Crashed s') ->
    fst s' = fst s /\ exists n, snd s' = upd_batch_set (snd s) (firstn n addr_list) (firstn n data_blocks).
Proof.
  unfold apply_txn; simpl; intros;
  repeat invert_exec; simpl in *;
  cleanup.

  split_ors; cleanup.
  apply decrypt_txn_crashed in H1; eauto; cleanup.
  split; eauto.
  exists 0; simpl; eauto.

  eapply decrypt_txn_finished in H1; eauto; cleanup; simpl in *.
  eapply write_batch_crashed in H2; eauto; cleanup.
  intuition eauto; cleanup.
Qed.

Theorem apply_txns_finished:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t,
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txns ->
    
    exec CryptoDiskLang o s (apply_txns txns log_blocks) (Finished s' t) ->
    fst s' = fst s /\
    snd s' = list_upd_batch_set (snd s) l_addr_list l_plain_data_blocks.
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  
  assume (Al: (length l = addr_count a)).

  eapply apply_txn_finished in H3; cleanup; eauto.
  edestruct IHtxns in H4; eauto; cleanup.
  simpl in *; intuition eauto.
  
  unfold get_addr_list at 1; simpl.

  2:{
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
  }
  
  rewrite <- Al in H7.
  setoid_rewrite H7.  
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  Unshelve.
  unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
  erewrite <- map_length, <- H8.
  rewrite firstn_length_l; eauto.
  rewrite firstn_length_l; try lia.
  rewrite skipn_length; try lia.
Qed.


Theorem apply_txns_crashed:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s',
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txns ->
    
    exec CryptoDiskLang o s (apply_txns txns log_blocks) (Crashed s') ->
    fst s' = fst s /\
    exists n m, snd s' = upd_batch_set (list_upd_batch_set (snd s) (firstn n l_addr_list) (firstn n l_plain_data_blocks)) (firstn m (selN l_addr_list n [])) (firstn m (selN l_plain_data_blocks n [])).
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.

  {
    intuition eauto.
    exists 0, 0; simpl; eauto.
  }
  
  assume (Al: (length l = addr_count a)).
  split_ors; cleanup; repeat invert_exec.
  {
    eapply apply_txn_crashed in H3; eauto; cleanup.
    intuition eauto.
    exists 0 , x0; simpl.
    unfold plain_addr_blocks_valid, get_addr_blocks,
    plain_data_blocks_valid, get_data_blocks, get_addr_list in *; cleanup; eauto.

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
    rewrite <- Al in H4.
    setoid_rewrite H4.  
    rewrite skipn_app.
    rewrite firstn_app2; eauto.

    rewrite <- Al. 
    rewrite skipn_app.
    rewrite firstn_app2; eauto.
  }
  {
    eapply apply_txn_finished in H3; cleanup; eauto.
    edestruct IHtxns in H4; eauto; cleanup.
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
    exists (S x), x4; simpl.
    rewrite <- Al in H8.
    setoid_rewrite H8.  
    rewrite skipn_app.
    rewrite firstn_app2; eauto.
    
    rewrite <- Al. 
    rewrite skipn_app.
    rewrite firstn_app2; eauto.
  }
  

  Unshelve.
  unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
  erewrite <- map_length, <- H7.
  rewrite firstn_length_l; eauto.
  rewrite firstn_length_l; try lia.
  rewrite skipn_length; try lia.
Qed.

Global Opaque apply_txns.


Theorem decrypt_txns_finished:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s' t,
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txns ->
    
    exec CryptoDiskLang o s (decrypt_txns txns log_blocks) (Finished s' t) ->
    t = combine l_addr_list l_plain_data_blocks /\
    s' = s.
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.
  
  assume (Al: (length l = addr_count a)).

  eapply decrypt_txn_finished in H3; cleanup; eauto.
  edestruct IHtxns in H4; eauto; cleanup.
  simpl in *; intuition eauto.
  unfold get_addr_list at 1; simpl.

  2:{
    unfold plain_addr_blocks_valid, plain_data_blocks_valid,
    get_addr_blocks, get_data_blocks in *; simpl in *.
    rewrite firstn_sum_split.
    rewrite firstn_firstn in H8;
    rewrite min_l in H8 by lia.
    rewrite H8.
    rewrite skipn_firstn_comm in H14.
    rewrite H14, <- map_app; eauto.
  }
  
  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  rewrite <- Al. 
  rewrite skipn_app.
  rewrite firstn_app2; eauto.

  Unshelve.
  unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
  erewrite <- map_length, <- H8.
  rewrite firstn_length_l; eauto.
  rewrite firstn_length_l; try lia.
  rewrite skipn_length; try lia.
Qed.

Theorem decrypt_txns_crashed:
  forall txns log_blocks l_plain_addr_blocks l_plain_data_blocks o s s',
    let l_addr_list := bimap get_addr_list txns l_plain_addr_blocks in
    
    Forall2 (plain_addr_blocks_valid log_blocks) l_plain_addr_blocks txns ->
    Forall2 (plain_data_blocks_valid log_blocks) l_plain_data_blocks txns ->
    Forall2 (fun l1 l2 => length l1 = length l2) l_addr_list l_plain_data_blocks ->
    Forall (fun txn_record => start txn_record + addr_count txn_record + data_count txn_record <= length log_blocks) txns ->
    exec CryptoDiskLang o s (decrypt_txns txns log_blocks) (Crashed s') ->
    s' = s.
Proof.
  induction txns; simpl; intros;
  repeat invert_exec; cleanup; eauto;
  inversion H; inversion H0;
  inversion H1; inversion H2; cleanup.

  repeat (split_ors; cleanup; repeat invert_exec); eauto.
  eapply decrypt_txn_crashed in H3; eauto.

  {
    assume (Al: (length l = addr_count a)).    
    eapply decrypt_txn_finished in H3; cleanup; eauto.
    instantiate (1:= l ++ x2).

    {
      unfold plain_addr_blocks_valid, plain_data_blocks_valid,
      get_addr_blocks, get_data_blocks in *; simpl in *.
      rewrite firstn_sum_split.
      rewrite firstn_firstn in H7;
      rewrite min_l in H7 by lia.
      rewrite H7.
      rewrite skipn_firstn_comm in H13.
      rewrite H13, <- map_app; eauto.
    }
    
    {
      rewrite <- Al. 
      rewrite skipn_app.
      rewrite firstn_app2; eauto.
    }
  }

  {
    eapply decrypt_txns_finished in H4; eauto; cleanup; eauto.
    assume (Al: (length l = addr_count a)).    
    eapply decrypt_txn_finished in H3; cleanup; eauto.
    instantiate (1:= l ++ x2).

    {
      unfold plain_addr_blocks_valid, plain_data_blocks_valid,
      get_addr_blocks, get_data_blocks in *; simpl in *.
      rewrite firstn_sum_split.
      rewrite firstn_firstn in H7;
      rewrite min_l in H7 by lia.
      rewrite H7.
      rewrite skipn_firstn_comm in H13.
      rewrite H13, <- map_app; eauto.
    }
    
    {
      rewrite <- Al. 
      rewrite skipn_app.
      rewrite firstn_app2; eauto.
    }
  }

  Unshelve.
  {
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H7.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }
  {
    unfold plain_addr_blocks_valid, get_addr_blocks in *; simpl in *.
    erewrite <- map_length, <- H7.
    rewrite firstn_length_l; eauto.
    rewrite firstn_length_l; try lia.
    rewrite skipn_length; try lia.
  }
Qed.



Theorem read_encrypted_log_finished :
  forall o s txns hdr r s' header_state log_state valid_part hdr_blockset log_blocksets,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang o s read_encrypted_log (Finished s' r) ->
    r =  (valid_header_part, valid_log_blocks) /\
    fst (fst s') = fst (fst s) /\
    snd s' = snd s /\
    subset (snd (fst s)) (snd (fst s')).
Proof.
  unfold read_encrypted_log, read_header, check_hash.
  intros; destruct valid_part.
  {(** Current part **)
    invert_exec.
    invert_exec'' H1.    
    invert_exec'' H8.
    invert_exec'' H11.
    invert_exec'' H7.
    invert_exec'' H8.
    invert_exec.
    eapply read_consecutive_finished in H1; cleanup.
    assert (x3 = firstn (count (current_part hdr)) (map fst log_blocksets)).
    {
      eapply list_selN_ext.
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
      rewrite selN_firstn; eauto.
      erewrite selN_map.
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
      apply hash_all_finished in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep in *; cleanup_no_match.
      intuition eauto.
      eapply upd_batch_consistent_subset; eauto.
      
    }
    {
      apply hash_all_finished in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; cleanup_no_match.
      exfalso; apply n.
      setoid_rewrite H14.
      rewrite <- H18; eauto.
    }
  }

  {(** Old Part **)
    invert_exec.
    invert_exec'' H1.    
    invert_exec'' H8.
    invert_exec'' H11.
    invert_exec'' H7.
    invert_exec'' H8.
    invert_exec.
    eapply read_consecutive_finished in H1; cleanup.
    assert (x3 = firstn (count (current_part hdr)) (map fst log_blocksets)).
    {
      eapply list_selN_ext.
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
      rewrite selN_firstn; eauto.
      erewrite selN_map.
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
      apply hash_all_finished in H2; cleanup.
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; cleanup_no_match.
      exfalso; apply H0; eauto.      
    }
    {       
      apply hash_all_finished in H2; cleanup.
      apply read_consecutive_finished in H4; cleanup.
      assert (x5= firstn (count (old_part hdr)) (map fst log_blocksets)).
      {
        eapply list_selN_ext.
        rewrite firstn_length_l; eauto.
        unfold log_rep_explicit, log_header_block_rep in *;
        cleanup_no_match; eauto.
        rewrite map_length;
        unfold log_rep_explicit, log_header_block_rep,
        log_rep_inner, header_part_is_valid in *;
        cleanup_no_match; eauto.      
        setoid_rewrite H12; lia.
        intros.
        edestruct H4.
        rewrite <- H2; eauto.
        cleanup_no_match.
        rewrite <- H12.
        rewrite selN_firstn; eauto.
        erewrite selN_map.
        unfold log_rep_explicit, log_data_blocks_rep in *;
        cleanup_no_match; eauto.
        destruct s; simpl in *.
        erewrite e1 in H12.
        rewrite <- H12; eauto.
        all: unfold log_rep_explicit, log_header_block_rep,
             log_rep_inner,
             header_part_is_valid in *; simpl in *; cleanup_no_match;
        try setoid_rewrite H14; try lia.
      }
      unfold log_rep_explicit, log_header_block_rep,
      log_rep_inner, header_part_is_valid in *; simpl in *; cleanup_no_match.
      intuition eauto.
      eapply upd_batch_consistent_subset; eauto.
    }
  }
  Unshelve.
  all: eauto.
Qed.

Theorem read_encrypted_log_crashed :
  forall o s txns hdr s' header_state log_state valid_part hdr_blockset log_blocksets,
    let valid_header_part :=
        match valid_part with
        | Old_Part => old_part hdr
        | Current_Part => current_part hdr
        end in
    let valid_log_blocks := firstn (count valid_header_part) (map fst log_blocksets) in

    log_rep_explicit header_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
    (valid_part = Old_Part ->
     hash (current_part hdr) <> rolling_hash hash0 (firstn (count (current_part hdr)) (map fst log_blocksets))) ->
    exec CryptoDiskLang o s read_encrypted_log (Crashed s') ->
    fst (fst s') = fst (fst s) /\
    snd s' = snd s /\
    subset (snd (fst s)) (snd (fst s')).
Proof.
  unfold read_encrypted_log, read_header, check_hash; simpl; intros.
  repeat (try split_ors; cleanup_no_match; invert_exec; repeat cleanup);
  try solve[ destruct s; simpl; eauto ].

  eapply read_consecutive_crashed in H2;
  cleanup_no_match; eauto;
  destruct s; simpl; eauto.
  
  all: try congruence;
  try solve
      [eapply read_consecutive_finished in H2;
       cleanup; eauto;
       destruct s; simpl; eauto;
       eapply hash_all_finished in H3;
       cleanup; eauto;
       destruct s; simpl in *; eauto ].

  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto.
    eapply hash_all_crashed in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply upd_batch_consistent_subset in H4.
    cleanup; intuition eauto.
    

  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply upd_batch_consistent_subset in H4.
    cleanup; intuition eauto.

  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply upd_batch_consistent_subset in H4.
    cleanup; intuition eauto.

  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply upd_batch_consistent_subset in H4.
    cleanup; intuition eauto.

  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply read_consecutive_crashed in H4;
    cleanup_no_match; eauto.      
    eapply upd_batch_consistent_subset in H5.
    cleanup; intuition eauto.
    
  - eapply read_consecutive_finished in H2;
    cleanup; eauto;
    destruct s; simpl; eauto;
    eapply hash_all_finished in H3;
    cleanup; eauto;
    destruct s; simpl in *; eauto.
    eapply read_consecutive_finished in H4;
    cleanup_no_match; eauto.
    eapply upd_batch_consistent_subset in H5.
    cleanup; intuition eauto.
Qed.


Theorem flush_txns_finished:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s' t,

    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang o s (flush_txns txn_records log_blocks) (Finished s' t) ->
    fst s' = fst s /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns)) hdr_block_num (encode_header (update_hdr hdr header_part0))).
Proof.
  unfold flush_txns, update_header, read_header, write_header; simpl; intros.
  repeat invert_exec; simpl in *; cleanup.
  eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; eauto; cleanup.  
  eapply apply_txns_finished in H2; eauto; cleanup.
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
      rewrite <- H13 in *.
      erewrite bimap_get_addr_list; eauto.
      rewrite list_upd_batch_not_in.
      unfold sync.
      rewrite H.
      erewrite selN_map; eauto.
      rewrite <- H6; eauto.
      {
        intros.
        apply in_map_iff in H15; cleanup.
        eapply Forall_forall in H14; eauto.
        unfold txn_well_formed in H14; cleanup.
        intuition.
        eapply Forall_forall in H20; eauto.
        pose proof data_start_where_log_ends.
        setoid_rewrite H6 in H12.
        lia.
      }
      {
        rewrite map_length; eauto.
      }
      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        setoid_rewrite H6 in H12.
        lia.
      }
      {
        apply in_map_iff in H12; cleanup; eauto.
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
        rewrite <- H11 in *.
        setoid_rewrite <- H11 in H.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; cleanup.
        eapply Forall_forall in H12; eauto.
        unfold txn_well_formed in H12; cleanup.
        intuition.
        eapply Forall_forall in H17; eauto.
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
      rewrite <- H12 in *.
      erewrite bimap_get_addr_list in H2; [ | | | eauto]; eauto.
      apply in_map_iff in H2; cleanup.
      eapply Forall_forall in H13; eauto.
      unfold txn_well_formed in H13; cleanup.
      intuition.
      eapply Forall_forall in H17; eauto.
      pose proof data_start_where_log_ends.
      pose proof hdr_before_log.
      lia.      
      rewrite map_length; eauto.
    }
  }
Qed.

Theorem flush_txns_crashed:
  forall txns txn_records log_blocks log_blocksets hdr hdr_blockset o s s',

    log_rep_explicit Hdr_Synced Synced Current_Part hdr txns hdr_blockset log_blocksets s ->
    txn_records = records (current_part hdr) ->
    log_blocks = firstn (count (current_part hdr)) (map fst log_blocksets) ->
    exec CryptoDiskLang o s (flush_txns txn_records log_blocks) (Crashed s') ->
    fst s' = fst s /\
    ((log_rep txns s' /\ (exists n m : nat,
                           snd s' =
                           upd_batch_set
                             (list_upd_batch_set (snd s)
                                                 (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                                                 (firstn n (map data_blocks txns)))
                             (firstn m (selN (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
                             (firstn m (selN (map data_blocks txns) n [])))) \/
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
  unfold flush_txns; intros.
  repeat (invert_exec; split_ors; cleanup).
  { (** apply txns crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; eauto; cleanup.
    eapply apply_txns_crashed in H0; eauto.
    clear H1 H2 H3 H4.
    cleanup.
    intuition.
    left.
    split; eauto.
    eapply log_rep_update_disk_preserves; eauto.
    unfold log_header_rep, log_rep_general; eauto.
  }
  { (** Sync crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished in H0; eauto; cleanup.
    clear H2 H3 H4 H5.
    invert_exec'' H1; repeat invert_exec.
    simpl in *.
    intuition.
    left.
    split; eauto.
    eapply log_rep_update_disk_preserves with (n:= length txns)(m:= 0); simpl; eauto.
    unfold log_header_rep, log_rep_general; eauto.
    repeat rewrite firstn_oob; eauto.
    rewrite map_length; eauto.
    rewrite bimap_length, map_length; eauto.
    rewrite min_r; eauto.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
    rewrite <- H8, map_length; eauto.

    exists (length txns), 0; simpl.
    repeat rewrite firstn_oob; eauto.
    rewrite map_length; eauto.
    rewrite bimap_length, min_r, map_length; eauto.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
    rewrite <- H8; repeat rewrite map_length; eauto.
  }
  { (** update_header crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished in H0; eauto; cleanup.
    clear H3 H4 H5 H6.
    invert_exec'' H1; repeat invert_exec.
    eapply_fresh (log_rep_update_disk_preserves txns hdr (length txns) 0) in H0; simpl; eauto.    
    2: unfold log_header_rep, log_rep_general; eauto.
    2: {
      repeat rewrite firstn_oob; eauto.
      rewrite map_length; eauto.
      rewrite bimap_length, map_length; eauto.
      rewrite min_r; eauto.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
      rewrite <- H9, map_length; eauto.
    }
    
    unfold update_header in *; repeat invert_exec.
    split_ors; cleanup; try invert_exec.
    { (** read_header crashed **)
      unfold read_header in *.
      repeat invert_exec.
      split_ors; cleanup; repeat invert_exec; simpl in *;
      repeat cleanup_pairs;
      intuition; right; left.
      all: split; [eapply log_rep_sync_preserves in Hx|]; eauto;
      cleanup; simpl; eauto.
    }
    { (** write_header crashed **)
      unfold read_header in *; repeat invert_exec.
      simpl in *.
      eapply log_rep_sync_preserves in Hx.
      unfold write_header in *; invert_exec'' H2;
      repeat invert_exec.
      repeat cleanup_pairs.
      simpl; intuition eauto.
    }
  }
  { (** Sync crashed **)
    eapply_fresh log_rep_explicit_implies_decrypt_txns_pre in H; logic_clean.
    eapply apply_txns_finished in H0; eauto; cleanup.
    clear H4 H5 H6 H7.
    invert_exec'' H1; repeat invert_exec.
    eapply_fresh (log_rep_update_disk_preserves txns hdr (length txns) 0) in H0; simpl; eauto.    
    apply log_rep_sync_preserves in Hx.
    unfold log_rep, log_rep_general in Hx; logic_clean; eauto.    
    eapply update_header_finished in H2; simpl in *; eauto.
    2: unfold log_rep_explicit, log_header_block_rep in *; cleanup; eauto.
    2: unfold log_header_rep, log_rep_general; eauto.
    simpl in *; cleanup.
    intuition.
    right; right.
    split.
    exists (encode_header (update_hdr (decode_header (fst x2)) header_part0)),
    (fst x2),
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
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H18 in *.
        erewrite bimap_get_addr_list in H1; [| | | eauto]; eauto.
        apply in_map_iff in H1; logic_clean; subst.
        eapply Forall_forall in H17; eauto.
        unfold txn_well_formed in H17; logic_clean.
        intuition.
        eapply Forall_forall in H17; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
        }
        {
        intros.
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H18 in *.
        erewrite bimap_get_addr_list in H1; [| | | eauto]; eauto.
        apply in_map_iff in H1; logic_clean; subst.
        eapply Forall_forall in H17; eauto.
        unfold txn_well_formed in H17; logic_clean.
        intuition.
        eapply Forall_forall in H17; eauto.
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
        pose proof hdr_before_log; lia.
        
      }
      lia.
      rewrite <- H0; lia.
      {
        unfold log_rep_inner in *; simpl in *; cleanup.
        split.
        apply header_part0_valid.
        apply txns_valid_nil.
      }
      {
        rewrite <- H0.
        unfold log_rep_inner in *; simpl in *; logic_clean.
        intuition eauto.
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
        rewrite <- H13 in *.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; logic_clean; subst.
        eapply Forall_forall in H6; eauto.
        unfold txn_well_formed in H6; logic_clean.
        intuition.
        eapply Forall_forall in H20; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
      }
      {
        intros.
        unfold log_header_block_rep, log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H13 in *.
        erewrite bimap_get_addr_list in H; [| | | eauto]; eauto.
        apply in_map_iff in H; logic_clean; subst.
        eapply Forall_forall in H6; eauto.
        unfold txn_well_formed in H6; logic_clean.
        intuition.
        eapply Forall_forall in H20; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.        
        rewrite map_length; eauto.
      }
    }
    {
      repeat cleanup_pairs; eauto.
      unfold log_rep_explicit, log_header_block_rep; do 2 eexists; simpl; intuition eauto.
      rewrite D; simpl; eauto.
      rewrite D; simpl; eauto.
    }
    {
      repeat rewrite firstn_oob; eauto.
      rewrite map_length; eauto.
      rewrite bimap_length, map_length, min_r; eauto.
      unfold log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
      rewrite <- H11, map_length; eauto.
    }
  }
Qed.


Theorem apply_log_finished:
  forall txns hdr o s s' t,

    log_header_rep hdr txns s ->
    exec CryptoDiskLang o s apply_log (Finished s' t) ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    log_rep [] s' /\
    snd s' = sync (upd_set (list_upd_batch_set (snd s) (map addr_list txns) (map data_blocks txns)) hdr_block_num (encode_header (update_hdr hdr header_part0))).
Proof.
  unfold apply_log; intros; invert_exec.
  unfold log_header_rep, log_rep_general in *; cleanup.
  eapply read_encrypted_log_finished in H0; eauto;
  intros; try congruence.
  simpl in *; cleanup; simpl in *.
  eapply log_rep_explicit_subset in H; eauto.
  eapply flush_txns_finished in H1; eauto.
  cleanup.
  repeat cleanup_pairs; simpl in *; eauto.
Qed.


Theorem apply_log_crashed:
  forall txns hdr o s s',

    log_header_rep hdr txns s ->
    exec CryptoDiskLang o s apply_log (Crashed s') ->
    fst (fst s') = fst (fst s) /\
    subset (snd (fst s)) (snd (fst s')) /\
    ((log_rep txns s' /\ snd s' = snd s) \/
     (log_rep txns s' /\ (exists n m : nat,
                           snd s' =
                           upd_batch_set
                             (list_upd_batch_set (snd s)
                                                 (firstn n (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)))
                                                 (firstn n (map data_blocks txns)))
                             (firstn m (selN (bimap get_addr_list (records (current_part hdr)) (map addr_blocks txns)) n []))
                             (firstn m (selN (map data_blocks txns) n [])))) \/
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
  unfold apply_log, log_header_rep, log_rep_general; intros; cleanup.
  invert_exec; split_ors; cleanup.
  {
    eapply read_encrypted_log_crashed in H0; eauto.
    cleanup.
    intuition eauto.
    left; intuition eauto.
    
    eapply log_rep_explicit_subset in H; eauto.
    unfold log_rep, log_rep_general; eauto.
    intros; congruence.
  }
  {
    eapply read_encrypted_log_finished in H0; eauto; simpl in *; cleanup.
    eapply log_rep_explicit_subset in H; eauto.
    eapply flush_txns_crashed in H1; eauto.
    cleanup; repeat cleanup_pairs; intuition eauto.
    intros; congruence.
  }
Qed.



Theorem commit_txn_finished:
  forall txns hdr l_addr l_data o s s' t,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    
    exec CryptoDiskLang o s (commit_txn l_addr l_data) (Finished s' t) ->
    exists txn,
      addr_blocks txn = l_addr /\
      data_blocks txn = l_data /\
      log_rep (txns ++ [txn]) s' /\
      (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a).
Proof.
  unfold commit_txn, update_header, read_header, write_header;
  intros; repeat invert_exec.
  apply encrypt_all_finished in H6.
  apply hash_all_finished in H8.
  apply write_consecutive_finished in H9.
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
      
      instantiate (1:= firstn (count (current_part (decode_header v0))) (map (fun vs => (fst vs, [])) x1) ++ 
                              (map (fun v => (v, [])) (map (encrypt x6) (l_addr ++ l_data))) ++
                              skipn (length (l_addr++l_data) + (count (current_part (decode_header v0))))
                              (map (fun vs => (fst vs, [])) x1)).
      repeat rewrite app_length in H.
      rewrite firstn_length_l, skipn_length in H.
      repeat rewrite map_length in *.
      
      repeat rewrite Nat.add_assoc in H.
      assume (A: (count (current_part (decode_header v0)) + length (l_addr ++ l_data) +
                  (length x1 - (length l_addr + length l_data + count (current_part (decode_header v0)))) = length x1)).
      setoid_rewrite A in H.
      clear A.
      destruct (lt_dec i (count (current_part (decode_header v0)))).
      {
        rewrite selN_app; eauto.
        rewrite upd_batch_ne.
        rewrite selN_firstn; eauto.
        unfold sync; rewrite e.
        erewrite selN_map; eauto.
        lia.
        intros Hx; apply in_seq in Hx.
        simpl in *.
        rewrite log_start_eq in Hx; simpl in *; lia.
        rewrite firstn_length_l; eauto.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
      }
      destruct (lt_dec i (count (current_part (decode_header v0)) + length (l_addr++l_data))).
      {
        rewrite selN_app2.
        rewrite firstn_length_l.
        rewrite selN_app1.
        erewrite upd_batch_eq; eauto.

        Lemma selN_seq:
          forall len start n def,
            n < len ->
            selN (seq start len) n def = (start + n).
        Proof.
          induction len; simpl; intuition eauto.
          lia.
          destruct n; eauto.
          rewrite IHlen; lia.
        Qed.
        
        rewrite selN_seq.
        rewrite log_start_eq; simpl.
        replace (S (S (count (current_part (decode_header v0)) + (i - count (current_part (decode_header v0)))))) with (S (S i)) by lia; eauto.
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
        setoid_rewrite e0; eauto.
        rewrite firstn_length_l; eauto.
        lia.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
      }
      {
        repeat rewrite selN_app2.
        rewrite firstn_length_l.
        repeat rewrite map_length.
        rewrite upd_batch_ne.
        rewrite skipn_selN.
        unfold sync.
        replace (length (l_addr ++ l_data) + count (current_part (decode_header v0)) +
                 (i - count (current_part (decode_header v0)) - length (l_addr ++ l_data))) with i by lia; eauto.
        erewrite e, selN_map; eauto.
        lia.

        intros Hx; apply in_seq in Hx.
        rewrite log_start_eq in Hx; simpl in *.
        inversion Hx. lia.
        
        repeat rewrite map_length, seq_length; eauto.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
        rewrite firstn_length_l;
        repeat rewrite map_length; eauto.
        lia.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.

        rewrite firstn_length_l;
        repeat rewrite map_length; eauto.
        lia.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
      }
      {
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
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
        setoid_rewrite e0.
        lia.
        rewrite map_length; eauto.
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        setoid_rewrite e0; eauto.
      }
    }
    {
      repeat rewrite app_length.
      rewrite firstn_length_l, skipn_length.
      repeat rewrite map_length.
      unfold log_header_block_rep in *; simpl in *;
      cleanup_no_match; simpl in *.
      repeat rewrite app_length in *.
      setoid_rewrite e0.
      lia.
      rewrite map_length; eauto.
      unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
      setoid_rewrite e0; eauto.
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
      rewrite hdr_block_num_eq in Hx; lia.
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
          setoid_rewrite e0; eauto.
          lia.
        }
        {
          (** Solve with lemma **)
          admit.
        }
        {
          repeat rewrite app_length in *; eauto.
        }
        {
          rewrite map_app, fold_left_app; simpl.
          lia.
        }
        {
          (** SOlve with lemma **)
          admit.
        }
      }
      {
        unfold txns_valid in *; simpl in *; cleanup_no_match.
        intuition eauto.
        repeat rewrite map_app; simpl;
        rewrite H5; eauto.

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
            rewrite H8.
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
            rewrite map_length; setoid_rewrite e0; lia.
            rewrite map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e0; lia.
          }
          {
            rewrite H9.
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
            rewrite map_length; setoid_rewrite e0; lia.
            rewrite map_length, firstn_length_l; try lia.
            rewrite map_length; setoid_rewrite e0; lia.
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
            setoid_rewrite e0; lia.
          }
          {
            rewrite skipn_app_r_ge.
            rewrite map_length, firstn_length_l.
            rewrite skipn_app_l.
            rewrite skipn_app_r_ge.
            rewrite map_length.
            replace (length l_addr + count (current_part (decode_header v0)) - count (current_part (decode_header v0)) -
                                     length l_addr) with 0 by lia; simpl.
            rewrite firstn_app_l.
            rewrite firstn_oob; eauto.
            rewrite map_length; eauto.
            rewrite map_length; eauto.
            rewrite map_length; lia.
            rewrite app_length, map_length; lia.
            rewrite map_length;
            setoid_rewrite e0; lia.
            rewrite map_length, firstn_length_l; eauto.
            lia.
            rewrite map_length;
            setoid_rewrite e0; lia.
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
    rewrite log_start_eq in H.
    lia.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
  }
  Unshelve.
  {
    unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; cleanup_no_match;
    simpl in *.
    repeat rewrite map_app in *.
    rewrite app_length in *.
    lia.
  }
  eauto.
Admitted.



Arguments log_crash_rep : simpl never.

Theorem commit_txn_crashed:
  forall txns hdr l_addr l_data o s s',
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    count (current_part hdr) + length (l_addr ++l_data) <= log_length ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    
    exec CryptoDiskLang o s (commit_txn l_addr l_data) (Crashed s') ->
    (log_rep txns s' /\ snd s' = snd s) \/
    (log_crash_rep (During_Commit_Log_Write txns) s' /\
     (forall a, a >= data_start -> (snd s') a = (snd s) a)) \/
    (exists txn,
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_crash_rep (During_Commit_Header_Write txns (txns ++ [txn])) s' /\
       (forall a, a >= data_start -> (snd s') a = (snd s) a)).
Proof.
  unfold commit_txn, read_header;
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
    eapply encrypt_all_crashed in H4; cleanup.
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
  }
  apply encrypt_all_finished in H4.
  repeat cleanup_pairs; simpl in *;
  split_ors; cleanup; repeat invert_exec.
  {(** hash_all crashed **)
    eapply hash_all_crashed in H4; cleanup.
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
        (** Hashes in hashmap goal **)
        admit.
      }
      {
        unfold txns_valid in *; simpl in *; logic_clean.
        intuition eauto.
        eapply Forall_impl; [| eauto].
        unfold txn_well_formed, record_is_valid; simpl; intros; logic_clean.
        intuition eauto.
      }
    }
  }
  apply hash_all_finished in H4.
  repeat cleanup_pairs; simpl in *;
  split_ors; cleanup_no_match; repeat invert_exec_no_match.
  {(** write_consecutive crashed **)
    eapply write_consecutive_crashed in H4; cleanup_no_match.
    repeat cleanup_pairs; simpl in *.
    right; left.
    intuition eauto.
    {
      unfold log_header_rep, log_rep_general, log_rep_explicit in *; simpl; logic_clean.
      unfold log_crash_rep; simpl.
      exists x1, (firstn (count (current_part hdr)) x3),
      (bimap (fun v vs => (v, fst vs::snd vs)) (firstn x (map (encrypt x0) (l_addr++l_data))) (firstn x (skipn (count (current_part hdr)) x3)) ++ skipn (x + (count (current_part hdr))) x3).
      simpl in *.
      intuition eauto.
      {
        unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
        intuition eauto.
        rewrite upd_batch_set_ne; eauto.
        intros Hx; apply in_firstn_in in Hx.
        apply in_seq in Hx.
        rewrite hdr_block_num_eq in Hx; lia.
      }
      {
        unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
        intuition eauto.
        rewrite firstn_length_l in H.
        rewrite upd_batch_set_ne; eauto.
        rewrite selN_firstn; eauto.
        apply H8; eauto.
        all: try lia.
        
        rewrite seq_length in H4.
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
        rewrite seq_length, map_length, app_length in H4.
        
        replace (count (current_part (decode_header v)) +
                 (x + (length x3 - (x + count (current_part (decode_header v)))))) with (length x3) in H by lia.

        destruct (lt_dec i (count (current_part (decode_header v)))).
        {(** first_part of log **) 
          rewrite upd_batch_set_ne; eauto.
          rewrite selN_app; eauto.
          rewrite selN_firstn; eauto.
          apply H8; eauto.
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
          rewrite selN_app2.
          rewrite selN_app.

          erewrite selN_bimap; simpl; auto.
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
          
          rewrite selN_firstn.
          rewrite skipn_selN.
          rewrite firstn_length_l.
          replace (count (current_part (decode_header v)) + (i - count (current_part (decode_header v)))) with i by lia.
          apply H8; eauto.
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
          repeat rewrite selN_app2; eauto.
          rewrite bimap_length, min_l.
          repeat rewrite firstn_length_l.
          rewrite skipn_selN; eauto.
          replace (x + count (current_part (decode_header v)) + (i - count (current_part (decode_header v)) - x)) with i by lia.          
          apply H8; eauto.
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
        all: rewrite seq_length in H4; eauto.
        lia.
        lia.        
        repeat rewrite firstn_length_l; eauto.
        rewrite skipn_length.
        rewrite map_length, app_length in H4; lia.
        {
          apply in_app_iff in H; split_ors.
          {
            apply in_firstn_in in H.
            rewrite H15; eauto.
          }
          apply in_app_iff in H; split_ors.
          {
            rewrite bimap_combine_map in H.
            apply in_map_iff in H; cleanup_no_match.
            simpl.
            destruct x1; simpl; eapply in_combine_r in H7.
            apply in_firstn_in in H7.
            apply in_skipn_in in H7.
            rewrite H15; eauto.
          }
          {
            apply in_skipn_in in H.
            rewrite H15; eauto.
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
        rewrite seq_length in H4.
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
        rewrite seq_length in H4.
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
      apply seq_length.
    }
  }
  apply write_consecutive_finished in H4.
  2: apply seq_length.
  simpl in *; logic_clean; repeat cleanup_pairs; simpl in *.
  split_ors; cleanup_no_match; repeat invert_exec_no_match.
  {
    eapply update_header_crashed in H6; eauto; subst.
    {
      right; left.
      intuition eauto.
      {
        unfold log_header_rep, log_rep_general, log_rep_explicit in *; simpl; logic_clean.
        unfold log_crash_rep; simpl.
          exists x, (firstn (count (current_part hdr)) x2),
          (bimap (fun v vs => (v, fst vs::snd vs)) (map (encrypt x0) (l_addr++l_data)) (firstn (length (l_addr++l_data)) (skipn (count (current_part hdr)) x2)) ++ skipn (length (l_addr++l_data) + (count (current_part hdr))) x2).
          simpl in *.
          intuition eauto.
          {
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite upd_batch_set_ne; eauto.
            intros Hx;
            apply in_seq in Hx.
            rewrite hdr_block_num_eq in Hx; lia.
          }
          {
            unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite firstn_length_l in H.
            rewrite upd_batch_set_ne; eauto.
            rewrite selN_firstn; eauto.
            apply H7; eauto.
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
              rewrite selN_app; eauto.
              rewrite selN_firstn; eauto.
              apply H7; eauto.
              all: try lia.
              repeat constructor; eauto.
              rewrite firstn_length_l; lia.
              
              intros Hx; apply in_seq in Hx.
              rewrite log_start_eq in Hx; simpl in *; lia.
            }
            destruct (lt_dec i (length (l_addr++l_data) + count (current_part (decode_header v)))).
            {(** overwritten part of the log **)
              erewrite upd_batch_set_seq_in.
              rewrite selN_app2.
              rewrite selN_app.

              erewrite selN_bimap; simpl; auto.
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
              
              rewrite selN_firstn.
              rewrite skipn_selN.
              rewrite firstn_length_l.
              replace (count (current_part (decode_header v)) + (i - count (current_part (decode_header v)))) with i by lia.
              apply H7; eauto.
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
              repeat rewrite selN_app2; eauto.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_selN; eauto.
              rewrite map_length, app_length in *.
              replace (length l_addr + length l_data + count (current_part (decode_header v)) +
        (i - count (current_part (decode_header v)) - (length l_addr + length l_data)))  with i by lia.          
              apply H7; eauto.
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
                rewrite H14; eauto.
              }
              apply in_app_iff in H; split_ors.
              {
                rewrite bimap_combine_map in H.
                apply in_map_iff in H; cleanup_no_match.
                simpl.
                destruct x; simpl; eapply in_combine_r in H6.
                apply in_firstn_in in H6.
                apply in_skipn_in in H6.
                rewrite H14; eauto.
              }
              {
                apply in_skipn_in in H.
                rewrite H14; eauto.
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
            }
          }
        }
        {
          apply upd_batch_set_ne.
          intros Hx; apply in_seq in Hx.
          pose proof data_start_where_log_ends.
          unfold log_header_rep, log_rep_general,
          log_rep_explicit, log_header_block_rep in *;
          simpl in *; cleanup_no_match; simpl in *.
          rewrite map_length, log_start_eq in *.
          lia.
        }
    }
  }
  {
    eapply update_header_finished in H6; eauto.
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
          (bimap (fun v vs => (v, fst vs::snd vs)) (map (encrypt x0) (l_addr++l_data)) (firstn (length (l_addr++l_data)) (skipn (count (current_part (decode_header (fst x)))) x1)) ++ skipn (length (l_addr++l_data) + (count (current_part (decode_header (fst x))))) x1).
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
            rewrite hdr_block_num_eq in Hx; simpl in *; lia.
          }
          {
            unfold log_data_blocks_rep in *; simpl in *; cleanup_no_match.
            intuition eauto.
            rewrite firstn_length_l in H15.
            rewrite upd_ne.
            rewrite upd_batch_set_ne; eauto.
            rewrite selN_firstn; eauto.
            apply H; eauto.
            all: try lia.
            
            intros Hx; apply in_seq in Hx.
            rewrite log_start_eq in Hx; simpl in *.
            unfold log_header_block_rep in *; simpl in *; cleanup_no_match.
            simpl in *; lia.
            rewrite log_start_eq, hdr_block_num_eq; lia.
            apply in_firstn_in in H15; eauto.        
            rewrite firstn_length_l; lia.
          }
          { 
            unfold log_header_block_rep, log_data_blocks_rep in *;
            simpl in *; cleanup_no_match; simpl in *.
            intuition eauto.
            
            rewrite upd_batch_set_ne in D0;
            cleanup_no_match; simpl; eauto.
            
            repeat rewrite app_length in *.
            rewrite bimap_length, min_l in H6.
            rewrite firstn_length_l in H6.
            rewrite skipn_length in H6.
            repeat rewrite map_length, app_length in H6.
            
            replace (count (current_part (decode_header v0)) +
        (length l_addr + length l_data +
         (length x1 - (length l_addr + length l_data + count (current_part (decode_header v0)))))) with (length x1) in H6 by lia.
            rewrite upd_ne.
            destruct (lt_dec i (count (current_part (decode_header v0)))).
            {(** first_part of log **) 
              rewrite upd_batch_set_ne; eauto.
              rewrite selN_app; eauto.
              rewrite selN_firstn; eauto.
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
              rewrite selN_app2.
              rewrite selN_app.

              erewrite selN_bimap; simpl; auto.
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

              rewrite selN_firstn.
              rewrite skipn_selN.
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
              repeat rewrite selN_app2; eauto.
              rewrite bimap_length, min_l.
              repeat rewrite firstn_length_l.
              rewrite skipn_selN; eauto.
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
              rewrite hdr_block_num_eq in Hx; simpl in *; lia.
            }
            {
              apply in_app_iff in H6; split_ors.
              {
                apply in_firstn_in in H6.
                rewrite H7; eauto.
              }
              apply in_app_iff in H6; split_ors.
              {
                rewrite bimap_combine_map in H6.
                apply in_map_iff in H6; cleanup_no_match.
                simpl.
                destruct x; simpl; eapply in_combine_r in H16.
                apply in_firstn_in in H16.
                apply in_skipn_in in H16.
                rewrite H7; eauto.
              }
              {
                apply in_skipn_in in H6.
                rewrite H7; eauto.
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
            rewrite hdr_block_num_eq in Hx; simpl in *; lia.    
          }
          {
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.            
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; rewrite app_length in *;
            lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq in Hx; simpl in *; lia.
          }
          {
            unfold log_header_block_rep in *; simpl in *;
            cleanup_no_match; subst; eauto.
            
            rewrite upd_batch_set_ne in D0; cleanup_no_match.
            simpl in *; rewrite app_length in *;
            lia.
            
            intros Hx; apply in_seq in Hx.              
            rewrite hdr_block_num_eq in Hx; simpl in *; lia.
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
            rewrite hdr_block_num_eq in Hx; simpl in *; lia.
                        
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
              (** Hashes in hashmap goal **)
              admit.

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
              apply upd_batch_consistent_subset; eauto.
              rewrite D in *; simpl in *.
              rewrite app_length in *; lia.
              {
                rewrite D in *; simpl in *.
                rewrite map_app; simpl; rewrite fold_left_app; simpl.            
                lia.
              }
              {
                (** Records are consecutive goal **)
                admit.
              }              
            }
            {
              simpl in *; 
              rewrite D in *; simpl in *.
              unfold txns_valid in *;
              simpl in *; logic_clean; simpl in *.
              rewrite <- H6 in *.
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
                }
              }
            }
            {
              intros Hx; apply in_seq in Hx.
              rewrite hdr_block_num_eq in Hx; lia.
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
              rewrite <- H6 in *.
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
              }
            }
            {
              intros Hx; apply in_seq in Hx.
              rewrite hdr_block_num_eq in Hx; lia.
            }              
          }
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
        rewrite log_start_eq in H; simpl in *; lia.
      }
      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
      }
      Unshelve.
      all: repeat constructor; eauto.
Admitted.



Theorem commit_finished:
  forall txns l_addr l_data hdr o s s' t,
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_header_rep hdr txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    
    exec CryptoDiskLang o s (commit l_addr l_data) (Finished s' t) ->
    (exists txn,
       t = true /\
       addr_blocks txn = l_addr /\
       data_blocks txn = l_data /\
       log_rep (txns ++ [txn]) s' /\
       (forall a, a >= data_start -> (snd s') a = (sync (snd s)) a)) \/
    (t = false /\ s' = s /\ count (current_part hdr) + length (l_addr ++ l_data) > log_length).
Proof.
  unfold commit, read_header; intros.
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
  eapply commit_txn_finished in H4; eauto.
  logic_clean; left; eexists; intuition eauto.
  unfold log_header_rep, log_rep_general, log_rep_explicit, log_header_block_rep in *.
  simpl in *; cleanup; simpl; rewrite app_length; eauto.
  apply Nat.ltb_ge; eauto.
Qed.


Theorem commit_crashed:
  forall txns l_addr l_data o s s',
    let addr_list := (firstn (length l_data) (blocks_to_addr_list l_addr)) in
    
    log_rep txns s ->
    NoDup addr_list ->
    Forall (fun a => disk_size > a /\ a >= data_start) addr_list ->
    length l_data <= length (blocks_to_addr_list l_addr) ->
    
    exec CryptoDiskLang o s (commit l_addr l_data) (Crashed s') ->
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
  unfold commit, read_header; simpl; intros.
  repeat invert_exec.
  split_ors; cleanup; repeat invert_exec; eauto.
  {(** read_header crashed **)
    split_ors; cleanup; repeat invert_exec; eauto.
  }
  split_ors; cleanup; repeat invert_exec; eauto.
  {(** commit_txn_crashed **)
    unfold log_rep in *; cleanup.
    eapply commit_txn_crashed in H3; eauto.
    intuition eauto.
    unfold log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *.
    rewrite app_length;
    apply Nat.ltb_ge in D; lia.
  }
  {
    unfold log_rep in *; cleanup.
    eapply commit_txn_finished in H3; eauto.
    unfold log_rep_general, log_rep_explicit, log_header_block_rep in *;
    simpl in *; cleanup; simpl in *.
    rewrite app_length;
    apply Nat.ltb_ge in D; lia.
  }
Qed.

Theorem recover_finished:
  forall o s txns s' r,
    log_reboot_rep txns s ->
    exec CryptoDiskLang o s recover (Finished s' r) ->
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
          rewrite map_length in H8.
          rewrite sync_upd_comm; simpl.
          rewrite upd_ne.
          unfold sync; erewrite selN_map. 
          rewrite H; eauto.
          rewrite <- H3; eauto.
          lia.
          pose proof hdr_before_log.
          lia.
        }
        {
          apply in_map_iff in H8; cleanup; simpl; eauto.
        }
        {
          rewrite map_length, <- H3; eauto.
        }
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D0 in *; simpl in *.
        destruct x0; eauto.
      }
      {
        unfold log_header_block_rep in *; cleanup; simpl in *.
        rewrite D0 in *; simpl in *.
        destruct x0; eauto.
      }
      {
        rewrite map_map; simpl.
        unfold log_rep_inner in *; cleanup_no_match; simpl in *.
        unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
        rewrite D0 in *; simpl in *; eauto.
        intuition eauto.
        {
          eapply header_part_is_valid_subset; eauto.
        }
      }
      {
        split.
        unfold log_rep_inner, txns_valid in *; logic_clean.
        rewrite <- H6.
        erewrite bimap_get_addr_list.
        eauto.
        3: eauto.
        destruct x0; eauto.
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
Qed.

Theorem recover_crashed:
  forall o s txns s',
    log_reboot_rep txns s ->
    exec CryptoDiskLang o s recover (Crashed s') ->
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
    eapply read_encrypted_log_finished in H0; eauto.
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
            pose proof hdr_before_log.
            lia.
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
            exists x0; intuition eauto.
            eapply header_part_is_valid_subset; eauto; cleanup; eauto.     
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
        eapply decrypt_txns_crashed in H2; eauto.
        clear H0 H3 H4 H6.
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
            rewrite map_length in H0.
            rewrite sync_upd_comm; simpl in *.
            rewrite upd_ne; eauto.
            unfold sync; erewrite selN_map;
            simpl; eauto.
            rewrite H; eauto.
            pose proof hdr_before_log.
            lia.
            apply in_map_iff in H0; cleanup; eauto.
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
          }
        }
        {
          simpl; intros.
          rewrite sync_upd_comm; simpl.
          apply upd_ne.
          pose proof hdr_before_log.
          pose proof data_start_where_log_ends; lia.
        }          
      }
    }
  }
Qed.

