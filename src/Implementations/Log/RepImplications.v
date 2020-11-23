Require Import EquivDec Framework CryptoDiskLayer BatchOperations Log.Log.
Require Import Datatypes PeanoNat.
Require Import Lia Sumbool.
Require Import FSParameters.
Require Import FunctionalExtensionality.
Require Import Compare_dec.

Set Nested Proofs Allowed.


Lemma select_list_shifted_select_0:
  forall V (l: list (V * list V)) n selector,
    (forall i, i < length l -> selector (n + i) = Some 0) ->
    select_list_shifted n selector l = map fst l.
Proof.
  unfold select_list_shifted; induction l;
  simpl; intros; eauto.
  erewrite IHl; eauto.
  unfold select_for_addr.
  setoid_rewrite <- Nat.add_0_r.
  rewrite H; eauto.
  lia.
  intros.
  rewrite Nat.add_succ_comm.
  eapply H; lia.
Qed.


Lemma select_list_shifted_app:
  forall V (l' l: list (V * list V)) n selector,
    select_list_shifted n selector (l++l') =
    select_list_shifted n selector l ++
                        select_list_shifted (n + length l) selector l'.
Proof.
  induction l; simpl; intros; eauto.
  unfold select_list_shifted; simpl.
  rewrite Nat.add_0_r; eauto.
  unfold select_list_shifted in *; simpl.
  rewrite IHl.
  replace (n + S (length l)) with (S n + length l) by lia; eauto.
Qed.


Lemma select_list_shifted_selN :
  forall V (l: list (V * list V)) selector i def1 def2 start,
    i < length l ->
    select_for_addr selector (start + i) (selN l i def1) =
    selN (select_list_shifted start selector l) i def2.
Proof.
  unfold select_list_shifted; induction l;
  simpl; intros; eauto.
  lia.
  destruct i; simpl in *; eauto.
  rewrite Nat.add_0_r; auto.
  erewrite <- IHl.
  rewrite Nat.add_succ_comm; eauto.
  lia.
Qed.


Lemma select_for_addr_not_1_latest :
  forall A AEQ V (selector: @mem A AEQ nat) (n: A) (v1 v2: V),
    selector n <> Some 1 ->
    select_for_addr selector n (v1, [v2]) = v1.
Proof.
  unfold select_for_addr; intros; simpl.
  destruct (selector n); simpl; eauto.
  destruct n0; simpl; eauto.
  destruct n0; simpl; eauto.
  congruence.
Qed.

Lemma crash_rep_to_reboot_rep :
  forall s old_txns new_txns selector,
    log_crash_rep (During_Commit_Header_Write old_txns new_txns) s ->
    
    (** Selector does not cause a hash collision. **)
    (forall old_log_blocksets new_log_blocks,
       length old_log_blocksets = length new_log_blocks ->
       length old_log_blocksets <= log_length ->
       (forall i, i < length old_log_blocksets ->
             (snd s) (log_start + i) = selNopt old_log_blocksets i) ->
       (forall i, i < length new_log_blocks ->
             (select_mem selector (snd s)) (log_start + i) = selNopt (map (fun v => (v, [])) new_log_blocks) i) ->
       rolling_hash hash0 (map fst old_log_blocksets) = rolling_hash hash0 new_log_blocks ->
       map fst old_log_blocksets = new_log_blocks) ->
    
    log_reboot_rep old_txns (fst s, select_mem selector (snd s)) \/
     log_reboot_rep new_txns (fst s, select_mem selector (snd s)).
Proof.
  unfold log_crash_rep, log_header_rep, log_reboot_rep, log_rep_general, log_rep_explicit; intros; cleanup.
  
  cleanup.
  (*
  { (** new txns **)
    right.
    eexists ?[hdr].
    exists Current_Part.
    exists (select_for_addr selector hdr_block_num ((x0, []), nil)).
    exists (map (fun v => (v, nil)) (select_list_shifted log_start selector x1)).
    simpl; intuition eauto.
    {
      unfold log_header_block_rep in *; cleanup_no_match; simpl in *.
      unfold select_mem; simpl.
      match goal with
      | [H: snd _ _ = Some _ |- _] =>
        setoid_rewrite H
      end; eauto.
      repeat rewrite select_for_addr_synced; simpl; eauto.      
    }
    {    
      unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.
      
      intuition eauto.
      {
        erewrite selN_selNopt.
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
        | [H: forall _, _ -> snd _ (_ + _) = selNopt _ _ |- _] =>
          rewrite H
        end.   
        erewrite selN_selNopt.
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
      unfold log_rep_inner in *; simpl in *.
      repeat rewrite select_for_addr_synced; eauto; simpl.
    }
    { unfold log_rep_inner in *; simpl in *.
      repeat rewrite select_for_addr_synced; eauto; simpl.
    }
    {      
      unfold log_rep_inner in *; simpl in *.
      repeat rewrite select_for_addr_synced; eauto; simpl.
      rewrite map_map, map_id; simpl.
      unfold log_data_blocks_rep in *; cleanup.
      rewrite select_list_shifted_synced; eauto.
      intuition eauto.
      {
        unfold txns_valid in *; cleanup; intuition eauto.
        eapply Forall_impl; [|eauto].
        unfold txn_well_formed; simpl; intros; cleanup; intuition eauto.
        match goal with
        | [H: forall _, In _ _ -> snd _ _ = None -> False |- _] =>
          eapply H
        end; eauto.
        unfold select_mem in *.
        destruct_fresh (snd s a0); cleanup; eauto.
      }
    }
    {
      congruence.
    }
  }
   *)
  {
    { (** old txns **)
      
      unfold log_header_block_rep in *; cleanup.
      simpl in *.
      cleanup.

      destruct (option_dec Nat.eq_dec (selector hdr_block_num) (Some 1)).
      {(** Selector rolled back to old header **)
        left.
        eexists ?[hdr].
        exists Current_Part.
        exists (select_for_addr selector hdr_block_num (x0,[x]), nil).
        exists (map (fun v => (v, nil)) (select_list_shifted log_start selector (x1++x2))).
        simpl; intuition eauto.
        {
          unfold select_mem, select_for_addr; simpl; cleanup.
          destruct_fresh (hdr_block_num =? hdr_block_num); simpl; intuition eauto.
        }
        {    
          unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.
          intuition eauto.
          {
            erewrite selN_selNopt.
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
            | [H: forall _, _ -> snd _ (_ + _) = selNopt _ _ |- _] =>
              rewrite H
            end.   
            erewrite selN_selNopt.
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
            unfold header_part_is_valid, txns_valid in *; cleanup; intuition eauto.
            eapply Forall_forall; intros.
            
            rewrite <- H14, <- H9 in *.
            eapply Forall_forall in H11; eauto.
            eapply Forall_forall in H15.
            2: apply in_map; eauto.
            
            unfold record_is_valid, txn_well_formed in *; simpl; intros; cleanup; intuition eauto.
            {
              rewrite select_list_shifted_app, map_app.
              repeat rewrite <- skipn_firstn_comm.
              repeat rewrite firstn_app_l.
              rewrite select_list_shifted_synced; eauto.

              unfold log_data_blocks_rep in *; cleanup; eauto.
              rewrite select_list_shifted_length; eauto.
              rewrite <- H14, <- H9 in *.
              eapply Nat.le_trans.
              2: eauto.
              lia.
              rewrite <- H14, <- H9 in *.
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
              rewrite <- H14, <- H9 in *.
              eapply Nat.le_trans.
              2: eauto.
              lia.
              rewrite <- H14, <- H9 in *.
              rewrite map_length;
              eapply Nat.le_trans.
              2: eauto.
              lia.
            }
            {
              match goal with
              | [H: forall _, In _ _ -> snd _ _ = None -> False |- _] =>
                eapply H
              end; eauto.
              unfold select_mem in *.
              destruct_fresh (snd s a); cleanup; eauto.
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
              repeat econstructor; eauto.
              rewrite firstn_length_l; eauto.
              setoid_rewrite H4.
              eauto.
              repeat econstructor; eauto.
              lia.
              lia.
              setoid_rewrite H4.
              eauto.
            }
            {
              rewrite firstn_length_l; eauto.
              intros.
              unfold select_mem.
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
              repeat econstructor; eauto.
              rewrite map_length, firstn_length_l; eauto.
              rewrite select_list_shifted_length.
              setoid_rewrite H4; eauto.
              repeat econstructor; eauto.
              lia.
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
             unfold select_mem; simpl.
             setoid_rewrite H1; eauto.
             rewrite select_for_addr_not_1_latest in *; eauto.
           }
           {    
             unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.             
             intuition eauto.
             {
               erewrite selN_selNopt; eauto.
               rewrite map_length in H15.
               erewrite selN_map; eauto.
               rewrite select_list_shifted_length in H15.
               rewrite H3.    
               erewrite selN_selNopt.
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
               unfold header_part_is_valid, txns_valid in *; logic_clean; intuition eauto.
               eapply Forall_forall; intros.
               eapply Forall_forall in H10; eauto.
               eapply Forall_forall in H15.
               2: rewrite <- H9; apply in_map; eauto.
                
                unfold record_is_valid, txn_well_formed in *; simpl; intros; logic_clean; intuition eauto.
               {
                 repeat rewrite <- skipn_firstn_comm.
                 replace (start (record x3) + addr_count (record x3)) with
                     (min (start (record x3) + addr_count (record x3))
                          (count (current_part (decode_header x0)))) by lia.
                 rewrite <- firstn_firstn, A.
                 rewrite firstn_firstn, min_l by lia.
                 rewrite skipn_firstn_comm; eauto.
               }
               
               {
                 repeat rewrite <- skipn_firstn_comm.
                 replace (addr_count (record x3) + start (record x3) + data_count (record x3)) with
                     (min (addr_count (record x3) + start (record x3) + data_count (record x3))
                          (count (current_part (decode_header x0)))) by lia.
                 rewrite <- firstn_firstn, A.
                 rewrite firstn_firstn, min_l by lia.
                 rewrite skipn_firstn_comm; eauto.
               }
               {
                 eapply H25; eauto.
                 unfold select_mem in *.
                 destruct_fresh (snd s a); eauto; setoid_rewrite D in H30; congruence.
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
            unfold select_mem; simpl; cleanup.
            rewrite select_for_addr_not_1_latest; eauto.
          }
          {    
            unfold log_data_blocks_rep, select_mem in *; cleanup_no_match; simpl in *.
            intuition eauto.
            {
              erewrite selN_selNopt.
              rewrite map_length in H15.
              erewrite selN_map; eauto.
              rewrite select_list_shifted_length in H15.
              rewrite H3.    
              erewrite selN_selNopt.
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
               unfold header_part_is_valid, txns_valid in *; logic_clean; intuition eauto.
               eapply Forall_forall; intros.
               eapply Forall_forall in H11; eauto.
               eapply Forall_forall in H15.
               2: rewrite <- H10; apply in_map; eauto.
                
                unfold record_is_valid, txn_well_formed in *; simpl; intros; logic_clean; intuition eauto.
              
                {
                  rewrite H11.
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
                  rewrite H19.
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
                  eapply H25; eauto.
                  unfold select_mem in *.
                  destruct_fresh (snd s a); subst; eauto.
                  setoid_rewrite D in H30; congruence.
                }
             }
          }
          {
            rewrite map_map, map_id in *; eauto.
          }
        }
      }
    }
  }
  Unshelve.
  all: repeat econstructor; eauto.
Qed.


Lemma header_part0_valid:
  forall log_blocksets kl hm,
    header_part_is_valid log_blocksets kl hm header_part0.
Proof.
  unfold header_part_is_valid; simpl; intros; intuition eauto.
  lia.
Qed.

Lemma txns_valid_nil:
  forall log_blocks em s,
    txns_valid header_part0 log_blocks em s [].
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
  forall txns log_blocks kl em count d,
    count <= log_length ->
    length log_blocks = log_length ->
    Forall (record_is_valid kl count) (map record txns) ->
    Forall (txn_well_formed log_blocks em d) txns ->
    bimap get_addr_list (map record txns) (map addr_blocks txns) = map addr_list txns.
Proof.
  induction txns; simpl; intros; eauto.
  inversion H1; inversion H2; cleanup.
  unfold txn_well_formed in H9; cleanup.
  unfold record_is_valid in H5; cleanup.
  unfold get_addr_list in *; simpl; eauto.
  erewrite <- map_length, H4.
  rewrite firstn_length_l; eauto.
  erewrite IHtxns; eauto.
  rewrite <- H15; eauto.
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
          rewrite map_length in H13.
          repeat erewrite selN_map; eauto.
          rewrite firstn_firstn, min_l by lia.
          rewrite <- skipn_firstn_comm.
          rewrite firstn_firstn, min_l.
          rewrite skipn_firstn_comm.
          eapply_fresh in_selN in H13.
          eapply Forall_forall in H7; eauto.
          unfold txn_well_formed in *; logic_clean; eauto.

          eapply_fresh in_selN in H13.
          eapply Forall_forall in H11; eauto.
          2: rewrite <- H6; apply in_map; eauto.
          unfold record_is_valid in *; logic_clean.
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
          rewrite map_length in H13.
          repeat erewrite selN_map; eauto.
          rewrite <- skipn_firstn_comm.
          rewrite firstn_firstn, min_l.
          repeat rewrite skipn_firstn_comm.
          rewrite skipn_skipn.
          eapply_fresh in_selN in H13.
          eapply Forall_forall in H7; eauto.
          unfold txn_well_formed in *; logic_clean; eauto.

          eapply_fresh in_selN in H13.
          eapply Forall_forall in H11; eauto.
          2: rewrite <- H6; apply in_map; eauto.
          unfold record_is_valid in *; logic_clean.
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
          rewrite bimap_length, map_length, min_l in H13; eauto.
          rewrite bimap_combine_map.
          repeat erewrite selN_map; eauto.
          rewrite firstn_length.
          rewrite selN_combine; eauto; simpl.      
          repeat erewrite selN_map; eauto.
          
          eapply_fresh in_selN in H13.
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
        eapply Forall_forall in H11; eauto.
        unfold record_is_valid in *; logic_clean; eauto.
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

Lemma encryption_upd_batch:
  forall l x8 m,
    Forall
      (fun v0 : value =>
         upd_batch m (map (encrypt x8) l)
                   (map (fun v1 : value => (x8, v1)) l) 
                   (encrypt x8 v0) = Some (x8, v0)) l.
Proof.
  induction l; simpl; eauto.
  intros; constructor; eauto.
  
  repeat rewrite <- map_app.
  destruct (in_dec value_dec a l).
  2: {
    rewrite upd_batch_upd; eauto.
    apply upd_eq; eauto.
    intro H; apply n.
    apply in_map_iff in H; cleanup.
    apply encrypt_ext in H; subst; eauto.
  }
  
  apply (in_split_last value_dec) in i; cleanup.      
  repeat rewrite map_app; simpl.
  rewrite upd_batch_app.
  simpl.
  
  rewrite upd_batch_ne.
  apply upd_eq; eauto.
  intros Hx; apply H0.
  apply in_map_iff in Hx; cleanup.
  apply encrypt_ext in H; subst; eauto.
  repeat rewrite map_length; eauto.
Qed.

Lemma upd_batch_rolling_hash_list:
  forall l l' h hm,
    hashes_in_hashmap hm h l ->
    consistent_with_upds hm (rolling_hash_list h l) l' ->
    upd_batch hm (rolling_hash_list h l) l' = hm.
Proof.
  induction l; simpl; intros; eauto.
  destruct l'; simpl in *; intuition.
  rewrite IHl; eauto.
  unfold consistent in *; intuition; try congruence.
  rewrite upd_nop; eauto.
  unfold consistent in *; intuition; try congruence.
  rewrite upd_nop; eauto.
Qed.


Lemma subset_refl:
  forall A AEQ V (m: @mem A AEQ V),
    subset m m.
Proof.
  unfold subset; intros; eauto.
Qed.

Hint Resolve subset_refl: core.

Lemma upd_batch_none:
  forall A AEQ V l l' (m: @mem A AEQ V) a,
    upd_batch m l l' a = None ->
    m a = None.
Proof.
  induction l; simpl; intros; eauto.
  destruct l'; eauto.
  eapply IHl in H; eauto.
  destruct (AEQ a a0); subst.
  rewrite upd_eq in H; eauto; congruence.
  rewrite upd_ne in H; eauto.
Qed.

Lemma subset_upd_batch_some:
  forall A AEQ V l l' (m: @mem A AEQ V) a v,
    subset m (upd_batch m l l') ->
    m a = Some v ->
    upd_batch m l l' a = Some v.
Proof.
  induction l; simpl; intros; eauto.
  destruct l'; eauto.
  edestruct H; eauto.
Qed.

Lemma upd_batch_consistent_subset:
  forall A AEQ V l l' (hm: @mem A AEQ V),
    consistent_with_upds hm l l' ->
    subset hm (upd_batch hm l l').
Proof.
  induction l; intros; eauto.
  destruct l'; intuition.
  unfold subset; intuition.
  eapply upd_batch_none; eauto.
  simpl in *; cleanup.
  eapply IHl in H1.
  eapply subset_upd_batch_some; eauto.
  unfold consistent in *; split_ors; cleanup; try congruence.
  destruct (AEQ a a0); subst; try congruence.
  rewrite upd_ne; eauto.
  destruct (AEQ a a0); subst; cleanup; try congruence.
  rewrite upd_eq; eauto.
  rewrite upd_ne; eauto.
Qed.

Lemma subset_some:
  forall A AEQ V (m1 m2: @mem A AEQ V) a v,
    m1 a = Some v ->
    subset m1 m2 ->
    m2 a = Some v.
Proof.
  intros; edestruct H0; intuition eauto.
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
  forall a b hm hm' hdr_part,
    header_part_is_valid a b hm hdr_part ->
    subset hm hm' ->
    header_part_is_valid a b hm' hdr_part.
Proof.
  unfold header_part_is_valid; intros; cleanup.
  intuition eauto.
  eapply hashes_in_hashmap_subset; eauto.
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
    setoid_rewrite e; eauto.
    simpl; eauto.
  }
  split.
  {
    unfold log_data_blocks_rep in *; cleanup.
    simpl; repeat split; intros; cleanup.
    apply sync_selNopt; eauto.
    apply e.
    rewrite map_length in H;
    rewrite <- H2; eauto.
    apply in_map_iff in H; cleanup; eauto.
    rewrite map_length, <- H2; eauto.
  }
  rewrite map_map, map_length; simpl; intuition eauto.
  {
    unfold log_rep_inner, txns_valid in *; logic_clean; simpl; intuition eauto.
    eapply Forall_impl; [| eauto].
    unfold txn_well_formed; simpl; intros; logic_clean; intuition eauto.
    eapply sync_not_none in H19; eauto.
  }
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
        rewrite <- H9 in *.
        erewrite bimap_get_addr_list in H8; eauto.
        apply in_firstn_in in H8.
        apply in_map_iff in H8; cleanup.
        eapply Forall_forall in H10; eauto.
        unfold txn_well_formed in H10; cleanup.
        intuition.
        eapply Forall_forall in H16; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.      
        rewrite map_length; eauto.
        unfold header_part_is_valid in *; cleanup; eauto.
      }
      {
        intuition.
        unfold log_rep_explicit, log_rep_inner, txns_valid in *; cleanup.
        rewrite <- H9 in *.
        erewrite bimap_get_addr_list in H8; eauto.
        apply in_firstn_in in H8.

        destruct (lt_dec n (length txns)).        
        erewrite selN_map in H8; eauto.
        eapply Forall_forall in H10; eauto.
        2: eapply in_selN; eauto.
        unfold txn_well_formed in H10; logic_clean.
        eapply Forall_forall in H16; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
        rewrite selN_oob in H8.
        intuition.
        rewrite map_length; lia.
        rewrite map_length; eauto.
        unfold header_part_is_valid in *; cleanup; eauto.
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
        5: eauto.
        apply in_firstn_in in H10.
        apply in_map_iff in H10; cleanup.
        eapply Forall_forall in H12; eauto.
        unfold txn_well_formed in H12; cleanup.
        intuition.
        eapply Forall_forall in H18; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
        apply H5.
        rewrite map_length; eauto.
        rewrite H11; unfold header_part_is_valid in *; logic_clean; eauto.
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
        eapply Forall_forall in H18; eauto.
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
        rewrite selN_oob in H10.
        intuition.
        rewrite map_length; lia.
        apply H5.
        rewrite map_length; eauto.
        unfold header_part_is_valid in *; cleanup; eauto.
        eauto.
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
        apply upd_batch_set_none in H21.
        eapply list_upd_batch_not_none in H21; eauto.
      }
    }
    Unshelve.
    all: repeat econstructor.
    all: exact key0.
    Qed.

Lemma map_noop:
  forall A l (f: A -> A),
    (forall a, In a l -> f a = a) ->
    map f l = l.
Proof.
  induction l; simpl; intuition eauto.
  rewrite IHl; eauto.
  rewrite H; eauto.
Qed.

Lemma upd_not_none:
  forall A AEQ V a v a' (m: @mem A AEQ V),
    m a <> None ->
    upd m a' v a <> None.
Proof.
  intuition.
  destruct (AEQ a a'); subst.
  rewrite upd_eq in H0; eauto; congruence.
  rewrite upd_ne in H0; eauto.
Qed.
