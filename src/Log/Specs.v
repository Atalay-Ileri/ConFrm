Require Import Primitives BatchOperations DiskLayer.
Require Import Log.Definitions Log.LogParameters.
Require Import Datatypes PeanoNat Omega.
Import Nat.

Set Nested Proofs Allowed.

Instance value_eq_dec : EqDec value := value_dec.

Definition encryptionmap_valid em :=
  (forall ev k v, em ev = Some (k, v) -> ev = encrypt k v) /\
  (forall k k' v v', em (encrypt k v) = Some (k', v') ->
                k = k' /\ v = v').

Lemma get_all_existing_encrypt_snd :
  forall l k (em: encryptionmap),
    encryptionmap_valid em ->
    (forall ev, In ev (map (encrypt k) l) -> em ev <> None) ->
    map snd (get_all_existing em (map (encrypt k) l)) = l.
Proof.
  induction l; simpl; intros; eauto.
  destruct_fresh (em (encrypt k a)); simpl in *.
  destruct p; simpl in *.
  rewrite IHl; eauto.
  unfold encryptionmap_valid in *; cleanup.
  specialize H1 with (1:= D); cleanup; eauto.
  exfalso; eapply H0; eauto.
Qed.

Lemma get_all_existing_encrypt_fst :
  forall l k (em: encryptionmap),
    encryptionmap_valid em ->
    (forall ev, In ev (map (encrypt k) l) -> em ev <> None) ->
    map fst (get_all_existing em (map (encrypt k) l)) = repeat k (length l).
Proof.
  induction l; simpl; intros; eauto.
  destruct_fresh (em (encrypt k a)); simpl in *.
  destruct p; simpl in *.
  rewrite IHl; eauto.
  unfold encryptionmap_valid in *; cleanup.
  specialize H1 with (1:= D); cleanup; eauto.
  exfalso; eapply H0; eauto.
Qed.

(*

Definition commit (addr_l data_l: list value) :=
  hdr <- read_header;
  let cur_hash := cur_hash hdr in
  let cur_count := cur_count hdr in
  let txns := txn_records hdr in
  let new_count := cur_count + (length addr_l + length data_l) in
  if (new_count <=? log_length) then
    new_key <- GetKey (addr_l++data_l);
    enc_data <- encrypt_all new_key (addr_l ++ data_l);
    _ <- write_consecutive (log_start + cur_count) enc_data;
    new_hash <- hash_all cur_hash enc_data;
    let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
    let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
    _ <- write_header new_hdr;
    Ret true
  else
    Ret false.

 *)

Lemma log_rep_extract_header_block:
  forall a hdr log_blocks,
    log_rep hdr log_blocks a =*=>
    exists* hdr_block,
      ((hdr_block_num |-> hdr_block *
       (hdr_block_num |-> hdr_block --* log_rep hdr log_blocks a)) *
       [[ decode_header (fst hdr_block) = hdr ]]).
Proof.
  unfold log_rep, log_rep_inner; intros.
  norml.
  exists hdr_block.
  apply sep_star_lift_apply'; eauto.
  setoid_rewrite <- septract_pimpl_r.
  apply sep_star_comm.
  apply septract_sep_star_extract.
  2: eauto.
  cancel.
  cancel.
Qed.

Lemma pred_array_split:
  forall V (l: list V) n a,
    a |=> l =*=> a |=> firstn n l * (a+n) |=> skipn n l.
Proof.
  induction l; intros.
  {
    simpl.
    rewrite firstn_nil, skipn_nil; simpl; cancel.
  }
  {
    destruct n; simpl.
    - rewrite add_0_r; cancel.
    - cancel.
      rewrite <- add_succ_comm; eauto.
  }
Qed.

Lemma pred_array_merge:
  forall V (l: list V) n a,
    a |=> firstn n l * (a+n) |=> skipn n l =*=> a |=> l.
Proof.
  induction l; intros.
  {
    simpl.
    rewrite firstn_nil, skipn_nil; simpl; cancel.
  }
  {
    destruct n; simpl.
    - rewrite add_0_r; cancel.
    - cancel.
      rewrite <- add_succ_comm; eauto.
      rewrite <- IHl; cancel.
  }
Qed.

Theorem log_write_consecutive_ok :
  forall vl start log_blocks hdr o d a,
    let log_index := start - log_start in
    let new_log_blocks :=
        firstn log_index log_blocks ++ vl ++
        skipn (log_index + length vl) log_blocks in  
    << o, d, a >>
      (log_rep hdr log_blocks a *
       [[ start >= log_start + cur_count hdr ]] *
       [[ start + length vl <= log_start + log_length ]])
      (write_consecutive start vl)
    << r, ar >>               
      (log_rep hdr new_log_blocks ar *
       [[ ar = a ]])%pred
      (exists* n,
         let partially_new_log_blocks :=
             firstn log_index log_blocks ++ firstn n vl ++
             skipn (log_index + n) log_blocks in
      log_rep hdr partially_new_log_blocks ar *
      [[ n <= length vl ]] *
      [[ ar = a ]])%pred.
Proof. Admitted. (*
  unfold log_rep; intros.
  eapply pre_impl.
  2:
    eassign
       (fun (_:oracle) a =>
          (exists* (log_blockset : list data)  (hdr_block : data),
             hdr_block_num |-> hdr_block *
             log_start |=> log_blockset *
             [[length log_blockset = log_length]] *
             [[hdr = decode_header (fst hdr_block)]] *
             [[log_blocks = map fst log_blockset]] *
             [[old_count hdr <= cur_count hdr]] *
             [[hash_valid (firstn (cur_count hdr) log_blocks) (cur_hash hdr)]] *
             [[hash_valid (firstn (old_count hdr) log_blocks) (old_hash hdr)]] *
             [[hashes_in_hashmap (snd a) hash0
                                 (firstn (cur_count hdr) log_blocks)]] *
             [[count_accurate hdr (length (txn_records hdr)) (cur_count hdr)]] *
   [[count_accurate hdr (old_txn_count hdr) (old_count hdr)]] *
   [[txns_valid hdr log_blocks (fst (fst a)) (snd (fst a))]] *
          [[start >= log_start + cur_count hdr]] *
          [[start + length vl <= log_start + log_length]]));
    unfold log_rep_inner; simpl; crush_pimpl.
  
  repeat (apply extract_exists; intros).
  eapply post_impl.
  eapply crash_impl.
  eapply pre_impl.
  eapply add_frame.
  apply write_consecutive_ok.
  {
    crush_pimpl.
    eassign (log_start |=> (firstn (start - log_start) v) *
             hdr_block_num |-> v0 *
             (start + length vl) |=> (skipn (length vl + (start - log_start)) v)).
    cancel.
    rewrite <- skipn_skipn.
    eapply pimpl_trans. 
    apply pred_array_split with (n:= start - log_start).
    cancel.
    rewrite Minus.le_plus_minus_r.
    eapply pimpl_trans. 
    apply pred_array_split with (n:= length vl).
    cancel.
    omega.
    apply firstn_length_l.
    rewrite skipn_length.
    omega.
  }
  {
    crush_pimpl.
    eassign n.
    eassign
      (firstn (start - log_start) v ++
       map_pointwise (map vsupd (firstn n vl))
       (firstn n (firstn (length vl) (skipn (start - log_start) v))) ++
        skipn (n + (start - log_start)) v).
    unfold log_rep_inner.
    repeat rewrite min_l; eauto.
    cancel.
    
    eapply pimpl_trans. 
    2: apply pred_array_merge with (n:= start - log_start).
    rewrite skipn_app_eq; [| rewrite firstn_length_l; omega].
    rewrite Minus.le_plus_minus_r; [| omega].
    rewrite firstn_app2; [| rewrite firstn_length_l; omega].
    cancel.

    eapply pimpl_trans. 
    2: apply pred_array_merge with (n:= n).
    setoid_rewrite firstn_app2.
    cancel.
    rewrite skipn_app_eq.
    rewrite le_plus_minus with (m:= length vl)(n:= n) at 3; eauto.
    rewrite skipn_firstn_comm.
    rewrite skipn_skipn.

    eapply pimpl_trans. 
    2: apply pred_array_merge with (n:= length vl - n).
    cancel.
    rewrite <- add_assoc.
    rewrite Minus.le_plus_minus_r; eauto.
    rewrite skipn_skipn.
    rewrite add_assoc.
    rewrite sub_add; eauto.
    admit.
    admit.
    {
      repeat rewrite app_length.
      rewrite firstn_length_l.
      rewrite skipn_length.
      admit.
      omega.
    }
    {
      repeat rewrite map_app.
      rewrite firstn_map_comm, skipn_map_comm.
      admit.
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    unfold txns_valid in *; intros.
    edestruct H6; eauto; cleanup.
    repeat split; eauto.
    repeat rewrite app_length;
    rewrite skipn_length.
    repeat rewrite firstn_length_l.
    omega.
    omega.
    rewrite map_length.
    setoid_rewrite H15; omega.
    rewrite skipn_app_l.
    admit.
    rewrite firstn_length_l.
    admit.
    rewrite map_length.
    setoid_rewrite H15; omega.
  }
  {
    intros; norm.
     eassign (firstn (start - log_start) v ++
       map_pointwise (map vsupd vl)
       (firstn (length vl) (skipn (start - log_start) v)) ++
       skipn (length vl + (start - log_start)) v).
     
     unfold log_rep_inner; crush_pimpl.
     rewrite <- skipn_skipn.
    eapply pimpl_trans. 
    2: apply pred_array_merge with (n:= start - log_start).
    rewrite firstn_app2.
    cancel.
    rewrite Minus.le_plus_minus_r.
    eapply pimpl_trans. 
    2: apply pred_array_merge with (n:= length vl).
    repeat rewrite skipn_app_eq.
    rewrite firstn_app2.
    cancel.
    admit.
    admit.
    rewrite firstn_length_l; omega.
    omega.
    rewrite firstn_length_l; omega.
    repeat rewrite app_length.
    rewrite firstn_length_l, skipn_length.
    admit.
    omega.
    {
      repeat rewrite map_app.
      rewrite firstn_map_comm, skipn_map_comm.
      assume (A : (map fst
    (map_pointwise (map vsupd vl)
                   (firstn (length vl) (skipn (start - log_start) v))) = vl)).
      rewrite A, add_comm; eauto.      
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    {
      rewrite firstn_app_l.
      rewrite firstn_firstn.
      rewrite min_l; eauto.
      omega.
      rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    {
      unfold txns_valid in *; intros.
      edestruct H6; eauto; cleanup.
      repeat split; eauto.
      repeat rewrite app_length;
      rewrite skipn_length.
      repeat rewrite firstn_length_l.
      omega.
      rewrite map_length.
      setoid_rewrite H15; omega.
      rewrite skipn_app_l.
      admit.
      rewrite firstn_length_l.
      admit.
      rewrite map_length.
      setoid_rewrite H15; omega.
    }
    intuition.
    Unshelve.
    admit.
Admitted.
*)

Hint Extern 1 (hoare_triple _ (write_consecutive _ _) _ _ _ _ _ _ _) => eapply log_write_consecutive_ok : specs.

Theorem read_header_ok :
  forall log_blocks hdr o d a,
    << o, d, a >>
      (log_rep hdr log_blocks a)
      (read_header)
    << r, ar >>
      (log_rep hdr log_blocks ar *
        [[ r = hdr ]] *
        [[ ar = a ]])%pred
      (log_rep hdr log_blocks ar *
       [[ ar = a ]])%pred.
Proof. 
  unfold read_header; intros.
  eapply pre_impl.
  2: eassign (fun (_: oracle) a => exists* hdr_block,
      ((hdr_block_num |-> hdr_block *
        (hdr_block_num |-> hdr_block --* log_rep hdr log_blocks a)) *
       [[ decode_header (fst hdr_block) = hdr ]]));
  intros; apply log_rep_extract_header_block.
  repeat (apply extract_exists; intros).
  step.
  { eassign (fun (_: oracle) a => log_rep hdr log_blocks a).
    crush_pimpl.
    apply septract_ptsto_merge.
  }

  {
    crush_pimpl.
    apply septract_ptsto_merge.
  }

  step.
Qed.

Hint Extern 1 (hoare_triple _ read_header _ _ _ _ _ _ _) => eapply read_header_ok : specs.

Theorem apply_log_ok :
  forall hdr log_blocks o d a,
    << o, d, a >>
      (log_rep hdr log_blocks a)
      (apply_log)
      << r, ar >>
      (exists* hdr', 
         log_rep hdr' log_blocks ar *
         [[ (r = true /\ hdr' = header0) \/
            (r= false /\ hdr' = hdr) ]] *     
         [[ ar = a ]])%pred
      (exists* hdr', 
         log_rep hdr' log_blocks ar *
         [[  hdr' = header0 \/  hdr' = hdr ]] *
         [[ ar = a ]])%pred.
Proof. Admitted.
  

Theorem commit_ok :
  forall hdr log_blocks addr_l data_l o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    let cur_hash := cur_hash hdr in
    let cur_count := cur_count hdr in
    let txns := txn_records hdr in
    
    << o, d, a >>
      (log_rep hdr log_blocks a *
       [[ encryptionmap_valid em ]])
      (commit addr_l data_l)
      << r, ar >>
      (exists* hdr' log_blocks', 
         log_rep hdr' log_blocks' ar *
         [[ (exists new_key,
               let new_count :=
                   cur_count + (length addr_l + length data_l) in
               let new_txn :=
                   Build_txn_record new_key
                                    cur_count
                                    (length addr_l)
                                    (length data_l) in
               let encrypted_blocks :=
                   map (encrypt new_key) (addr_l++data_l) in
               let new_log_blocks :=
                   firstn cur_count log_blocks ++
                          encrypted_blocks ++
                          skipn new_count log_blocks in 
               let new_hash :=
                   rolling_hash hash0 encrypted_blocks in
               let new_hdr :=
                   Build_header cur_hash
                                cur_count
                                (length txns)
                                new_hash new_count
                                (txns++[new_txn]) in
              r = true /\ hdr' = new_hdr /\ log_blocks' = new_log_blocks) \/
             (r= false /\ hdr' = hdr /\ log_blocks' = log_blocks) ]]      
       (* [[ ar = a ]] *) )%pred
      (exists* hdr' log_blocks',
         log_rep hdr' log_blocks' ar *
         [[ (exists new_key,
            let new_count := cur_count + (length addr_l + length data_l) in
            let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
            let encrypted_blocks := map (encrypt new_key) (addr_l++data_l) in
            let new_hash := rolling_hash hash0 encrypted_blocks in
            let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
               hdr' = new_hdr) \/ hdr' = hdr ]] 
          (* [[ ar = a ]] *) )%pred.
Proof. Admitted. (*
  unfold commit; step.
  { crush_pimpl.
    eassign hdr; cancel. 
  }
  {
    crush_pimpl. 
    eassign (fun (_: oracle) ax => log_rep hdr log_blocks ax); cancel.   }
  {
    crush_pimpl.
  }

  intros.
  destruct_fresh (PeanoNat.Nat.leb
              (cur_count r + (length addr_l + length data_l))
              LogParameters.log_length); [ apply leb_complete in D | apply leb_complete_conv in D].
  {
    step.
    { crush_pimpl.
      eassign (fun (_: oracle) ax => log_rep hdr log_blocks ax); cancel.
      (* doable *)
      admit. }
    
    intros; step.
    { crush_pimpl.
      eassign (fun (_: oracle) ax => log_rep hdr log_blocks ax); cancel.
      (* doable *)
      admit. }
    { crush_pimpl.
      (* doable *)
      admit. }

    step.
    {
      crush_pimpl.
      eassign log_blocks; cancel.
      rewrite map_length, app_length.  
      omega.
    }
    {
      crush_pimpl.
      eassign (fun (_:oracle) ax => log_rep hdr (firstn (log_start + cur_count hdr - log_start) log_blocks ++
     map (encrypt r0) (addr_l ++ data_l) ++
     skipn
       (log_start + cur_count hdr - log_start +
        length (map (encrypt r0) (addr_l ++ data_l))) log_blocks) ax).
      simpl; cancel.
    }
    {
      crush_pimpl.
    }

    step.
    {
      crush_pimpl.
      admit.
    }
    {
      crush_pimpl.
    
      unfold log_rep.
    intros.
    apply extract_exists; intros.

    step.
    eapply write_consecutive_ok.
    (* need a septract type lemma here *)
Abort.
*)

Theorem apply_txn_ok :
  forall txn log_blocks hdr txn_plain_blocks (disk_data: list data) o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    let key := txn_key txn in
    let start := txn_start txn in
    let addr_count := addr_count txn in
    let data_count := data_count txn in
    let txn_blocks := firstn (addr_count+data_count) (skipn start log_blocks) in
    let plain_addr_blocks := firstn addr_count txn_plain_blocks in
    let plain_data_blocks := skipn addr_count txn_plain_blocks in
    let addr_list := firstn data_count (blocks_to_addr_list plain_addr_blocks) in
    << o, d, a >>
      (log_rep hdr log_blocks a *
       addr_list |L> disk_data *
       [[ length disk_data = data_count ]] *
       [[ In txn (txn_records hdr) ]] *
       [[ txn_blocks = map (encrypt key) txn_plain_blocks ]] *
       [[ encryptionmap_valid em ]])
      (apply_txn txn log_blocks)
      << r, ar >>
      (log_rep hdr log_blocks ar *
       addr_list |L> (map_pointwise (map vsupd plain_data_blocks) disk_data) * 
       [[ ar = a ]])%pred
      (exists* vsl',
          log_rep hdr log_blocks ar *
          addr_list |L> vsl' *
          [[ ar = a ]])%pred.
Proof. Abort. (*
  unfold apply_txn; step.
  {
    unfold log_inner_rep.
    crush_pimpl.

    rewrite H3.
    rewrite get_all_existing_encrypt_snd; eauto.

    intros; unfold cur_txns_valid in *.
    specialize H8 with (1:= H4); cleanup.
    rewrite H3 in *.
    specialize H17 with (1:=H0); cleanup; congruence.

    unfold cur_txns_valid in *.
    specialize H8 with (1:= H4); cleanup.
    rewrite H3 in *.
    rewrite map_length.
    symmetry; apply get_all_existing_encrypt_fst; eauto.
    intros.
    unfold cur_txns_valid in *.
    specialize H8 with (1:= H17); cleanup; congruence.
  }

  {
    crush_pimpl.
    instantiate (1:= fun _ ax => firstn (data_count txn) (blocks_to_addr_list (firstn (addr_count txn) txn_plain_blocks)) |L> disk_data * log_inner_rep log_blocks hdr ax).
    simpl; cancel. }

  step.
  {
    crush_pimpl.
    rewrite get_all_existing_encrypt_snd; eauto.

    intros; unfold log_inner_rep, cur_txns_valid in *.
    destruct_lifts.
    specialize H22 with (1:= H7); cleanup.
    rewrite H6 in *.
    specialize H10 with (1:=H1); cleanup; congruence.
    
    destruct_lifts.
    destruct_lift H; cleanup.
    rewrite get_all_existing_encrypt_snd; eauto.
    
    unfold log_inner_rep, cur_txns_valid in *.
    destruct_lift H.
    specialize H11 with (1:= H7); cleanup.
    rewrite H6 in *.
    simpl in *.    
    rewrite skipn_length.
    erewrite <- map_length, <- H6.
    rewrite firstn_length_l.
    rewrite Minus.minus_plus; eauto.
    rewrite skipn_length.
    rewrite H19.
    unfold cur_count_accurate in *.
    rewrite H13.
    (* TODO: Figure out this goal *)
    admit.
      
      intros.
      unfold log_inner_rep, cur_txns_valid in *.
      destruct_lift H.
      specialize H12 with (1:= H7); cleanup.
      rewrite H6 in *.
      specialize H10 with (1:=H1); cleanup; congruence.

      destruct_lifts.
      unfold log_inner_rep, cur_txns_valid in *.
      destruct_lift H.
      specialize H11 with (1:= H7); cleanup.
      rewrite H6 in *.
      simpl in *.    
      rewrite skipn_length.
      rewrite get_all_existing_encrypt_snd; eauto.
      rewrite firstn_length_l.
      erewrite <- map_length, <- H6.
      rewrite firstn_length_l.
      rewrite Minus.minus_plus; eauto.
      rewrite skipn_length.
      rewrite H19.
      unfold cur_count_accurate in *.
      rewrite H13.
      (* TODO: Figure out this goal *)
      admit.

      cleanup.
Abort.
*)