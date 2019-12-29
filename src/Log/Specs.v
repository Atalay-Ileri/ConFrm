Require Import Primitives BatchOperations Layer1.
Require Import Log.Definitions.
Require Import Datatypes.

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
Theorem read_header_ok :
  forall hdr o d a,
    << o, d, a >>
      (log_rep hdr a)
      (read_header)
    << r, ar >>
      (log_rep hdr ar *
        [[ r = hdr ]] *
        [[ ar = a ]])%pred
      (log_rep hdr ar *
       [[ ar = a ]])%pred.
Proof. Admitted. (*
  unfold read_header; intros.
  unfold log_rep, log_inner_rep.
  repeat (apply extract_exists; intros).
  step.
  { eassign (fun a => log_rep hdr a).
    unfold log_rep, log_inner_rep; crush_pimpl.
    cleanup; cancel.
  }

  { crush_pimpl.
    cleanup; cancel. }

  step.
  { unfold log_rep, log_inner_rep; crush_pimpl. }
  { unfold log_rep, log_inner_rep; crush_pimpl. }
Qed.
*)
Hint Extern 1 (hoare_triple _ read_header _ _ _ _ _ _ _) => eapply read_header_ok : specs.

Theorem commit_ok :
  forall hdr addr_l data_l o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    let cur_hash := cur_hash hdr in
    let cur_count := cur_count hdr in
    let txns := txn_records hdr in
    
    << o, d, a >>
      (log_rep hdr a *
       [[ encryptionmap_valid em ]])
      (commit addr_l data_l)
      << r, ar >>
      (exists* hdr',
         log_rep hdr' ar *
         [[ (exists new_key,
            let new_count := cur_count + (length addr_l + length data_l) in
            let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
            let encrypted_blocks := map (encrypt new_key) (addr_l++data_l) in
            let new_hash := rolling_hash hash0 encrypted_blocks in
            let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
              r = true /\ hdr' = new_hdr) \/
             (r= false /\ hdr' = hdr) ]]      
       (* [[ ar = a ]] *) )%pred
      (exists* hdr',
         log_rep hdr' ar *
         [[ (exists new_key,
            let new_count := cur_count + (length addr_l + length data_l) in
            let new_txn := Build_txn_record new_key cur_count (length addr_l) (length data_l) in
            let encrypted_blocks := map (encrypt new_key) (addr_l++data_l) in
            let new_hash := rolling_hash hash0 encrypted_blocks in
            let new_hdr := Build_header cur_hash cur_count (length txns) new_hash new_count (txns++[new_txn]) in
               hdr' = new_hdr) \/ hdr' = hdr ]] 
          (* [[ ar = a ]] *) )%pred.
Proof.
  unfold commit; step.
  { crush_pimpl.
    eassign (fun (_: oracle) ax => log_rep hdr ax); cancel. }

  intros.
  destruct (PeanoNat.Nat.leb
              (cur_count r + (length addr_l + length data_l))
              LogParameters.log_length).
  {
    step.
    { crush_pimpl.
      eassign (fun (_: oracle) ax => log_rep hdr ax); cancel.
      (* doable *)
      admit. }
    
    intros; step.
    { crush_pimpl.
      eassign (fun (_: oracle) ax => log_rep hdr ax); cancel.
      (* doable *)
      admit. }
    { crush_pimpl.
      (* doable *)
      admit. }

    unfold log_rep.
    intros.
    apply extract_exists; intros.
    step.
    eapply write_consecutive_ok.
    (* need a septract type lemma here *)

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
      (log_inner_rep log_blocks hdr kl em hm *
       addr_list |L> disk_data *
       [[ length disk_data = data_count ]] *
       [[ In txn (txn_records hdr) ]] *
       [[ txn_blocks = map (encrypt key) txn_plain_blocks ]] *
       [[ encryptionmap_valid em ]])
      (apply_txn txn log_blocks)
      << r, ar >>
      (log_inner_rep log_blocks hdr kl em hm *
       addr_list |L> (map_pointwise (map vsupd plain_data_blocks) disk_data) * 
       [[ ar = a ]])%pred
      (exists* vsl',
          log_inner_rep log_blocks hdr kl em hm *
          addr_list |L> vsl' *
          [[ ar = a ]])%pred.
Proof.
  unfold apply_txn; intros.
  destruct a, p; simpl fst; simpl snd.

  eapply bind_ok.
  {
    intros.
    eapply pre_impl.
    eapply add_frame.
    apply decrypt_all_ok.
    simpl.
    eassign (log_inner_rep log_blocks hdr l e h * firstn (data_count txn) (blocks_to_addr_list (firstn (addr_count txn) txn_plain_blocks)) |L> disk_data).
    unfold log_inner_rep.
    intros; cancel.
    all: try eauto.
    rewrite H4.

    rewrite get_all_existing_encrypt_snd; eauto.
    intros.
    unfold cur_txns_valid in *.
    specialize H9 with (1:= H5); cleanup.
    rewrite H4 in *.
    specialize H9 with (1:=H); cleanup; congruence.

    unfold cur_txns_valid in *.
    specialize H9 with (1:= H5); cleanup.
    rewrite H4 in *.
    rewrite map_length.
    symmetry; apply get_all_existing_encrypt_fst; eauto.
    intros.
    unfold cur_txns_valid in *.
    specialize H7 with (1:= H9); cleanup; congruence.
  }

  { intros; simpl; cancel.
    instantiate (1:= fun ax => firstn (data_count txn) (blocks_to_addr_list (firstn (addr_count txn) txn_plain_blocks)) |L> disk_data * log_inner_rep log_blocks hdr (fst (fst ax)) (snd (fst ax)) (snd ax) ).
    simpl; cancel. }
  { intros; simpl; cancel. }

  intros.
  eapply bind_ok.
  { intros.
    eapply pre_impl.
    eapply add_frame.
    apply write_batch_ok.

    {
      simpl; intros; cancel.
      repeat destruct_lifts; cleanup.
      cancel.
      destruct_lift H; cleanup.
      rewrite get_all_existing_encrypt_snd; eauto.
      cancel.
      intros.
      unfold log_inner_rep, cur_txns_valid in *.
      destruct_lift H.
      specialize H12 with (1:= H7); cleanup.
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


      
      rewrite 
      get_all_existing_length.
    
    