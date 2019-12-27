Require Import String Datatypes.
Require Import Primitives BatchOperations Layer1.
Require Import Log.Definitions.

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
      
      rewrite 
      get_all_existing_length.
    
    