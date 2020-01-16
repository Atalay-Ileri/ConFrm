Require Import Omega.
Require Import Primitives DiskLayer.
Require Import BatchOperations.Definitions.
Require Import Datatypes.

Theorem encrypt_all_ok :
  forall vl k o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    << o, d, a >>
    ([[ consistent_with_upds em
             (map (encrypt k) vl) (map (fun v=> (k,v)) vl) ]])
      (encrypt_all k vl)
    << r, ar >>
      ([[ r = map (encrypt k) vl ]] *
       [[ ar = (kl, upd_batch em r (map (fun v => (k, v)) vl), hm) ]])%pred
      ([[ exists n, ar = (kl, upd_batch em (firstn n (map (encrypt k) vl)) (map (fun v => (k, v)) (firstn n vl)), hm) ]]).
Proof.
  induction vl; do 5 intro; cleanup.
  {
    step.
    intros; cancel.
    exists 0; simpl; eauto.
  }

  {
    cleanup. destruct a0, p.
    simpl fst; simpl snd.
    step.
    { intros; simpl. instantiate(1:= fun _ _ => emp); simpl; cancel. }
    { intros; simpl; cancel; exists 0; simpl; eauto. }
    
    intros; cleanup.
    step.
    { apply IHvl. }
    { crush_pimpl. }
    { crush_pimpl. instantiate (1:= fun _ _ => emp); simpl; cancel.  }
    { crush_pimpl. simpl; exists (S n); eauto. }
    
    step.
    { crush_pimpl.
      exists (S (length vl)); simpl.
      rewrite firstn_map_comm.
      rewrite firstn_exact; eauto. }
  }
Qed.

Theorem decrypt_all_ok :
  forall evl k o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    let kvl := get_all_existing em evl in
    let vl := map snd kvl in
    << o, d, a >>
    ([[ evl = map (encrypt k) vl ]] *
     [[ repeat k (length evl) = map fst kvl ]])
      (decrypt_all k evl)
    << r, ar >>
      ([[ r = vl ]] *
       [[ ar = a ]])%pred
      ([[ ar = a ]]).
Proof.
  induction evl; intros; cleanup.  
  { step. }
  {
    cleanup. destruct a0, p.
    destruct_fresh (m a).
    {
      destruct p.
      simpl fst; simpl snd.
      step.
      { crush_pimpl; cleanup; simpl in *; eauto. }
      { instantiate (1:= fun _ _ => emp); simpl; cancel. }
      
      intros; cleanup.
      step.
      { apply IHevl. }
      { crush_pimpl. }
      { crush_pimpl.
        instantiate (1:= fun _ _ => emp); simpl; cancel. }
      { crush_pimpl. }

      step.
    }
    
    {
      unfold hoare_triple; intros.
      destruct_lifts; cleanup.
      assert (A: length (a :: evl) =
        length (map (encrypt k)
                    (map snd (get_all_existing m evl))))
        by (cleanup; eauto).
      simpl in A.
      repeat rewrite map_length in A.
      pose proof (@get_all_existing_length_le _ _ _ m evl).
      omega.
    }
  }
Qed.

Theorem hash_all_ok :
  forall vl h o d a,
    let kl := fst (fst a) in
    let em := snd (fst a) in
    let hm := snd a in
    let rhl := rolling_hash_list h vl in
    let hvl := hash_and_pair h vl in
    << o, d, a >>
    ([[ consistent_with_upds hm rhl hvl ]])
      (hash_all h vl)
    << r, ar >>
      ([[ r = rolling_hash h vl ]] *
       [[ ar = (kl, em, upd_batch hm rhl hvl) ]])%pred
      ([[ exists n, ar = (kl, em, upd_batch hm (firstn n rhl) (firstn n hvl)) ]]).
Proof.
  induction vl; intros; cleanup.
  {
    step.
    intros; cancel.
    exists 0; simpl; eauto.
  }

  {
    cleanup. destruct a0, p.
    simpl fst; simpl snd.
    step.
    { intros; simpl. instantiate(1:= fun _ _ => emp); simpl; cancel. }
    { intros; simpl; cancel; exists 0; simpl; eauto. }
  
    intros; cleanup.
    step.
    {  apply IHvl. }
    { crush_pimpl. }
    { crush_pimpl.
      instantiate (1:= fun _ _ => emp); simpl; cancel.  }
    { crush_pimpl; simpl; exists (S n); eauto. }

    step.
    { crush_pimpl.
      exists (S (length vl)); simpl.
      rewrite firstn_rolling_hash_list_comm.
      rewrite firstn_hash_and_pair_comm.
      rewrite firstn_exact; eauto. } 
  }
Qed.

Theorem read_consecutive_ok :
  forall n start vl o d a,
    << o, d, a >>
      (start |=> vl *
      [[ length vl = n ]])
      (read_consecutive start n)
    << r, ar >>
      (start |=> vl *
       [[ r = map fst vl ]] *
       [[ ar = a ]])%pred
      (start |=> vl *
      [[ ar = a ]]).
Proof.
  induction n; intros; cleanup.
  { step. }
  {
    cleanup.
    destruct vl.
    {
      unfold hoare_triple; simpl; intros.
      repeat destruct_lifts; congruence.
    }
    
    simpl fst; simpl snd.
    step.
    { intros; simpl.
      instantiate (1:= fun _ _ => start |=> (d0::vl)); simpl; cancel. }
    
    intros; cleanup.
    step.
    { apply IHn. }
    { crush_pimpl. }
    { crush_pimpl.
      instantiate (1:= fun _ _ => start |=> (d0::vl)); simpl; cancel. }
    { crush_pimpl. }
    
    step.
  }
Qed.

Theorem write_consecutive_ok :
  forall vl start vsl o d a,
    << o, d, a >>
      (start |=> vsl *
      [[ length vsl = length vl ]])
      (write_consecutive start vl)
    << r, ar >>
      (start |=> (map_pointwise (map vsupd vl) vsl) *
       [[ ar = a ]])%pred
      (exists* n, start |=> (map_pointwise (map vsupd (firstn n vl)) (firstn n vsl)) *
             (start + n) |=> skipn n vsl *
             [[ n <= length vl ]] *
             [[ ar = a ]]).
Proof.
  unfold vsupd; induction vl; intros; cleanup.
  {
    step.
    crush_pimpl.
    rewrite firstn_nil, skipn_nil; simpl; cancel.
  }
  {
    cleanup.
    destruct vsl.
    {
      unfold hoare_triple; simpl; intros.
      repeat destruct_lifts; congruence.
    }
    
    simpl fst; simpl snd.
    step.
    { intros; simpl.
      instantiate (1:= fun _ _ => S start |=> vsl * start |-> (a, fst d0 :: snd d0)); simpl; cancel. }
    { intros; simpl; cancel.
      eassign 0; simpl; cancel.
      rewrite Nat.add_0_r; cancel. }
    
    step.
    { apply IHvl. }
    { crush_pimpl. }
    { intros; simpl.
      instantiate (1:= fun _ _ => S start |=> map_pointwise
        (map (fun v vs => (v, fst vs :: snd vs)) vl) vsl *
         start |-> (a, fst d0 :: snd d0)); simpl; cancel. }
    { crush_pimpl.
      eassign (S n); simpl.
      rewrite Nat.add_succ_r; cancel.
      rewrite min_l; eauto; cancel. }

    step.
    { crush_pimpl.
      eassign (S (length vsl)); simpl; cancel.
      rewrite min_l; try omega.
      repeat rewrite firstn_oob; try omega.
      rewrite skipn_oob; try omega.
      simpl; cancel.
    }
  }
  Unshelve.
  eauto.
Qed.

Theorem write_batch_ok :
  forall al vl vsl o d a,
    << o, d, a >>
      (al |L> vsl *
       [[ length vsl = length vl ]] *
       [[ length al = length vl ]])
      (write_batch al vl)
    << r, ar >>
      (al |L> (map_pointwise (map vsupd vl) vsl) *
       [[ ar = a ]])%pred
      (exists* n, (firstn n al) |L> (map_pointwise (map vsupd (firstn n vl)) (firstn n vsl)) *
             (skipn n al) |L> (skipn n vsl) *  
      [[ ar = a ]]).
Proof.
  unfold vsupd; induction al; intros; cleanup.
  {
    step.
    crush_pimpl.
    eassign 0; simpl; cancel.
  }

  
  cleanup.
  destruct vl.
  {
    unfold hoare_triple; simpl; intros.
    repeat destruct_lifts; congruence.
  }
  destruct vsl.
  {
    unfold hoare_triple; simpl; intros.
    repeat destruct_lifts; congruence.
  }
  
  simpl fst; simpl snd.
  step.
  { intros; simpl.
    instantiate (1:= fun _ _ => al |L> vsl * a |-> (v, fst d0 :: snd d0)); simpl; cancel. }
  { crush_pimpl.
    eassign 0; simpl; cancel. }    
  
  step.
  { apply IHal. }
  { crush_pimpl. }
  { crush_pimpl.
    instantiate (1:= fun _ _ =>
       al |L> map_pointwise
             (map (fun v0 vs => (v0, fst vs :: snd vs)) vl) vsl *
              a |-> (v, fst d0 :: snd d0)); simpl; cancel. }
  { crush_pimpl.
    eassign (S n); simpl; cancel. }

  step.
  { crush_pimpl.
    eassign (S (length vl)); simpl; cancel.
    repeat rewrite firstn_oob; try omega.
    rewrite skipn_oob; try omega.
    simpl; cancel.
  }
Qed.

Hint Extern 1 (hoare_triple _ (encrypt_all _ _) _ _ _ _ _ _ _) => eapply encrypt_all_ok : specs.
Hint Extern 1 (hoare_triple _ (decrypt_all _ _) _ _ _ _ _ _ _) => eapply decrypt_all_ok : specs.
Hint Extern 1 (hoare_triple _ (hash_all _ _) _ _ _ _ _ _ _) => eapply hash_all_ok : specs.
Hint Extern 1 (hoare_triple _ (read_consecutive _ _) _ _ _ _ _ _ _) => eapply read_consecutive_ok : specs.
Hint Extern 1 (hoare_triple _ (write_consecutive _) _ _ _ _ _ _ _) => eapply write_consecutive_ok : specs.
Hint Extern 1 (hoare_triple _ (write_batch _ _) _ _ _ _ _ _ _) => eapply write_batch_ok : specs.