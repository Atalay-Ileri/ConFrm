Require Import String Datatypes Omega.
Require Import Primitives Layer1.
Require Import BatchOperations.Definitions.

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
    eapply pre_impl.
    eapply post_impl.
    eapply crash_impl.
    apply ret_ok.
    intros; cancel.
    exists 0; simpl; eauto.
    intros; cancel.
    simpl; cancel.
  }

  {
    cleanup. destruct a0, p.
    simpl encrypt_all; simpl fst; simpl snd.
    eapply bind_ok.
    { intros; eapply pre_impl; [ apply (@encrypt_ok _ _ _ k a) |intros; simpl in *; cancel]. }
    { intros; simpl. instantiate(1:= fun _ => emp); simpl; cancel. }
    { intros; simpl; cancel; exists 0; simpl; eauto. }
    
    intros; cleanup.
    eapply bind_ok.
    { intros; eapply pre_impl; try apply IHvl.
      intros; simpl in *.
      repeat destruct_lifts; cleanup; cancel. }
    { intros; simpl in *; cancel.
      instantiate (1:= fun _ => emp); simpl; cancel.  }
    { intros; simpl in *; repeat destruct_lifts; cleanup;
      simpl; cancel; simpl; exists (S n); eauto. }
    { intros.
      eapply pre_impl.
      eapply post_impl.
      eapply crash_impl.
      apply ret_ok.
      { intros; cancel.
        simpl in *; repeat destruct_lifts; cleanup.
        exists (S (length vl)); simpl.
        rewrite firstn_map_comm.
        rewrite firstn_exact; eauto. }
      { intros; simpl in *; repeat destruct_lifts; cleanup; cancel. }
      { intros; simpl; cancel. }
    }
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
  {
    eapply pre_impl.
    eapply post_impl.
    eapply crash_impl.
    apply ret_ok.
    all: intros; cancel.
  }

  {
    cleanup. destruct a0, p.
    destruct_fresh (m a).
    {
      destruct p.
      simpl decrypt_all; simpl fst; simpl snd.
      eapply bind_ok.
      { intros; eapply pre_impl; [ apply (@decrypt_ok _ _ _ k a) |intros; simpl in *; cancel].
        cleanup; simpl in *.
        inversion H2; eauto.
        cleanup; simpl in *.
        inversion H2; inversion H3; eauto. }
      { intros; simpl. instantiate(1:= fun _ => emp); simpl; cancel. }
      { intros; simpl; cancel. }
      
      intros; cleanup.
      eapply bind_ok.
      { intros; eapply pre_impl; try apply IHevl.
        intros; simpl in *.
        repeat destruct_lifts; cleanup; cancel. }
      { intros; simpl in *; cancel.
        instantiate (1:= fun _ => emp); simpl; cancel.  }
      { intros; simpl in *; repeat destruct_lifts; cleanup;
        simpl; cancel. }

      intros.
      eapply pre_impl.
      eapply post_impl.
      eapply crash_impl.
      apply ret_ok.
      { intros; cancel.
        simpl in *; repeat destruct_lifts; cleanup; eauto. }
      { intros; simpl in *; repeat destruct_lifts; cleanup; cancel. }
      { intros; simpl; cancel. }
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
    eapply pre_impl.
    eapply post_impl.
    eapply crash_impl.
    apply ret_ok.
    intros; cancel.
    exists 0; simpl; eauto.
    intros; cancel.
    simpl; cancel.
  }

  {
    cleanup. destruct a0, p.
    simpl hash_all; simpl fst; simpl snd.
    eapply bind_ok.
    { intros; eapply pre_impl; [ apply (@hash_ok _ _ _ h a) |intros; simpl in *; cancel]. }
    { intros; simpl. instantiate(1:= fun _ => emp); simpl; cancel. }
    { intros; simpl; cancel; exists 0; simpl; eauto. }
  
    intros; cleanup.
    eapply bind_ok.
    { intros; eapply pre_impl; try apply IHvl.
      intros; simpl in *.
      repeat destruct_lifts; cleanup; cancel. }
    { intros; simpl in *; cancel.
      instantiate (1:= fun _ => emp); simpl; cancel.  }
    { intros; simpl in *; repeat destruct_lifts; cleanup;
      simpl; cancel; simpl; exists (S n); eauto. }

    { intros.
      eapply pre_impl.
      eapply post_impl.
      eapply crash_impl.
      apply ret_ok.
      { intros; cancel.
        simpl in *; repeat destruct_lifts; cleanup.
        exists (S (length vl)); simpl.
        rewrite firstn_rolling_hash_list_comm.
        rewrite firstn_hash_and_pair_comm.
        rewrite firstn_exact; eauto. }
      { intros; simpl in *; repeat destruct_lifts; cleanup; cancel. }
      { intros; simpl; cancel. }
    }
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
  {
    eapply post_impl.
    eapply crash_impl.
    eapply pre_impl.
    apply ret_ok.
    all: simpl in *; intros; repeat destruct_lifts; cancel.
    all: match goal with
         |[H: length _ = 0 |- _] =>
          apply length_zero_iff_nil in H
         end; cleanup; simpl; eauto.
  }

  {
    cleanup.
    destruct vl.
    {
      unfold hoare_triple; simpl; intros.
      repeat destruct_lifts; congruence.
    }
    
    simpl read_consecutive; simpl fst; simpl snd.
    eapply bind_ok.
    { intros; eapply pre_impl.
      eapply add_frame; apply (@read_ok _ _ start).
      simpl; cancel.
    }
    { intros; simpl.
      instantiate (1:= fun ar => start |=> (d0::vl)); simpl; cancel. }
    { intros; simpl; cancel. }
    
    intros; cleanup.
      eapply bind_ok.
      { intros; eapply pre_impl.
        eapply add_frame; try apply IHn.
        intros; simpl in *.
        repeat destruct_lifts; cleanup; cancel.
        destruct_lift H; cleanup; eauto.
      }
      { intros; simpl in *; cancel.
        instantiate (1:= fun _ => start |=> (d0::vl)); simpl; cancel.  }
      { intros; simpl in *; repeat destruct_lifts; cleanup;
        simpl; cancel.
      destruct_lift H0; eauto. }

      intros.
      eapply pre_impl.
      eapply post_impl.
      eapply crash_impl.
      eapply add_frame.
      apply ret_ok.
      { intros; cancel.
        simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
        cleanup; eauto. }
      { intros; simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
        cleanup; cancel. }
      { intros; simpl; cancel. }
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
      [[ ar = a ]]).
Proof.
  unfold vsupd; induction vl; intros; cleanup.
  {
    eapply post_impl.
    eapply crash_impl.
    eapply pre_impl.
    apply ret_ok.
    all: simpl in *; intros; repeat destruct_lifts; cancel.
    all: match goal with
         |[H: length _ = 0 |- _] =>
          apply length_zero_iff_nil in H
         end; cleanup; simpl; eauto.
    rewrite firstn_nil, skipn_nil; simpl.
    cancel.
  }

  {
    cleanup.
    destruct vsl.
    {
      unfold hoare_triple; simpl; intros.
      repeat destruct_lifts; congruence.
    }
    
    simpl write_consecutive; simpl fst; simpl snd.
    eapply bind_ok.
    { intros; eapply pre_impl.
      eapply add_frame; apply write_ok.
      simpl; cancel.
    }
    { intros; simpl.
      instantiate (1:= fun ar => S start |=> vsl * start |-> (a, fst d0 :: snd d0)); simpl; cancel. }
    { intros; simpl; cancel.
      eassign 0; simpl; cancel.
      rewrite Nat.add_0_r; cancel. }
    

      intros.
      eapply pre_impl.
      eapply post_impl.
      eapply crash_impl.
      eapply add_frame.
      apply IHvl.
      { intros; cancel.
        eassign (S n); eassign vsl; simpl.
        rewrite Nat.add_succ_r; cancel.
        simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
        cleanup; eauto. }
      { intros; simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
        cleanup; cancel. }
      { intros; simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
        cleanup; cancel. }
      Unshelve.
      eauto.
    }
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
    eapply post_impl.
    eapply crash_impl.
    eapply pre_impl.
    eapply add_frame.
    apply ret_ok.
    all: simpl in *; intros; repeat destruct_lifts; cancel; cleanup.
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
  
  simpl write_batch; simpl fst; simpl snd.
  eapply bind_ok.
  { intros; eapply pre_impl.
    eapply add_frame; apply write_ok.
    simpl; cancel.
  }
  { intros; simpl.
    instantiate (1:= fun ar => al |L> vsl * a |-> (v, fst d0 :: snd d0)); simpl; cancel. }
  { intros; simpl; cancel.
    eassign 0; simpl; cancel. }    
  
  intros.
  eapply pre_impl.
  eapply post_impl.
  eapply crash_impl.
  eapply add_frame.
  apply IHal.
  { intros; cancel.
    eassign (S n); eassign vsl; simpl.
    cancel.
      simpl in *; destruct_lift H;
        destruct_lift H0; destruct_lift H2;
          cleanup; eauto. }
  { intros; simpl in *; destruct_lift H;
      destruct_lift H0; destruct_lift H2;
        cleanup; cancel. }
  { intros; simpl in *; destruct_lift H;
      destruct_lift H0; destruct_lift H2;
        cleanup; cancel. }
Qed.