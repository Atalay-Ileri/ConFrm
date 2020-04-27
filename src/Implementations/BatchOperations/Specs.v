(*
Require Import Omega.
Require Import Framework DiskLayer.
Require Import BatchOperations.Definitions.
Require Import Datatypes.

Opaque oracle_ok.

Theorem encrypt_all_ok :
  forall vl k o s F,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
    PRE: (F * [[ consistent_with_upds em
             (map (encrypt k) vl) (map (fun v=> (k,v)) vl) ]] >> s)
    PROG: (encrypt_all k vl)
    << r, s' >>
    POST: (F * [[ r = map (encrypt k) vl ]] *
           [[ fst s' = (kl, upd_batch em r (map (fun v => (k, v)) vl), hm) ]] >> s')%pred
    CRASH: (F * [[ exists n, fst s' = (kl, upd_batch em (firstn n (map (encrypt k) vl)) (map (fun v => (k, v)) (firstn n vl)), hm) ]] >> s').
Proof.
  induction vl; intros; cleanup.
  {
    step.
    simpl; intros; cleanup; eauto.
    pred_apply; cancel.
    exists 0; simpl; eauto.
    simpl in *; intros; cleanup.
    pred_apply; cancel.
  }

  {
    cleanup. 
    step.
    { intros; simpl; pred_apply; cancel. }
    { intros; simpl in *.
      instantiate (1:= fun s => F  >> s).
      simpl; pred_apply; cancel.
    }
    { intros; simpl in *.
      simpl; pred_apply; cancel.
      exists 0; simpl in *; eauto.
    } 
    
    intros; cleanup.
    step.
    { destruct_lifts; intros;
      pred_apply; cancel; eauto;
      setoid_rewrite H10; simpl; eauto. }
    { simpl in *; intros.
      instantiate (1:= fun s => F >> s).
      simpl; pred_apply; cancel.
    }
    { simpl; intros; pred_apply; cancel.
      destruct_lifts; cleanup.
      exists (S x); simpl; setoid_rewrite H13; simpl; eauto.      
    }
    
    intros; simpl in *.
    destruct_lifts; cleanup.
    step.
    {
      simpl; intros; cleanup.
      pred_apply; cancel.
      exists (S (length vl)); simpl.
      rewrite firstn_map_comm.
      rewrite firstn_exact; eauto.
      cleanup; eauto.
      setoid_rewrite H14; simpl; eauto.
    }
    {
      simpl in *; intros; cleanup.
      pred_apply; cancel.
      cleanup; setoid_rewrite H14; simpl; eauto.
    }
  }
  Unshelve.
  all: exact DiskLang.
Qed.

Theorem decrypt_all_ok :
  forall evl k o s F,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    let kvl := get_all_existing em evl in
    let vl := map snd kvl in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
    PRE: (F * [[ evl = map (encrypt k) vl ]] *
     [[ repeat k (length evl) = map fst kvl ]] >> s)
    PROG: (decrypt_all k evl)
    << r, s' >>
    POST: (F * [[ r = vl ]] *
       [[ fst s' = fst s ]] >> s')%pred
    CRASH: (F * [[ fst s' = fst s ]] >> s').
Proof.
  induction evl; intros; cleanup.  
  { step.
    all: simpl; intros; cleanup; try (pred_apply; cancel).
  }
  {
    cleanup. destruct s, p, p.
    destruct_fresh (m a).
    {
      destruct p.
      simpl fst; simpl snd.
      step.
      { simpl in *; intros; cleanup.
        destruct_lifts.
        inversion H3; inversion H4.
        pred_apply; cancel. }
      { instantiate (1:= fun s => F >> s); simpl; intros; cleanup.
        pred_apply; cancel. }
      { simpl in *; intros; pred_apply; cancel. }
      
      intros; cleanup.
      step.
      { simpl; intros; destruct_lifts; simpl in *; cleanup.
        simpl in *.
        setoid_rewrite H10; clear H10.
        inversion H11; inversion H12.
        pred_apply; cancel. }
      { instantiate (1:= fun s => F >> s); simpl; intros; cleanup.
        pred_apply; cancel. }
      { simpl in *; intros; destruct_lifts; cleanup.
        pred_apply; cancel. }

      simpl in *; intros; destruct_lifts; cleanup.
      step.
       {
         simpl; intros; cleanup.
         pred_apply; cancel.
       }
       {
         simpl in *; intros.
         intuition; subst.
         pred_apply; cancel.
         setoid_rewrite H11; simpl; eauto.
         clear H13 H14; cleanup; eauto.
       }
    }
    
    {
      eapply pre_impl_false; intros.
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
  Unshelve.
  all: exact DiskLang.
Qed.

Theorem hash_all_ok :
  forall vl h o s F,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    let rhl := rolling_hash_list h vl in
    let hvl := hash_and_pair h vl in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
    PRE: (F * [[ consistent_with_upds hm rhl hvl ]] >> s)
    PROG: (hash_all h vl)
    << r, s' >>
    POST: (F * [[ r = rolling_hash h vl ]] *
           [[ fst s' = (kl, em, upd_batch hm rhl hvl) ]] >> s')%pred
    CRASH: (F * [[ exists n, fst s' = (kl, em, upd_batch hm (firstn n rhl) (firstn n hvl)) ]] >> s').
Proof.
  induction vl; intros; cleanup.
  {
    step.
    all: simpl; intros; cleanup; try (pred_apply; cancel).
    exists 0; simpl; eauto.
  }

  {
    cleanup. destruct s, p, p.
    simpl fst; simpl snd.
    step.
    { simpl in *; intros; cleanup.
      pred_apply; cancel; cleanup; eauto. }
    { instantiate (1:= fun s => F >> s); simpl; intros; cleanup.
      pred_apply; cancel. }
    { simpl in *; intros; pred_apply; cancel.
      exists 0; simpl; eauto. }
  
    intros; cleanup.
    step.
    { simpl; intros; destruct_lifts; simpl in *; cleanup.
      simpl in *.
      setoid_rewrite H10; clear H10.
      pred_apply; cancel. }
    { instantiate (1:= fun s => F >> s); simpl; intros; cleanup.
      pred_apply; cancel. }
    { simpl in *; intros; destruct_lifts; cleanup.
      pred_apply; cancel.
      exists (S x); setoid_rewrite H10; simpl; eauto. }

     simpl in *; intros; destruct_lifts; cleanup.
      step.
       {
         simpl; intros; cleanup.
         pred_apply; cancel.
         cleanup; eauto.
         exists (S (length vl)); simpl.
         rewrite firstn_rolling_hash_list_comm.
         rewrite firstn_hash_and_pair_comm.
         rewrite firstn_exact; eauto.         
         setoid_rewrite H11; simpl; eauto.
       }
       {
         simpl in *; intros.
         intuition.
         pred_apply; cancel.
         cleanup.
         setoid_rewrite H11; simpl; eauto.
       }
  }
  Unshelve.
  all: exact DiskLang.
Qed.

Theorem read_consecutive_ok :
  forall n start vl o s F,
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
      PRE: (F * start |=> vl *
      [[ length vl = n ]] >> s)
      PROG: (read_consecutive start n)
    << r, s' >>
      POST: (F * start |=> vl *
       [[ r = map fst vl ]] *
       [[ fst s' = fst s ]] >> s')%pred
      CRASH: (F *start |=> vl *
      [[ fst s' = fst s ]] >> s').
Proof. Admitted. (*
  induction n; intros; cleanup.
  {
    step.
    instantiate (1:=fun s' => F * start |=> vl * [[fst s' = fst s]] >> s').
    all: simpl; intros; cleanup; try (pred_apply; cancel).
    destruct_lifts; cleanup; simpl; eauto.
  }
  
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
      pred_apply; cancel. }
    
    intros; cleanup.
    step.
    { apply IHn. }
    { crush_pimpl. }
    { crush_pimpl.
      instantiate (1:= fun _ _ => start |=> (d0::vl)); simpl; cancel. }
    { crush_pimpl. }
    
    step.
  }
Qed. *)

Theorem write_consecutive_ok :
  forall vl start vsl o s F,
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
      PRE: (F * start |=> vsl *
      [[ length vsl = length vl ]] >> s)
      PROG: (write_consecutive start vl)
    << r, s' >>
      POST: (F * start |=> (map_pointwise (map vsupd vl) vsl) *
       [[ fst s' = fst s ]] >> s')%pred
      CRASH: ((exists* n, F * start |=> (map_pointwise (map vsupd (firstn n vl)) (firstn n vsl)) *
             (start + n) |=> skipn n vsl *
             [[ n <= length vl ]] *
             [[ fst s' = fst s ]]) >> s').
Proof. Admitted. (*
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
Qed. *)

Theorem write_batch_ok :
  forall al vl vsl o s F,
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
      PRE: (F * al |L> vsl *
       [[ length vsl = length vl ]] *
       [[ length al = length vl ]] >> s)
      PROG: (write_batch al vl)
    << r, s' >>
      POST: (F * al |L> (map_pointwise (map vsupd vl) vsl) *
       [[ fst s' = fst s ]] >> s')%pred
      CRASH: ((exists* n, F * (firstn n al) |L> (map_pointwise (map vsupd (firstn n vl)) (firstn n vsl)) *
             (skipn n al) |L> (skipn n vsl) *  
      [[ fst s' = fst s ]]) >> s').
Proof. Admitted. (*
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
Qed. *)

Hint Extern 1 (hoare_triple _ _ _ (encrypt_all _ _) _ _ _ _ _ _) => eapply encrypt_all_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (decrypt_all _ _) _ _ _ _ _ _) => eapply decrypt_all_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (hash_all _ _) _ _ _ _ _ _) => eapply hash_all_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (read_consecutive _ _) _ _ _ _ _ _) => eapply read_consecutive_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (write_consecutive _) _ _ _ _ _ _) => eapply write_consecutive_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (write_batch _ _) _ _ _ _ _ _) => eapply write_batch_ok : specs.
*)
