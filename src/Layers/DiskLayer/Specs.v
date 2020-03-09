Require Import Framework.
Require Import DiskLayer.Definitions.
Open Scope pred_scope.

Theorem read_ok:
  forall F o s a v,
    << o, s >>
    PRE:
     (F * a |-> v >> s)
    PROG:
     |Read a|
    << r, s' >>
    POST:
     (F * a |-> v * [[r = fst v]] * [[fst s' = fst s]] >> s')
    CRASH:
     (F * a |-> v * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; cleanup.
  
  eapply ptsto_valid' in H0 as Hx;
    cleanup; eauto.  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  unfold read in *; cleanup; eauto.
  
  simpl in *; pred_apply; cancel; eauto.

  eexists; intuition eauto.
  eapply ExecOpCrash; eauto;
  econstructor; eauto.
  
  right; eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem write_ok:
  forall F o s a v v',
    << o, s >>
     PRE: (F * a |-> v >> s)
     PROG: |Write a v'|
    << r, s' >>
     POST: (F * a |-> (v', (fst v::snd v)) * [[fst s' = fst s]] >> s')
     CRASH: (F * a |-> v * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H0 as Hx;
    cleanup; eauto.  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  
    unfold read in *; cleanup; eauto.  
    unfold write; cleanup.
    unfold upd_disk; simpl.
    eapply ptsto_upd' in H0; eauto.
    pred_apply' H0; cancel.

    eexists; intuition eauto.
    eapply ExecOpCrash; eauto;
    econstructor; eauto.
    right; eexists; intuition eauto.
    simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem getkey_ok:
  forall F vl o s,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    << o, s >>
     PRE: F >> s
     PROG: |GetKey vl|
    << r, s' >>
     POST:
      F * [[~In r kl]] *
      [[consistent_with_upds em
          (map (encrypt r) vl) (map (fun v => (r, v)) vl) ]] *
      [[fst s' = (r::kl, em, hm)]] >> s'
     CRASH:
      (F * [[fst s' = fst s]] >> s') .
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct s, p, p; simpl in *.
  simpl in *; cleanup;
  split_ors; eexists;
    intuition eauto.
  
  repeat econstructor; intuition eauto.
  left; do 2 eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.

  eapply ExecOpCrash; econstructor; eauto.
  
  right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.  


Theorem hash_ok:
  forall F o s h v,
    let hv := hash_function h v in
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    << o, s >>
     PRE: (F * [[ consistent hm hv (h, v) ]] >> s)
     PROG: (|Hash h v|)
    << r, s' >>
     POST: (F * [[r = hv]] * [[fst s' = (kl, em, upd hm hv (h, v))]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0;
  simpl in *; cleanup; simpl in *.
  split_ors; eexists;
    intuition eauto.

  do 2 econstructor; intuition eauto.
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  
  eapply ExecOpCrash; econstructor; eauto.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem encrypt_ok:
  forall F o s k v,
    let ev := encrypt k v in
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    << o, s >>
     PRE: (F * [[ consistent em ev (k, v) ]] >> s)
     PROG: (|Encrypt k v|)
    << r, s' >>
     POST: (F * [[r = ev]] *
                [[fst s' = (kl, upd em ev (k, v), hm)]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0; cleanup.
  split_ors; eexists;
  intuition eauto.

  do 2 econstructor; intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  eapply ExecOpCrash; econstructor; eauto.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem decrypt_ok:
  forall F o s k ev v,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    << o, s >>
     PRE: (F * [[ ev = encrypt k v ]] * [[ em ev = Some (k, v) ]] >> s)
     PROG: (|Decrypt k ev|)
    << r, s' >>
     POST: (F * [[r = v]] * [[fst s' = fst s]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0; cleanup.
  split_ors; eexists;
    intuition eauto.

  do 2 econstructor; intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  eapply ExecOpCrash; econstructor; eauto.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.

Hint Extern 1 (hoare_triple _ _ (|Read _|) _ _ _ _ _ _) => eapply read_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|Write _ _|) _ _ _ _ _ _) => eapply write_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|Hash _ _|) _ _ _ _ _ _) => eapply hash_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|GetKey _|) _ _ _ _ _ _) => eapply getkey_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|Encrypt _ _|) _ _ _ _ _ _) => eapply encrypt_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|Decrypt _ _|) _ _ _ _ _ _) => eapply decrypt_ok : specs.