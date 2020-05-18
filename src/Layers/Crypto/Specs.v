(*
Require Import Framework.
Require Import CryptoLayer.Definitions.
Open Scope pred_scope.


Notation "| p |" := (Op CryptoOperation _ p)(at level 60).


Theorem getkey_ok:
  forall F vl o s,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    LANG: DiskLang
    LOGIC: DiskHL
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
  unfold hoare_triple, hoare_triple'; intros.
  destruct s, p, p; simpl in *.
  simpl in *; cleanup;
  split_ors; eexists;
  intuition eauto.  

  eapply (ExecOp _).
  repeat econstructor; intuition eauto.
  left; do 2 eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.

  eapply (ExecOpCrash _); econstructor; eauto.
  
  right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.  


Theorem hash_ok:
  forall F o s h v,
    let hv := hash_function h v in
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
     PRE: (F * [[ consistent hm hv (h, v) ]] >> s)
     PROG: (|Hash h v|)
    << r, s' >>
     POST: (F * [[r = hv]] * [[fst s' = (kl, em, upd hm hv (h, v))]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple, hoare_triple'; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0;
  simpl in *; cleanup; simpl in *.
  split_ors; eexists;
    intuition eauto.

  eapply (ExecOp _).
  econstructor; eauto.
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.
  
  eapply (ExecOpCrash _); econstructor; eauto.  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem encrypt_ok:
  forall F o s k v,
    let ev := encrypt k v in
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
     PRE: (F * [[ consistent em ev (k, v) ]] >> s)
     PROG: (|Encrypt k v|)
    << r, s' >>
     POST: (F * [[r = ev]] *
                [[fst s' = (kl, upd em ev (k, v), hm)]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple, hoare_triple'; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0; cleanup.
  split_ors; eexists;
  intuition eauto.

  eapply (ExecOp _); econstructor; eauto.
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  eapply (ExecOpCrash _); econstructor; eauto.  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem decrypt_ok:
  forall F o s k ev v,
    let kl := fst (fst (fst s)) in
    let em := snd (fst (fst s)) in
    let hm := snd (fst s) in
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
     PRE: (F * [[ ev = encrypt k v ]] * [[ em ev = Some (k, v) ]] >> s)
     PROG: (|Decrypt k ev|)
    << r, s' >>
     POST: (F * [[r = v]] * [[fst s' = fst s]] >> s')
     CRASH: (F * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple, hoare_triple'; intros.
  destruct s, p, p; simpl; intros.
  destruct_lift H0; cleanup.
  split_ors; eexists;
    intuition eauto.

  eapply (ExecOp _); econstructor; eauto.
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  eapply (ExecOpCrash _); econstructor; eauto.  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.

Hint Extern 1 (hoare_triple _ _ _ (|Hash _ _|) _ _ _ _ _ _) => eapply hash_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (|GetKey _|) _ _ _ _ _ _) => eapply getkey_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (|Encrypt _ _|) _ _ _ _ _ _) => eapply encrypt_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (|Decrypt _ _|) _ _ _ _ _ _) => eapply decrypt_ok : specs.
*)
