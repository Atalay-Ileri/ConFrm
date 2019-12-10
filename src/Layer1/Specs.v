Require Import Primitives.
Require Import Layer1.Definitions Layer1.HoareLogic Layer1.Automation.
Open Scope pred_scope.

Theorem read_ok:
  forall o d a v ax,
    << o, d, ax>>
     (a |-> v)
     (Read a)
    << r, axr >>
     (a |-> v * [[r = fst v]] * [[axr = ax]])
     (a |-> v * [[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors.
  eexists; intuition eauto;
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  
  do 2 eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.

  eexists; intuition eauto.
  econstructor; intuition eauto.
  inversion H0.
  right; eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem write_ok:
  forall o d ax a v v',
    << o, d, ax >>
     (a |-> v)
     (Write a v')
    << r, axr >>
     ([[axr = ax]] * a |-> (v', (fst v::snd v)))
     ([[axr = ax]] * a |-> v).
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors.
  eexists; intuition eauto;
    econstructor; intuition eauto.
  
    unfold Disk.read in *;
    cleanup; eauto.  
    do 2 eexists; intuition eauto.
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk; simpl.
    apply sep_star_assoc; eapply ptsto_upd'; eauto.
    pred_apply; cancel.

    eexists; intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    right; eexists; intuition eauto.
    simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem ret_ok:
  forall o d ax T (v: T),
    << o, d, ax >>
     emp
     (Ret v)
    << r, axr >>
     ([[r = v]] * [[axr = ax]])
     ([[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any, exec; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem getkey_ok:
  forall vl o d ax,
    let kl := fst (fst ax) in
    let em := snd (fst ax) in
    let hm := snd ax in
    << o, d, ax >>
     emp
     (GetKey vl)
    << r, axr >>
     ([[~In r kl]] *
      [[consistent_with_upds em (map (encrypt r) vl) (map (fun v => (r, v)) vl) ]] *
      [[axr = (r::kl, em, hm)]])
     ([[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any, exec; intros.
  destruct ax, p; simpl; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.  


Theorem hash_ok:
  forall o d ax h v,
    let hv := hash_function h v in
    let kl := fst (fst ax) in
    let em := snd (fst ax) in
    let hm := snd ax in
    << o, d, ax >>
     ([[ consistent hm hv (h, v) ]])
     (Hash h v)
    << r, axr >>
     ([[r = hv]] * [[axr = (kl, em, upd hm hv (h, v))]])
     ([[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any, exec; intros.
  destruct ax, p; simpl; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem encrypt_ok:
  forall o d ax k v,
    let ev := encrypt k v in
    let kl := fst (fst ax) in
    let em := snd (fst ax) in
    let hm := snd ax in
    << o, d, ax >>
     ([[ consistent em ev (k, v) ]])
     (Encrypt k v)
    << r, axr >>
     ([[r = ev]] * [[axr = (kl, upd em ev (k, v), hm)]])
     ([[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any, exec; intros.
  destruct ax, p; simpl; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.


Theorem decrypt_ok:
  forall o d ax k ev v,
    let kl := fst (fst ax) in
    let em := snd (fst ax) in
    let hm := snd ax in
    << o, d, ax >>
     ([[ ev = encrypt k v ]] * [[ em ev = Some (k, v) ]])
     (Decrypt k ev)
    << r, axr >>
     ([[r = v]] * [[axr = ax]])
     ([[axr = ax]]).
Proof.
  intros.
  unfold hoare_triple, any, exec; intros.
  destruct ax, p; simpl; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  simpl; pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  simpl; pred_apply; cancel.    
Qed.
