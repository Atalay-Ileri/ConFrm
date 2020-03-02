Require Import Primitives.
Require Import CacheLayer.Definitions CacheLayer.HoareLogic CacheLayer.Automation.
Open Scope pred_scope.

Theorem read_ok_some:
  forall o d a v ax,
    << o, d, ax>>
     (a |-> v)
     (Read a)
    << r, axr >>
     (a |-> v * [[r = Some v]])
     (a |-> v).
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
Qed.

Theorem read_ok_none:
  forall o d a ax,
    << o, d, ax>>
     ([[d a = None]])
     (Read a)
    << r, axr >>
     ([[r = None]])
     emp.
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
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
  simpl; pred_apply; cancel.
Qed.

Theorem read_ok:
  forall o d a ax,
    << o, d, ax>>
     emp
     (Read a)
    << r, axr >>
     ([[r = d a]])
     emp.
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
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
  simpl; pred_apply; cancel.
Qed.

Theorem write_ok_some:
  forall o d ax a v v',
    << o, d, ax >>
     (a |-> v)
     (Write a v')
    << r, axr >>
     (a |-> v')
     (a |-> v).
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
    eapply ptsto_upd'; eauto.

    eexists; intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    right; eexists; intuition eauto.
Qed.

Theorem write_ok_none:
  forall o d ax a v',
    << o, d, ax >>
     ([[d a = None]])
     (Write a v')
    << r, axr >>
     (a |-> v')
     emp.
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  split_ors.
  eexists; intuition eauto;
    econstructor; intuition eauto.
  
    unfold Disk.read in *;
    cleanup; eauto.  
    do 2 eexists; intuition eauto.
    simpl; eapply ptsto_upd_disjoint; eauto.

    eexists; intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    right; eexists; intuition eauto.
    simpl; pred_apply; cancel.
Qed.

Theorem write_ok:
  forall o d ax a v',
    << o, d, ax >>
     (match d a with
      |Some v => a |-> v
      |None =>  emp
     end)
     (Write a v')
    << r, axr >>
     (a |-> v')
     (match d a with
      |Some v => a |-> v
      |None =>  emp
     end).
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  split_ors.
  eexists; intuition eauto;
    econstructor; intuition eauto.
  
    cleanup; eauto.  
    do 2 eexists; intuition eauto.
    simpl; eapply ptsto_upd'; eauto.
    
    eexists; intuition eauto;
    econstructor; intuition eauto.    
    do 2 eexists; intuition eauto.
    simpl; eapply ptsto_upd_disjoint; eauto.
    pred_apply; cancel.

    eexists; intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    right; eexists; intuition eauto.

    eexists; intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    right; eexists; intuition eauto.
Qed.

Theorem ret_ok:
  forall o d ax T (v: T),
    << o, d, ax >>
     emp
     (Ret v)
    << r, axr >>
     ([[r = v]])
     emp.
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

Hint Extern 1 (hoare_triple _ (Read _) _ _ _ _ _ _ _) => eapply read_ok : specs.
Hint Extern 1 (hoare_triple _ (Write _ _) _ _ _ _ _ _ _) => eapply write_ok : specs.
Hint Extern 1 (hoare_triple _ (Ret _) _ _ _ _ _ _ _) => eapply ret_ok : specs.