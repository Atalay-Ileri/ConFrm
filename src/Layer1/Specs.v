Require Import Primitives Layer1.Definitions HoareLogic ProgAuto.
Open Scope pred_scope.

Theorem read_ok:
  forall o d a v,
    << o, d >>
     (a |-> v)
     (Read a)
    << r >>
     (a |-> v * [[r = fst v]])
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors; eexists;
    intuition eauto;
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  
  do 2 eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.
  inversion H0.
Qed.

Theorem write_ok:
  forall o d a v v',
    << o, d >>
     (a |-> v)
     (Write a v')
    << r >>
     (a |-> (v', (fst v::snd v)))
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors; eexists;
    intuition eauto;
    econstructor; intuition eauto.
  
    unfold Disk.read in *;
    cleanup; eauto.  
    do 2 eexists; intuition eauto.
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk.
    eapply ptsto_upd'; eauto.
    inversion H0.
Qed.

Theorem ret_ok:
  forall o d T (v: T),
    << o, d >>
     emp
     (Ret v)
    << r >>
     (emp * [[r = v]])
     emp.
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; intuition eauto.
  pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  pred_apply; cancel.    
Qed.

