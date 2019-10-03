Require Import List BaseTypes Memx Predx.
Require Import CommonAutomation SepAuto Layer1 ProgAuto HoareL1.
Open Scope pred_scope.

Theorem read_ok:
  forall a v,
    << o >>
     (a |-> v)
     (Read a)
    << r >>
     (a |-> v * [[r = fst v]])
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors; eexists;
    intuition eauto;
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  
  do 2 eexists; split; eauto.
  simpl in *; pred_apply; cancel; eauto.
  inversion H0.
Qed.

Theorem write_ok:
  forall a v v',
    << o >>
     (a |-> v)
     (Write a v')
    << r >>
     (a |-> (v', (fst v::snd v)))
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  split_ors; eexists;
    intuition eauto;
    econstructor; intuition eauto.
  
    unfold Disk.read in *;
    cleanup; eauto.  
    do 2 eexists; split; eauto.
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk.
    eapply ptsto_upd'; eauto.
    inversion H0.
Qed.

Theorem ret_ok:
  forall T (v: T),
    << o >>
     emp
     (Ret v)
    << r >>
     (emp * [[r = v]])
     emp.
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  split_ors; eexists;
    intuition eauto.
  
  left; do 2 eexists; split; eauto.
  pred_apply; cancel; eauto.

  econstructor; intuition eauto.
  inversion H0.
  
  simpl in *; cleanup; right; eexists; intuition eauto.
  pred_apply; cancel.    
Qed.

