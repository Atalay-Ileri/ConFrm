Require Import List BaseTypes Memx Predx.
Require Import CommonAutomation SepAuto Layer1 ProgAuto HoareL1.
Open Scope pred_scope.

Theorem read_okay:
  forall a v t,
    << o >>
     (a |-> v * [[ o = t::nil ]])
     (Read a)
    << r >>
     (a |-> v * [[r = fst v]])
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  destruct t; eexists;
    intuition eauto;
  econstructor; intuition eauto.
  inversion H0.
  unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  do 2 eexists; split; eauto.
  unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
  simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem write_okay:
  forall a v v' t,
    << o >>
     (a |-> v * [[ o = t::nil ]])
     (Write a v')
    << r >>
     (a |-> (v', (fst v::snd v)))
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  destruct t; eexists;
    intuition eauto;
    econstructor; intuition eauto.
  inversion H0.
  
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    do 2 eexists; split; eauto.
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk.
    eapply ptsto_upd'.
    pred_apply; cancel; eauto.
Qed.

Theorem ret_okay:
  forall T (v: T) t,
    << o >>
     (emp * [[ o = t::nil ]])
     (Ret v)
    << r >>
     (emp * [[r = v]])
     emp.
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  destruct t; eexists;
    intuition eauto.
    econstructor; intuition eauto.
    inversion H0.
    simpl in *; cleanup; right; eexists; intuition eauto.
    pred_apply; cancel.

    left.
    do 2 eexists; split; eauto.
    pred_apply; cancel; eauto.
Qed.

