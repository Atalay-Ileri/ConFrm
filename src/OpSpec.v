Require Import List BaseTypes Memx Predx.
Require Import CommonAutomation SepAuto Layer1 ProgAuto HoareL1.
Open Scope pred_scope.

Theorem read_okay:
  forall a v,
    << o >>
     (a |-> v)
     (Read a)
    << o', r >>
     (a |-> v * [[r = fst v]])
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  invert_exec; cleanup.
  {
    left.
    do 3 eexists; split; eauto.
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    simpl in *; pred_apply; cancel; eauto.
  }
  {
    simpl in *; cleanup; right; eauto.
  }
Qed.

Theorem write_okay:
  forall a v v',
    << o >>
     (a |-> v)
     (Write a v')
    << o', r >>
     (a |-> (v', (fst v::snd v)))
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  invert_exec; cleanup; simpl in *.
  {
    left.
    do 3 eexists; split; eauto.
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk.
    eapply ptsto_upd'.
    pred_apply; cancel; eauto.
  }
  {
    simpl in *; cleanup; right; eauto. 
  }
Qed.

Theorem ret_okay:
  forall T (v: T),
    << o >>
     emp
     (Ret v)
    << o', r >>
     (emp * [[r = v]])
     emp.
Proof.
  intros.
  unfold hoare_triple; intros.
  invert_exec; cleanup; simpl in *.
  {
    left.
    do 3 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    simpl in *; cleanup; right; eauto.
  }
Qed.

