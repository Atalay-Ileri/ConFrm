Require Import List BaseTypes Memx Predx.
Require Import CommonAutomation SepAuto Layer1 ProgAuto HoareL1.
Open Scope pred_scope.

Theorem read_okay:
  forall a v t ox,
    << o >>
     (a |-> v * [[ o = t::ox ]])
     (Read a)
    << o', r >>
     (a |-> v *
      [[ o' = ox ]] *
      [[r = fst v]])
     (a |-> v *
     [[ o' = ox ]]).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.
  destruct t; do 2 eexists;
    intuition eauto.
  econstructor; intuition eauto.
  inversion H0.
  right; eexists; split; eauto.
  pred_apply; cancel.
  
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  left; do 2 eexists; split; eauto.
  pred_apply; cancel.
Qed.

Theorem write_okay:
  forall a v v' t ox,
    << o >>
     (a |-> v * [[ o = t::ox ]])
     (Write a v')
    << o', r >>
     (a |-> (v', (fst v::snd v)) *
      [[ o' = ox ]])
     (a |-> v *
      [[ o' = ox ]]).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.
  
  destruct t; do 2 eexists;
    intuition eauto.
  econstructor; intuition eauto.
  inversion H0.
  right; eexists; split; eauto.
  pred_apply; cancel.

  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  left; do 2 eexists; split; eauto.
  unfold Disk.write; cleanup.
  unfold Disk.upd_disk.
  eapply ptsto_upd' in H.
  pred_apply' H; cancel; eauto.
Qed.

Theorem ret_okay:
  forall T (v: T) t ox,
    << o >>
     (emp * [[ o = t::ox ]])
     (Ret v)
    << o', r >>
    (emp *
     [[r = v]] *
     [[ o' = ox ]])
    (emp *
     [[o' = ox]]).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  destruct t; do 2 eexists;
    intuition eauto.  
  econstructor; intuition eauto.
  inversion H0.
  simpl in *; cleanup; right; eexists; intuition eauto.
  pred_apply; cancel.

  left; do 2 eexists; split; eauto.
  pred_apply; cancel; eauto.
Qed.

