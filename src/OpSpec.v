Require Import List BaseTypes Memx Predx.
Require Import CommonAutomation SepAuto Layer1 ProgAuto HoareL1.
Open Scope pred_scope.

Lemma star_split:
    forall (AT : Type) (AEQ : EqDec AT) (V : Type)
      (p q : @pred AT AEQ V) (m : @mem AT AEQ V),
      (p * q)%pred m ->
      (exists m1 m2, mem_disjoint m1 m2 /\ p m1 /\ q m2 /\ mem_union m1 m2 = m)%type.
  Proof.
    intros; unfold sep_star in *; rewrite sep_star_is in *;
      destruct H; cleanup; eauto.
    do 2 eexists; intuition eauto.
  Qed.

Theorem read_okay:
  forall a v,
    << o >>
     (a |-> v)
     (Read a)
    << o', r >>
     (a |-> v *
      [[r = fst v]])
     (a |-> v).
Proof.
  unfold hoare_triple; intros. 
  eapply ptsto_valid' in H as Hx;
  cleanup; eauto.
  destruct o.
  destruct t; do 2 eexists.
    intuition eauto.
  econstructor; intuition eauto.
  inversion H0.

  intuition.
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  left; do 2 eexists; split; eauto.
  pred_apply; cancel.
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
  eapply ptsto_valid' in H as Hx;
    cleanup; eauto.
  
  destruct o, t; do 2 eexists.
    intuition eauto.
  econstructor; intuition eauto.
  inversion H0.

  split.
  econstructor; intuition eauto.
  unfold Disk.read in *; cleanup; eauto.
  left; do 2 eexists; split; eauto.
  unfold Disk.write; cleanup.
  unfold Disk.upd_disk.
  eapply ptsto_upd'; eauto.
Qed.

Theorem ret_okay:
  forall T (v: T),
    << o >>
     (emp)
     (Ret v)
    << o', r >>
    (emp *
     [[r = v]])
    (emp).
Proof.
  intros.
  unfold hoare_triple; intros.
  
  destruct o, t; do 2 eexists;
    intuition eauto.  
  econstructor; intuition eauto.
  inversion H0.
  left; do 2 eexists; split; eauto.
  pred_apply; cancel; eauto.
Qed.

