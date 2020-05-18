(*
Require Import Framework.
Require Import DiskLayer.Definitions.
Open Scope pred_scope.


Notation "| p |" := (Op DiskOperation _ p)(at level 60).

Theorem read_ok:
  forall F o s a v,
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
    PRE:
     (F * a |-> v >> s)
    PROG:
     |Read a|
    << r, s' >>
    POST:
     (F * a |-> v * [[r = fst v]] >> s')
    CRASH:
     (F * a |-> v >> s').
Proof.
  intros.
  unfold hoare_triple, hoare_triple'; intros.
  destruct_lift H; cleanup.
  
  eapply ptsto_valid' in H0 as Hx;
    cleanup; eauto.  
  
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  repeat econstructor; eauto.
  unfold read in *; cleanup; eauto.
  
  simpl in *; pred_apply; cancel; eauto.

  eexists; intuition eauto.
  eapply (ExecOpCrash _); eauto;
  econstructor; eauto.
  
  right; eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.
Qed.

Theorem write_ok:
  forall F o s a v v',
    LANG: DiskLang
    LOGIC: DiskHL
    << o, s >>
     PRE: (F * a |-> v >> s)
     PROG: |Write a v'|
    << r, s' >>
     POST: (F * a |-> (v', (fst v::snd v)) * [[fst s' = fst s]] >> s')
     CRASH: (F * a |-> v * [[fst s' = fst s]] >> s').
Proof.
  intros.
  unfold hoare_triple, hoare_triple'; intros.
  destruct_lift H; subst.
  eapply ptsto_valid' in H0 as Hx;
    cleanup; eauto.  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  repeat econstructor; eauto.
  
  
  unfold read in *; cleanup; intuition; cleanup.
  unfold write; cleanup.
  unfold upd_disk; simpl.
  eapply ptsto_upd' in H0; eauto.
  pred_apply' H0; cancel.
  
  eexists; intuition eauto.
  eapply (ExecOpCrash _); eauto;
  econstructor; eauto.
  right; eexists; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.
Qed.

Hint Extern 1 (hoare_triple _ _ _ (|Read _|) _ _ _ _ _ _) => eapply read_ok : specs.
Hint Extern 1 (hoare_triple _ _ _ (|Write _ _|) _ _ _ _ _ _) => eapply write_ok : specs.
*)
