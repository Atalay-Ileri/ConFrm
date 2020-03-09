Require Import Framework.
Require Import CacheLayer.Definitions.
Open Scope pred_scope.

Theorem read_ok_some:
  forall o s a v F,
    << o, s >>
     PRE: (F * a |-> v >> s)
     PROG: (|Read a|)
    << r, s' >>
     POST: (F * a |-> v * [[r = Some v]] >> s')
     CRASH: (F * a |-> v >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; cleanup.

  split_ors.
  eapply ptsto_valid' in H0 as Hx;
  cleanup; eauto.
  
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.

  eexists; intuition eauto.
  eapply ExecOpCrash; eauto;
  econstructor; eauto.
Qed.

Theorem read_ok_none:
  forall o s a F,
    << o, s >>
     PRE: (F * [[s a = None]] >> s)
     PROG: (|Read a|)
    << r, s' >>
     POST: (F * [[r = None]] >> s')
     CRASH: (F >> s').
Proof.
  intros.
  unfold hoare_triple, any; intros.
  destruct_lift H; cleanup.

  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  
  destruct_lifts; cleanup.
  eexists; intuition eauto.
  eapply ExecOpCrash; eauto;
  econstructor; eauto.
Qed.

Theorem read_ok:
  forall o s a F,
    << o, s >>
     PRE: (F >> s)
     PROG: (|Read a|)
    << r, s' >>
     POST: (F * [[r = s a]] >> s')
     CRASH: (F >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; cleanup.
  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  simpl in *; pred_apply; cancel; eauto.

  eexists; intuition eauto.
  repeat econstructor; intuition eauto.
Qed.

Theorem write_ok_some:
  forall o s a v v' F,
    << o, s >>
     PRE: (F * a |-> v >> s)
     PROG: (|Write a v'|)
    << r, s' >>
     POST: (F * a |-> v' >> s')
     CRASH: (F * a |-> v >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; cleanup.
  eapply ptsto_valid' in H0 as Hx;
  cleanup; eauto.
  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  eapply ptsto_upd'; eauto.

  eexists; intuition eauto.
  repeat econstructor; intuition eauto.
Qed.

Theorem write_ok_none:
  forall o s a v' F,
    << o, s >>
     PRE: (F * [[s a = None]] >> s)
     PROG: (|Write a v'|)
    << r, s' >>
     POST: (F * a |-> v' >> s')
     CRASH: (F >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; cleanup.
  
  split_ors.
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  
  destruct_lifts;
  simpl; eapply ptsto_upd_disjoint; eauto.
  
  destruct_lifts.
  eexists; intuition eauto.
  repeat econstructor; intuition eauto.
Qed.

Theorem write_ok:
  forall o s a v' F,
    << o, s >>
     PRE:
     (match s a with
      |Some v => F * a |-> v
      |None => F
      end >> s)
     PROG: (|Write a v'|)
    << r, s' >>
     POST: (F * a |-> v' >> s')
     CRASH:
     (match s a with
      |Some v => F * a |-> v
      |None =>  F
      end >> s').
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; deex.
  
  eexists; intuition eauto;
  repeat econstructor; intuition eauto.
  
  cleanup; eauto.  
  simpl; eapply ptsto_upd'; eauto.    
  simpl; eapply ptsto_upd_disjoint; eauto.

  eexists; intuition eauto.
  repeat econstructor; intuition eauto.
Qed.

Hint Extern 1 (hoare_triple _ _ (|Read _|) _ _ _ _ _ _) => eapply read_ok : specs.
Hint Extern 1 (hoare_triple _ _ (|Write _ _|) _ _ _ _ _ _) => eapply write_ok : specs.