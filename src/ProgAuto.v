Require Import BaseTypes Prog.
Require Import Memx.
Require Import List.
Require Import Eqdep.
Import ListNotations.

Lemma app_cons_nil:
  forall T (l: list T) a,
    a::l = (a::nil)++l.
Proof.
  intros; simpl; auto.
Qed.

Lemma cons_app_inv_tail :
  forall T (l l': list T) a,
    a::l = l'++l ->
    a::nil = l'.
Proof.
  intros.
  rewrite app_cons_nil in H.
  apply app_inv_tail in H; subst; auto.
Qed.


Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst; repeat sigT_eq
  end.


Ltac inv_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_exec' :=
  match goal with
  | [ H: exec _ _ _ _ (Ret _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ (Read _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ (Write _ _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ (Seal _ _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ (Unseal _) _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ _ _ _ (Auth _) _ _ |- _ ] =>
    inv_exec'' H
  end.

Lemma bind_sep:
  forall T T' pr (p1: prog T) (p2: T -> prog T') d bm dm (ret: result T') tr',
    exec pr d bm dm (Bind p1 p2) ret tr' ->
    match ret with
    | Finished _ _ _ _ =>
    (exists tr1 tr2 r1 d1 dm1 bm1,
       exec pr d bm dm p1 (Finished d1 bm1 dm1 r1) tr1 /\
       exec pr d1 bm1 dm1 (p2 r1) ret tr2 /\ tr' = tr1 ++ tr2)
  | Crashed _ d' bm' dm' =>
    (exec pr d bm dm p1 (Crashed _ d' bm' dm') tr' \/
     (exists tr1 tr2 r1 d1 dm1 bm1,
        exec pr d bm dm p1 (Finished d1 bm1 dm1 r1) tr1 /\
        exec pr d1 bm1 dm1 (p2 r1) ret tr2 /\ tr' = tr1 ++ tr2))
    end.
Proof.
  intros.
  inv_exec'' H; eauto.
  destruct ret.
  do 7 eexists; eauto.
  right; do 7 eexists; eauto.
Qed.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H; repeat logic_clean
  | [H: _ /\ _ |- _] => destruct H; repeat logic_clean
  end.

Ltac some_subst :=
  match goal with
  | [H: Some _ = Some _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Some _ = None |- _] => inversion H
  | [H: None = Some _ |- _] => inversion H
  | [H: Finished _ _ _ _ = Finished _ _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Crashed _ _ _ _ = Crashed _ _ _ _ |- _] => inversion H; subst; clear H; repeat some_subst
  | [H: Finished _ _ _ _ = Crashed _ _ _ _ |- _] => inversion H
  | [H: Crashed _ _ _ _ = Finished _ _ _ _ |- _] => inversion H
  end.

Ltac clear_dup:=
  match goal with
  | [H: ?x = ?x |- _] => clear H; repeat clear_dup
  | [H: ?x, H0: ?x |- _] => clear H0; repeat clear_dup
  end.

Ltac rewrite_upd_eq:=
  match goal with
  |[H: upd _ ?x _ ?x = _ |- _] => rewrite upd_eq in H; repeat rewrite_upd_eq; try some_subst
  end.

Ltac rewriteall :=
  match goal with
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _ |- context [?x] ] => rewrite H; repeat rewriteall
  end.


Ltac clear_trace:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H; repeat clear_trace
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1; repeat clear_trace
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H; repeat clear_trace
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H; repeat clear_trace
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  end.


Ltac split_match:=
  match goal with
  |[H: context [match ?x with | _ => _ end] |- _] =>
   let name := fresh "D" in
     destruct x eqn:name; repeat split_match
  end.

Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; try sigT_eq;
               subst; try rewriteall.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H; cleanup
  end.


Ltac inv_exec_perm :=
  match goal with
  |[H : exec _ _ _ _ (Bind _ _) _ _ |- _ ] => apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ _ _ |- _ ] => inv_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall pr d bm dm tr' out,
        exec pr d bm dm p1 out tr' <-> exec pr d bm dm p2 out tr'.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat inv_exec_perm; cleanup.
      rewrite <- app_assoc.
      repeat econstructor; eauto.

      split_ors.
      inv_exec_perm; cleanup.
      split_ors; cleanup.
      eapply ExecBindCrash; auto.      
      econstructor; eauto.
      eapply ExecBindCrash; eauto.
      inv_exec_perm.
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    
    - repeat inv_exec_perm; cleanup.
      rewrite app_assoc.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      repeat econstructor; eauto.
      inv_exec_perm.
      split_ors.
      eapply ExecBindCrash; eauto.
      econstructor; eauto.
      rewrite app_assoc.
      repeat econstructor; eauto.
  Qed.
