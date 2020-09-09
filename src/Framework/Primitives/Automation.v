Require Import BaseTypes.
Require Import Mem.
Require Import List ListUtils.
Require Import Eqdep.
Import ListNotations.

Tactic Notation "eapply_fresh" constr(thm) "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm in H as Hx.

Tactic Notation "destruct_fresh" constr(term) :=
  let D := fresh "D" in destruct term eqn:D.

Tactic Notation "assert_fresh" constr(ass) :=
  let A := fresh "A" in assert ass as A.

Tactic Notation "assume" "(" ident(label) ":" constr(type) ")" :=
  assert (label: type); [shelve|].

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
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end; repeat sigT_eq.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H
  | [H: _ /\ _ |- _] => destruct H
  end; repeat logic_clean.

Local Ltac invert_const :=
  match goal with
  | [H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [H: Some _ = None |- _ ] =>
    inversion H; subst; clear H
  | [H: None = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [H: Finished _ _ = _ |- _ ] =>
    inversion H; subst; clear H
  | [H: Crashed _ = _ |- _ ] =>
    inversion H; subst; clear H
  | [H: (_, _) = (_, _) |- _ ] =>
    inversion H; subst; clear H
  end; repeat invert_const.

Local Ltac clear_dup:=
  match goal with
  | [H: ?x = ?x |- _] => clear H
  | [H: ?x, H0: ?x |- _] => clear H0
  end; repeat clear_dup.

Local Ltac rewrite_upd_eq:=
  match goal with
  |[H: upd _ ?x _ ?x = _ |- _] => rewrite upd_eq in H; try invert_const
  end; repeat rewrite_upd_eq.

Local Ltac rewriteall :=
  match goal with
  | [H := _ |- _] =>
    subst H
  | [H: ?x = _, H0: context [?x] |- _ ] =>
    rewrite H in H0
  | [H: ?x = _ |-  context [?x] ] =>
    rewrite H
  end; repeat rewriteall.

Local Ltac list_append_clear:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H
  | [H: ?tr++_ = ?tr++_ |- _] =>
    apply app_inv_head in H
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H
  end.

Local Ltac clear_lists:=
  match goal with
  | [H: _::_ = _::_ |- _] =>
    inversion H; clear H
  | [H: length _ = 0 |- _] =>
    apply length_zero_iff_nil in H
  | [H: 0 = length _  |- _] =>
    symmetry in H
  | [H: context[ firstn _ [] ] |- _] =>
    rewrite firstn_nil in H
  | [|- context[ firstn _ [] ] ] =>
    rewrite firstn_nil
  | [H: context[ skipn _ [] ] |- _] =>
    rewrite skipn_nil in H
  | [|- context[ skipn _ [] ] ] =>
    rewrite skipn_nil
  | _ =>
    list_append_clear
  end; repeat clear_lists.


Ltac split_match:=
  match goal with
  |[H: context [match ?x with | _ => _ end] |- _] =>
   let name := fresh "D" in
     destruct x eqn:name
  end;  repeat split_match.

Ltac cleanup:= try split_match; try logic_clean;
               subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try invert_const;
               try clear_lists; try sigT_eq;
               subst; try rewriteall.

Ltac cleanup_no_match
  := try logic_clean;
     subst; try rewriteall;
     try clear_dup; try rewrite_upd_eq;
     try clear_dup; try invert_const;
     try clear_lists; try sigT_eq;
     subst; try rewriteall.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H
  end.


