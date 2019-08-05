Require Import BaseTypes Prog Simulation.
Require Import Memx CommonAutomation.
Require Import List.
Require Import Eqdep.
Import ListNotations.

Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac invert_exec' :=
  match goal with
  | [ H: exec _ (Ret _) _ _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Read _) _ _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Write _ _) _ _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Seal _ _) _ _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Unseal _) _ _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Auth _) _ _ |- _ ] =>
    invert_exec'' H
  end.

Lemma bind_sep:
  forall T T' st (p1: prog T) (p2: T -> prog T') ret tr',
    exec st (Bind p1 p2) ret tr' ->
    match ret with
    | Finished st' r =>
    (exists tr1 tr2 r1 st1,
       exec st p1 (Finished st1 r1) tr1 /\
       exec st1 (p2 r1) ret tr2 /\ tr' = tr1 ++ tr2)
  | Crashed st' =>
    (exec st p1 (Crashed st') tr' \/
     (exists tr1 tr2 r1 st1,
        exec st p1 (Finished st1 r1) tr1 /\
        exec st1 (p2 r1) ret tr2 /\ tr' = tr1 ++ tr2))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 4 eexists; eauto.
  right; do 4 eexists; eauto.
Qed.

Ltac invert_exec :=
  match goal with
  |[H : exec _ (Bind _ _) _ _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ |- _ ] =>
   invert_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall st tr' out,
        exec st p1 out tr' <-> exec st p2 out tr'.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat invert_exec; cleanup.
      rewrite <- app_assoc.
      repeat econstructor; eauto.

      split_ors.
      invert_exec; cleanup.
      split_ors; cleanup.
      eapply ExecBindCrash; auto.      
      econstructor; eauto.
      eapply ExecBindCrash; eauto.
      invert_exec.
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    
    - repeat invert_exec; cleanup.
      rewrite app_assoc.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      repeat econstructor; eauto.
      invert_exec.
      split_ors.
      eapply ExecBindCrash; eauto.
      econstructor; eauto.
      rewrite app_assoc.
      repeat econstructor; eauto.
  Qed.
