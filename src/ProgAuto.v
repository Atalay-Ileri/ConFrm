Require Import BaseTypes Layer1 Simulation.
Require Import Memx CommonAutomation.
Require Import List.
Require Import Eqdep.
Import ListNotations.

Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac invert_exec' :=
  match goal with
  | [ H: exec _ (Ret _) _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Read _) _ |- _ ] =>
    invert_exec'' H
  | [ H: exec _ (Write _ _) _ |- _ ] =>
    invert_exec'' H
  end.

Lemma bind_sep:
  forall T T' st (p1: prog T) (p2: T -> prog T') ret,
    exec st (Bind p1 p2) ret ->
    match ret with
    | Finished st' r =>
    (exists r1 st1,
       exec st p1 (Finished st1 r1) /\
       exec st1 (p2 r1) ret)
  | Crashed st' =>
    (exec st p1 (Crashed st') \/
     (exists r1 st1,
        exec st p1 (Finished st1 r1) /\
        exec st1 (p2 r1) ret ))
  | Failed st' =>
    (exec st p1 (Failed st') \/
     (exists r1 st1,
        exec st p1 (Finished st1 r1) /\
        exec st1 (p2 r1) ret ))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  right; do 2 eexists; eauto.
  right; do 2 eexists; eauto.
Qed.

Ltac invert_exec :=
  match goal with
  |[H : exec _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ |- _ ] =>
   invert_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall st out,
        exec st p1 out <-> exec st p2 out.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat invert_exec; cleanup.
      repeat econstructor; eauto.

      split_ors.
      invert_exec; cleanup.
      split_ors; cleanup.
      eapply ExecBindCrash; auto.      
      econstructor; eauto.
      eapply ExecBindCrash; eauto.
      invert_exec.
      repeat econstructor; eauto.

      split_ors.
      invert_exec; cleanup.
      split_ors; cleanup.
      eapply ExecBindFail; auto.      
      econstructor; eauto.
      eapply ExecBindFail; eauto.
      invert_exec.
      repeat econstructor; eauto.
    
    - repeat invert_exec; cleanup.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      eapply ExecBindCrash; eauto.
      eapply ExecBindCrash; eauto.
      invert_exec.
      split_ors.
      eapply ExecBindCrash; eauto.
      econstructor; eauto.
      repeat econstructor; eauto.

      split_ors.
      eapply ExecBindFail; eauto.
      eapply ExecBindFail; eauto.
      invert_exec.
      split_ors.
      eapply ExecBindFail; eauto.
      econstructor; eauto.
      repeat econstructor; eauto.
  Qed.
