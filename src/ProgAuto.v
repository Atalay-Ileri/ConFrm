Require Import BaseTypes Layer1 Simulation.
Require Import Memx CommonAutomation.
Require Import List.
Require Import Eqdep.
Import ListNotations.

Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac invert_exec' :=
  match goal with
  | [ H: exec _ _ ?p _ _ |- _ ] =>
    match p with
    | Bind _ _ => idtac
    | Read _ => invert_exec'' H
    | Write _ _ => invert_exec'' H
    | Ret _ => invert_exec'' H
    end
  end.

Lemma bind_sep:
  forall T T' o o' d (p1: prog T) (p2: T -> prog T') ret,
    exec o d (Bind p1 p2) o' ret ->
    match ret with
    | Finished d' r =>
    (exists o1 d1 r1,
       exec o d p1 o1 (Finished d1 r1) /\
       exec o1 d1 (p2 r1) o' ret)
  | Crashed d' =>
    (exec o d p1 o' (Crashed d') \/
     (exists o1 d1 r1,
        exec o d p1 o1 (Finished d1 r1) /\
        exec o1 d1 (p2 r1) o' ret))
  | Failed d' =>
    (exec o d p1 o' (Failed d') \/
     (exists o1 d1 r1,
        exec o d p1 o1 (Finished d1 r1) /\
        exec o1 d1 (p2 r1) o' ret))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  right; do 2 eexists; eauto.
  right; do 2 eexists; eauto.
  exfalso; intuition eauto.
Qed.

Ltac invert_exec :=
  match goal with
  |[H : exec _ _ (Bind _ _) _ _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ |- _ ] =>
   invert_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall o o' d out,
        exec o d p1 o' out <-> exec o d p2 o' out.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros;
      repeat invert_exec; cleanup;
        repeat (split_ors; try invert_exec; cleanup);
        intuition eauto.
  Qed.