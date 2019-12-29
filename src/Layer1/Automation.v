Require Import Primitives Simulation Layer1.Definitions.
Require Import Eqdep.
Import ListNotations.

Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac invert_exec' :=
  match goal with
  | [ H: exec _ _ ?p _ |- _ ] =>
    match p with
    | Bind _ _ => idtac
    | Read _ => invert_exec'' H
    | Write _ _ => invert_exec'' H
    | Hash _ _ => invert_exec'' H
    | Encrypt _ _ => invert_exec'' H
    | Decrypt _ _ => invert_exec'' H
    | GetKey _ => invert_exec'' H
    | Ret _ => invert_exec'' H
    end
  end.

Lemma bind_sep:
  forall T T' o d (p1: prog T) (p2: T -> prog T') ret,
    exec o d (Bind p1 p2) ret ->
    match ret with
    | Finished d' r =>
    (exists o1 o2 d1 r1,
       exec o1 d p1 (Finished d1 r1) /\
       exec o2 d1 (p2 r1) ret /\
       o = o1++o2)
  | Crashed d' =>
    (exec o d p1 (Crashed d') \/
     (exists o1 o2 d1 r1,
        exec o1 d p1 (Finished d1 r1) /\
        exec o2 d1 (p2 r1) ret /\
        o = o1++o2))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  right; do 2 eexists; eauto.
  exfalso; intuition eauto.
Qed.

Ltac invert_exec :=
  match goal with
  |[H : exec _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ |- _ ] =>
   invert_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall o d out,
        exec o d p1 out <-> exec o d p2 out.

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
      
      invert_exec.
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    
    - repeat invert_exec; cleanup.
      rewrite app_assoc.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      eapply ExecBindCrash; eauto.
      
      invert_exec.
      split_ors.
      eapply ExecBindCrash; eauto.
      
      rewrite app_assoc.
      repeat econstructor; eauto.
  Qed.

