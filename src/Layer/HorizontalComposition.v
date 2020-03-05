Require Import Primitives Simulation Layer.Language.
Import ListNotations.

Set Implicit Arguments.

Module HorizontalComposition (O1 O2: Operation) <: Operation.
  Inductive token :=
  | Oracle1 : O1.oracle -> token
  | Oracle2 : O2.oracle -> token.

  Definition oracle := list token.

  Definition token_dec: forall (t t': token), {t = t'}+{t <> t'}.
   decide equality.
   apply O1.oracle_dec.
   apply O2.oracle_dec.
  Defined.

  Definition oracle_dec:= list_eq_dec token_dec.
  Definition state := (O1.state * O2.state)%type.

  Inductive op' : Type -> Type :=
  | Op1 : forall T, O1.op T -> op' T
  | Op2 : forall T, O2.op T -> op' T.
  
  Definition op := op'.

  Inductive exec': forall T, oracle -> state -> op T -> @Result state T -> Prop :=
  | ExecOp1:
      forall T (p1: O1.op T) o1 s s1 r,
        O1.exec o1 (fst s) p1 (Finished s1 r) ->
        exec' [Oracle1 o1] s (Op1 p1) (Finished (s1, snd s) r)
| ExecOp2:
      forall T (p2: O2.op T) o2 s s2 r,
        O2.exec o2 (snd s) p2 (Finished s2 r) ->
        exec' [Oracle2 o2] s (Op2 p2) (Finished (fst s, s2) r)
| ExecOp1Crash:
      forall T (p1: O1.op T) o1 s s1,
        O1.exec o1 (fst s) p1 (Crashed s1) ->
        exec' [Oracle1 o1] s (Op1 p1) (Crashed (s1, snd s))
| ExecOp2Crash:
      forall T (p2: O2.op T) o2 s s2,
        O2.exec o2 (snd s) p2 (Crashed s2) ->
        exec' [Oracle2 o2] s (Op2 p2) (Crashed (fst s, s2)).
  Definition exec := exec'.
  Definition oracle_ok T (p: op T) o s := 
    match p with
    | Op1 p1 =>
      exists o1,
      o = [Oracle1 o1] /\ O1.oracle_ok p1 o1 (fst s)
    | Op2 p2 =>
      exists o2,
      o = [Oracle2 o2] /\ O2.oracle_ok p2 o2 (snd s)
    end.
  
  Definition exec_deterministic_wrt_oracle :
    forall o s T (p: op T) ret1 ret2,
      exec o s p ret1 ->
      exec o s p ret2 ->
      ret1 = ret2.
    intros; destruct p; simpl in *;
    inversion H; inversion H0;
    sigT_eq; clear H H0; cleanup;
    try solve [eapply O1.exec_deterministic_wrt_oracle in H6;
               eauto; cleanup; eauto];
    try solve [eapply O2.exec_deterministic_wrt_oracle in H6;
               eauto; cleanup; eauto].
  Qed.
    
  Definition exec_then_oracle_ok:
    forall T (p: op T) o s r,
      exec o s p r ->
      oracle_ok p o s.
    intros; destruct p; simpl in *;
    inversion H; inversion H0;
    sigT_eq; clear H H0; cleanup;
    try solve [eapply O1.exec_then_oracle_ok in H5; eauto];
    try solve [eapply O2.exec_then_oracle_ok in H5; eauto].
  Qed.
End HorizontalComposition.

