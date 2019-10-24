Require Import Primitives Simulation Layer2Definitions.

Lemma layer2_finished_not_crashed_oracle_app:
  forall T (p: prog T) o1 o2 s s1 s2 r1,
    exec o1 s p (Finished s1 r1) ->
    ~exec (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
    repeat match goal with
           | [H: exec _ _ _ _ |- _] =>
             inversion H; sigT_eq; cleanup; clear H
           end; simpl; eauto.
  simpl in *; cleanup.
  rewrite <- app_assoc in H2.
  -
    admit.
  - rewrite <- app_assoc in H6; eauto.
Admitted.

Lemma layer2_finished_oracle_length_eq:
  forall T (p: prog T) o1 o2 s s1 s2 r1 r2,
      exec o1 s p (Finished s1 r1) ->
      exec o2 s p (Finished s2 r2) ->
      length o1 = length o2.
Proof.
  induction p; intros;
    repeat match goal with
           | [H: exec _ _ _ _ |- _] =>
             inversion H; sigT_eq; cleanup; clear H
           end; simpl; eauto.
  repeat rewrite app_length.
  specialize IHp with (1:= H6)(2:= H7); cleanup.
