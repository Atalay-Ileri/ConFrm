Require Import Primitives Simulation Layer2.Definitions.

Lemma layer2_exec_finished_deterministic:
  forall T (p: prog T) o1 o2 o3 o4 s s1 s2 r1 r2,
      exec o1 s p (Finished s1 r1) ->
      exec o2 s p (Finished s2 r2) ->
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat match goal with
           | [H: exec _ _ _ _ |- _] =>
             inversion H; sigT_eq; simpl in *; cleanup; clear H
           end; simpl; eauto; try solve [intuition].
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H7)(2:= H8)(3:=H2); cleanup.
  apply app_inv_head in H2.
  specialize H with (1:= H12)(2:= H11)(3:=H2); cleanup; eauto.
Qed.

Lemma layer2_finished_not_crashed_oracle_app:
  forall T (p: prog T) o1 o2 s s1 s2 r1,
    exec o1 s p (Finished s1 r1) ->
    ~exec (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
    repeat match goal with
           | [H: exec _ _ _ _ |- _] =>
             inversion H; sigT_eq; simpl in *; cleanup; clear H
           end; simpl; eauto.
  -
    rewrite <- app_assoc in H2.
    eapply layer2_exec_finished_deterministic in H7; eauto; cleanup; eauto.
    apply app_inv_head in H2; cleanup; eauto.
    
  -
    rewrite <- app_assoc in H6; eauto.
Qed.

Lemma layer2_exec_deterministic:
  forall T (p: prog T) o s r1 r2,
      exec o s p r1 ->
      exec o s p r2 ->
      r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat match goal with
           | [H: exec _ _ _ _ |- _] =>
             inversion H; sigT_eq; simpl in *; cleanup; clear H
           end; simpl; eauto; try solve [intuition].
  eapply layer2_exec_finished_deterministic in H7; eauto; cleanup; eauto.
  apply app_inv_head in H1; cleanup; eauto.
  exfalso; eapply layer2_finished_not_crashed_oracle_app; eauto.
  exfalso; eapply layer2_finished_not_crashed_oracle_app; eauto.  
  specialize IHp with (1:= H5)(2:= H6); cleanup; eauto.
Qed.