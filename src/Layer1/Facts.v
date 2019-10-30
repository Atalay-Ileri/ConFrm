Require Import Primitives Simulation Layer1.Definitions ProgAuto.
Import ListNotations.

Lemma exec_crash_in:
  forall T (p: prog T) o d d',
    exec o d p (Crashed d') ->
    In Crash o.
Proof.
  induction p; simpl in *; intros;
    invert_exec; intuition; eauto.
  cleanup.
  apply in_app_iff; eauto.
Qed.

Lemma exec_finished_deterministic:
  forall T (p: prog T) o1 o2 st st1 st2 r1 r2,
    exec o1 st p (Finished st1 r1)->
    exec o2 st p (Finished st2 r2) ->
    st1 = st2 /\ r1 = r2 /\ o1 = o2.
Proof.
    unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
      cleanup; eauto.
    specialize IHp with (1:=H0)(2:=H1); eauto; cleanup.
    specialize H with (1:=H2)(2:=H3); cleanup.
    repeat rewrite app_length; eauto.
Qed.

Lemma exec_finished_oracle_app:
  forall T (p: prog T) o1 o2 st st1 r1 ret,
    exec o1 st p (Finished st1 r1)->
    exec (o1++o2) st p ret ->
    o2 = [] /\ ret = Finished st1 r1.
Proof.
  unfold state; induction p; simpl; intros;
    try solve [
          invert_exec; cleanup;
          invert_exec; cleanup; 
          [ match goal with
            | [H: [_] = [_] ++ _ |- _] =>
              rewrite app_nil_end in H at 1;
              apply app_inv_head in H; eauto
            end|
            repeat rewrite <- app_cons_nil in *;
            inversion H1; congruence] ].

  invert_exec; cleanup;
    invert_exec; cleanup.
    -
      eapply exec_finished_deterministic in H0; eauto; cleanup.
      eapply exec_finished_deterministic in H4; eauto; cleanup.
      rewrite <- app_assoc in H3.
      apply app_inv_head in H3; cleanup; eauto.
      setoid_rewrite <- app_nil_r in H3 at 4.
      apply app_inv_head in H3; cleanup; eauto.
    -
      split_ors.
      +
        rewrite <- app_assoc in H1; eauto.
        edestruct IHp; eauto; inversion H4.
      +
        eapply exec_finished_deterministic in H0; eauto; cleanup.
        rewrite <- app_assoc in H4.
        apply app_inv_head in H4; cleanup; eauto.
Qed.

Lemma deterministic_prog:
  forall T (p: prog T) o st ret1 ret2,
    exec o st p ret1 ->
    exec o st p ret2 ->
    ret1 = ret2.
Proof.
  unfold state; induction p; simpl; intros;
  invert_exec; cleanup;
    invert_exec; cleanup;
      try solve [intuition eauto].
  - eapply exec_finished_deterministic in H0; eauto; cleanup.
    eapply exec_finished_deterministic in H3; eauto; cleanup; eauto.
  
  - destruct H0; cleanup.
    + exfalso; eapply exec_finished_oracle_app in H1; eauto; cleanup.  
    + eapply exec_finished_deterministic in H0; eauto; cleanup.
      apply app_inv_head in H4; cleanup; eauto.

  - destruct H1; cleanup.
    + exfalso; eapply exec_finished_oracle_app in H1; eauto; cleanup.  
    + eapply exec_finished_deterministic in H0; eauto; cleanup.
      apply app_inv_head in H4; cleanup; eauto.

  - destruct H0; cleanup; destruct H1; cleanup.
    + specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
    + exfalso; eapply exec_finished_oracle_app in H1; eauto; cleanup.
    + exfalso; eapply exec_finished_oracle_app in H1; eauto; cleanup.      
    + eapply exec_finished_deterministic in H0; eauto; cleanup.
      apply app_inv_head in H4; cleanup; eauto.

Qed.

  Lemma oracle_ok_nonempty:
    forall T (p: prog T) s,
      ~oracle_ok p [] s.
  Proof.
    unfold not, oracle_ok;
    induction p; simpl; intros; try intuition congruence.
    cleanup.
    symmetry in H0; apply app_eq_nil in H0; cleanup; eauto.
  Qed.

  Lemma oracle_ok_bind_assoc:
    forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T'') o sl,
      oracle_ok (Bind (Bind p1 p2) p3) o sl ->
      oracle_ok (Bind p1 (fun x => (Bind (p2 x) p3))) o sl.      
  Proof.
    intros;
      unfold oracle_ok in *; intuition.
    fold (@oracle_ok T) in *;
      fold (@oracle_ok T') in *;
      fold (@oracle_ok T'') in *.
    cleanup.
    exists x1, (x2++x0).
    split.
    rewrite app_assoc; eauto.
    intuition eauto.
    specialize H4 with (1:= H).
    do 2 eexists; intuition eauto.
    erewrite H5, H2; eauto.
    erewrite H5; eauto.
    rewrite app_nil_r.
    eapply ExecBindCrash; eauto.
  Qed.
  
  Lemma oracle_ok_bind_finished_split:
    forall T T' (p1: prog T) (p2: T -> prog T') o1 o2 sl sl' r ret,
      exec o1 sl p1 (Finished sl' r) ->
      exec o2 sl' (p2 r) ret ->
      oracle_ok (Bind p1 p2) (o1 ++ o2) sl ->
      oracle_ok p1 o1 sl /\
      oracle_ok (p2 r) o2 sl'.      
  Proof.
    induction p1; simpl; intros;
    try solve [  pose proof H;
      unfold oracle_ok in *; intuition;
        invert_exec; simpl in *; cleanup;
      split_ors; cleanup; inversion H1; subst; eauto;
      specialize H3 with (1:= H); eauto].
    apply oracle_ok_bind_assoc in H2.
    invert_exec.
    rewrite <- app_assoc in H2.
    specialize (IHp1 (fun x => Bind (p x) p2)) with (1:=H0)(3:= H2).
    edestruct IHp1.
    econstructor; eauto.
    
    specialize H with (1:=H3)(2:= H1)(3:= H5).
    destruct H; intuition eauto.
    
    unfold oracle_ok in H5; cleanup;
    fold (@oracle_ok T) in *;
      fold (@oracle_ok T') in *;
      fold (@oracle_ok T'0) in *.

    unfold oracle_ok; cleanup;
    fold (@oracle_ok T) in *;
      fold (@oracle_ok T') in *;
      fold (@oracle_ok T'0) in *.
    do 2 eexists; intuition eauto.
    eapply deterministic_prog in H0; eauto; cleanup; eauto.
    eapply deterministic_prog in H0; eauto; cleanup.
  Qed.

  Lemma oracle_ok_finished_eq:
    forall T (p: prog T) o1 o2 o1' o2' s s' r,
      exec o1 s p (Finished s' r) ->
      o1 ++ o2 = o1' ++ o2' ->
      oracle_ok p o1' s ->
      o1 = o1' /\ o2 = o2'.
  Proof.
    induction p; simpl; intros;
    try solve [ unfold oracle_ok in *; intuition;
                invert_exec; simpl in *; cleanup; eauto ].
    invert_exec; cleanup.
     repeat rewrite <- app_assoc in H1.
     specialize IHp with (1:= H0)(2:= H1)(3:=H3); cleanup.
     specialize H4 with (1:= H0).
     specialize H with (1:= H6)(2:= H7)(3:=H4); cleanup; eauto.
  Qed.     

  Lemma oracle_ok_exec_crashed_app_nil:
    forall T (p: prog T) o1 o2 s s',
      exec (o1++o2) s p (Crashed s') ->
      oracle_ok p o1 s ->
      o2=[].
  Proof.
     induction p; simpl; intros;
     try solve [ unfold oracle_ok in *; intuition;
        invert_exec; simpl in *; cleanup; eauto].
     invert_exec; split_ors; cleanup.

     -
       rewrite <- app_assoc in H0.
       specialize IHp with (1:= H0)(2:=H2).
       apply app_eq_nil in IHp; cleanup; eauto.

     -
       rewrite <- app_assoc in H5.
       symmetry in H5.
       eapply_fresh oracle_ok_finished_eq in H0; eauto; cleanup.
       specialize H3 with (1:=H0).
       specialize H with (1:= H1)(2:=H3); eauto.
  Qed.

   Lemma oracle_ok_bind_crashed_split:
    forall T T' (p1: prog T) (p2: T -> prog T') o1 sl sl',
      exec o1 sl p1 (Crashed sl') ->
      oracle_ok (Bind p1 p2) o1 sl ->
      oracle_ok p1 o1 sl.      
  Proof.
    intros; simpl in *; cleanup.
    eapply_fresh oracle_ok_exec_crashed_app_nil in H; eauto; cleanup.
    rewrite app_nil_r; eauto.
  Qed.

   Lemma exec_then_oracle_ok:
    forall T (p: prog T) o s r,
      exec o s p r ->
      oracle_ok p o s.
  Proof.
    induction p; simpl; intros; try solve [unfold oracle_ok; invert_exec; cleanup; simpl; eauto].
    invert_exec.
    - specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply deterministic_prog in H0; eauto; cleanup; eauto.
    -
      split_ors; cleanup.
      specialize IHp with (1:= H0).
      do 2 eexists; intuition; eauto;
        eapply deterministic_prog in H0; eauto; cleanup; eauto.

      specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply deterministic_prog in H0; eauto; cleanup; eauto.
  Qed.

  Lemma finished_crash_not_in:
    forall T (p: prog T) s s' o r,
      exec o s p (Finished s' r) ->
      ~In Crash o.
  Proof.
    induction p; simpl; intros; invert_exec; cleanup; simpl; intuition eauto; try congruence.
    apply in_app_iff in H2; intuition eauto.
  Qed.