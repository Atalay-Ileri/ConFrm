Require Import Primitives Simulation CacheLayer.Definitions CacheLayer.Automation.
Import ListNotations.

Lemma cache_layer_exec_crash_in:
  forall T (p: prog T) o d d',
    exec o d p (Crashed d') ->
    In Crash o.
Proof.
  induction p; simpl in *; intros;
    try invert_exec; intuition; eauto.
  cleanup.
  apply in_app_iff; eauto.
Qed.

Lemma cache_layer_exec_finished_deterministic:
  forall T (p: prog T) o1 o2 o3 o4 s s1 s2 r1 r2,
      exec o1 s p (Finished s1 r1) ->
      exec o2 s p (Finished s2 r2) ->
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H0)(2:= H1)(3:=H2); cleanup.
  apply app_inv_head in H2.
  specialize H with (1:= H4)(2:= H3)(3:=H2); cleanup; eauto.
Qed.

Lemma cache_layer_finished_not_crashed_oracle_app:
  forall T (p: prog T) o1 o2 s s1 s2 r1,
    exec o1 s p (Finished s1 r1) ->
    ~exec (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup); simpl; eauto.
  split_ors; cleanup.
  -
    rewrite <- app_assoc in H1; eauto.
  -
    rewrite <- app_assoc in H4; eauto.
    eapply cache_layer_exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
Qed.

Lemma cache_layer_exec_deterministic:
  forall T (p: prog T) o s r1 r2,
      exec o s p r1 ->
      exec o s p r2 ->
      r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  -
    eapply cache_layer_exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
  -
    split_ors; cleanup.
    exfalso; clear H2; eapply cache_layer_finished_not_crashed_oracle_app; eauto.

    eapply cache_layer_exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
    
  -
    split_ors; cleanup.
    exfalso; clear H2; eapply cache_layer_finished_not_crashed_oracle_app; eauto.

    eapply cache_layer_exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
  -
    repeat split_ors; cleanup.
    specialize IHp with (1:= H0)(2:= H1); cleanup; eauto.

    exfalso; clear H2; eapply cache_layer_finished_not_crashed_oracle_app; eauto.
    
    exfalso; clear H2; eapply cache_layer_finished_not_crashed_oracle_app; eauto.

    eapply cache_layer_exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
Qed.

  Lemma oracle_ok_nonempty:
    forall T (p: prog T) s,
      ~oracle_ok p [] s.
  Proof.
    unfold not;
    induction p; simpl; intros; try (split_ors; cleanup); try intuition congruence.
    cleanup.
    symmetry in H0; apply app_eq_nil in H0; cleanup; eauto.
  Qed.

  Lemma oracle_ok_bind_assoc:
    forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T'') o sl,
      oracle_ok (Bind (Bind p1 p2) p3) o sl ->
      oracle_ok (Bind p1 (fun x => (Bind (p2 x) p3))) o sl.      
  Proof.
    intros; simpl in *; cleanup.
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
      simpl in *; intuition;
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
    
    simpl in *; cleanup.
    
    do 2 eexists; intuition eauto.
    eapply cache_layer_exec_deterministic in H0; eauto; cleanup; eauto.
    eapply cache_layer_exec_deterministic in H0; eauto; cleanup.
  Qed.
(*
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
     try solve [ intuition; invert_exec; simpl in *; cleanup; eauto].
     split_ors; cleanup; invert_exec; eauto.
     
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
*)
   Lemma exec_then_oracle_ok:
    forall T (p: prog T) o s r,
      exec o s p r ->
      oracle_ok p o s.
  Proof.
    induction p; simpl; intros; try solve [invert_exec; cleanup; simpl; eauto].
    invert_exec.
    - specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply cache_layer_exec_deterministic in H0; eauto; cleanup; eauto.
    -
      split_ors; cleanup.
      specialize IHp with (1:= H0).
      do 2 eexists; intuition; eauto;
        eapply cache_layer_exec_deterministic in H0; eauto; cleanup; eauto.

      specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply cache_layer_exec_deterministic in H0; eauto; cleanup; eauto.
  Qed.

  Lemma finished_crash_not_in:
    forall T (p: prog T) s s' o r,
      exec o s p (Finished s' r) ->
      ~In Crash o.
  Proof.
    induction p; simpl; intros; invert_exec; cleanup; simpl; intuition eauto; try congruence.
    apply in_app_iff in H2; intuition eauto.
  Qed.