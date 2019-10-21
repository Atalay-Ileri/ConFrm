Require Import Primitives Layer1 BlockAllocator.
Require Import Layer2 SimulationLayer Layer1to2RefinementDefinitions.
Require Import FunctionalExtensionality Omega.

Section Layer1to2Refinement.

  Lemma length_lt_prefix:
    forall T (l1 l2 l3 l4: list T),
      l1++l2=l3++l4 ->
      length l1 < length l3 ->
      exists l1', l3 = l1++l1' /\ l1' <> [].
  Proof.
    induction l1; simpl in *; intros; eauto.
    destruct l3; simpl in *.
    inversion H0.
    eexists; split; eauto.
    congruence.
    destruct l3; simpl in *.
    inversion H0.
    inversion H; subst.
    edestruct IHl1; eauto.
    omega.
    destruct H1; subst.
    eexists; eauto.
  Qed.

  Lemma oracle_ok_app_exec_nil:
    forall T (p: Layer1.prog T) o1 o2 s ret,
      Layer1.exec o1 s p ret ->
      oracle_ok p (o1++o2) s ->
      o2=[].
  Proof.
     induction p; simpl; intros;
       try solve [  unfold oracle_ok in *; intuition; apply app_eq_unit in H1;
                    split_ors; cleanup; eauto; invert_exec ].
     invert_exec;
     unfold oracle_ok in H1; cleanup;
    fold (@oracle_ok T) in *;
    fold (@oracle_ok T') in *.
    cleanup.
      Search app nil.
    split_ors; cleanup.
    
  Lemma oracle_ok_bind_split:
    forall T T' (p1: Layer1.prog T) (p2: T -> Layer1.prog T') o1 o2 sl sl' r ret,
      Layer1.exec o1 sl p1 (Finished sl' r) ->
      Layer1.exec o2 sl' (p2 r) ret ->
      oracle_ok (Layer1.Bind p1 p2) (o1 ++ o2) sl ->
      oracle_ok p1 o1 sl /\
      oracle_ok (p2 r) o2 sl'.      
  Proof.
    simpl; intros.
    unfold oracle_ok in H1; cleanup;
    fold (@oracle_ok T) in *;
    fold (@oracle_ok T') in *.
    destruct (lt_dec (length o1) (length x)).
    -
      eapply length_lt_prefix in H1; eauto; cleanup.
      
      Search app length lt.
    specialize IHp with (1:= H0)(2:=H3).
    repeat rewrite app_length; cleanup.
Admitted.

  Axiom oracle_ok_exec_app_nil:
    forall T (p: Layer1.prog T) o1 o2 s ret,
      Layer1.exec (o1++o2) s p ret ->
      oracle_ok p o1 s ->
      o2=[].

  (* XXX: We need oracle lengths to extract oracle equalities *) 
  Axiom layer1_exec_finished_then_oracle_length_eq :
    forall T (p: Layer1.prog T) s o1 o2 s'1 s'2 r1 r2,
      Layer1.exec o1 s p (Finished s'1 r1) ->
      Layer1.exec o2 s p (Finished s'2 r2) ->
      o1 = o2.

  Axiom layer1_finished_not_crashed_app:
    forall T (p1: Layer1.prog T) o1 o2 s s' s'' r,
       Layer1.exec o1 s p1 (Finished s' r) ->
       ~ Layer1.exec (o1++o2) s p1 (Crashed s'').

  Axiom layer1_exec_preserves_refines_to:
    forall T (p2: Layer2.prog T) o1 s1 s1',
      Layer1.exec o1 s1 (compile p2) s1' ->
      (exists s2, refines_to s1 s2) ->
      (exists s2', refines_to (extract_state s1') s2').
  

  Axiom oracle_refines_to_deterministic:
    forall T (p: Layer2.prog T) s o o1 o2,
      oracle_refines_to T s p o o1 ->
      oracle_refines_to T s p o o2 ->
      o1 = o2.

  Lemma oracle_ok_nonempty:
    forall T (p: Layer1.prog T) s,
      ~oracle_ok p [] s.
  Proof.
    unfold not, oracle_ok;
    induction p; simpl; intros; try intuition congruence.
    cleanup.
    symmetry in H0; apply app_eq_nil in H0; cleanup; eauto.
  Qed.
  Hint Resolve oracle_ok_nonempty.
  
  (*
  Lemma oracle_refinement_deterministic:
    forall T p2 ol1 ol2 oh sl1 sl2 p1 sl1' sl2', (* sh1 sh2 sh1' sh2' ,
      refines_to sl1 sh1 ->
      refines_to sl2 sh2 ->
      *)
      compilation_of T p1 p2 ->
      Layer1.exec ol1 sl1 p1 sl1' ->
      Layer1.exec ol2 sl2 p1 sl2' ->
      result_same sl1' sl2' ->
      (forall def, extract_ret def sl1' = extract_ret def sl2') ->
      (*
      Layer2.exec oh sh1 p2 sh1' ->
      Layer2.exec oh sh2 p2 sh2' ->
      result_same sl1' sh1' ->
      result_same sl2' sh2' ->
      result_same sh1' sh2' ->
                                *)
      oracle_refines_to T sl1 p2 ol1 oh ->
      oracle_refines_to T sl2 p2 ol2 oh ->
      ol1 = ol2.
  Proof.
    unfold compilation_of; induction p2; simpl; intros.
    - (* Read *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Write *)
        cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Alloc *)
      destruct (in_dec token_dec Layer1.Crash ol1), (in_dec token_dec Layer1.Crash ol2);
        try solve [cleanup; tauto].
      cleanup.
      + (* Crashed *)
        admit.
      + destruct H4, H5.
        clear H0 H1 H6 H7; cleanup.
        clear H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t; try tauto.
        erewrite H1; eauto.
    - (* Free *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a0, t; try tauto.
        erewrite H1; eauto.
    - (* Ret *)
      cleanup.
      + (* Crashed *)
        admit.
      + (* Finished *)
        clear D D0 H0 H1 H4.
        generalize dependent ol2.
        induction ol1; destruct ol2; simpl in *; intros; eauto; try omega.
        intuition; cleanup.
        destruct a, t0; try tauto.
        erewrite H1; eauto.
    - (* Bind *)
      cleanup.
      invert_exec; invert_exec; try tauto.
      + (* Both Finished *)
        specialize (H8 x1).
        specialize (H7 x5).
        cleanup.
        edestruct H10; eauto; cleanup.
        edestruct H11; eauto; cleanup.
        specialize IHp2 with (2:= H0)(3:=H2); simpl in *.
        edestruct IHp2; eauto.
        specialize H with (2:= H1)(3:=H9); simpl in *.
        
      destruct oh; simpl in *.
        cleanup; try tauto.
        unfold refines_to in *; cleanup.
        eapply read_ok in H; cleanup.
        split_ors; destruct_lifts; cleanup.
        edestruct H4.
        
        split_ors; cleanup.
        
        edestruct read_ok.
        pred_apply' H; cancel.
        eassign
   *)

  Arguments oracle_ok T p o s : simpl never.
  Arguments oracle_refines_to T d1 p o1 o2 : simpl never.
  
  Lemma Axiom1:
    forall T p2 p1 ol sl sl',
      (exists sh, refines_to sl sh) ->
      oracle_ok p1 ol sl ->
      Layer1.exec ol sl p1 sl' ->
      (forall d, sl' <> Failed d) ->
      compilation_of T p1 p2 ->
      exists oh, oracle_refines_to T sl p2 ol oh.
  Proof.
    unfold refines_to, compilation_of;
    induction p2; simpl; intros; cleanup.

    - (* Read *)
      edestruct read_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
      cleanup; destruct_lifts; eauto.
    - (* Write *)
      edestruct write_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; eauto.
      split_ors; cleanup; eauto.
        
    - (* Alloc *)
      edestruct alloc_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; 
          split_ors; cleanup; eauto.
    - (* Free *)
      edestruct free_ok.
      pred_apply' H; cancel; eauto.
      cleanup; split_ors;
        cleanup; destruct_lifts; eauto;
          split_ors; cleanup; eauto.
    - (* Ret *)
      destruct sl';
      unfold oracle_refines_to; simpl;
        destruct (in_dec token_dec Crash ol); eauto.
    - (* Bind *)
      invert_exec; cleanup.      
      + (* Finished *)
        unfold oracle_ok in H1; cleanup.
        fold (@oracle_ok T) in H5.
        fold (@oracle_ok T') in H6.

        eapply_fresh oracle_ok_finished_length in H2; eauto.
        eapply ListUtils.app_split_length_eq_l in Hx; eauto; cleanup.
        edestruct IHp2; eauto.
        intros d Hx; inversion Hx.
        edestruct layer1_exec_preserves_refines_to; try apply H2; eauto.
        unfold refines_to; eauto.
        edestruct H; eauto; simpl in *.
        exists (x1++x7).
        unfold oracle_refines_to; simpl; fold oracle_refines_to.
        split.
        unfold oracle_ok; simpl;
        fold (@oracle_ok T); fold (@oracle_ok T').

        do 2 eexists; intuition eauto.
        do 2 eexists; intuition eauto.
        
        exfalso; eapply layer1_finished_not_crashed_app in H2; eauto.
        exfalso; eapply layer1_finished_not_crashed_app in H2; eauto.
        eapply exec_finished_deterministic in H2; eauto; cleanup.
        do 2 eexists; intuition eauto.
        
      + (* Crashed *)
        unfold oracle_ok in H1; cleanup.
        fold (@oracle_ok T) in H4.
        fold (@oracle_ok T') in H5.

        split_ors; cleanup.
        * eapply_fresh oracle_ok_exec_app_nil in H1; eauto; cleanup.
          rewrite app_nil_r in *.
          edestruct IHp2; eauto.
          intros d Hx; inversion Hx.
          exists x2.
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split.
          unfold oracle_ok; simpl;
          fold (@oracle_ok T); fold (@oracle_ok T').

          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          specialize H5 with (1:= H8).
          
          exfalso; eapply oracle_ok_nonempty; eauto.
        
        * eapply_fresh oracle_ok_finished_length in H4; eauto.
          eapply ListUtils.app_split_length_eq_l in Hx; eauto; cleanup.
          edestruct IHp2; eauto.
          intros d Hx; inversion Hx.
          edestruct layer1_exec_preserves_refines_to; try apply H1; eauto.
          unfold refines_to; eauto.
          edestruct H; eauto; simpl in *.
          exists (x3++x7).
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split.
          unfold oracle_ok; simpl;
          fold (@oracle_ok T); fold (@oracle_ok T').

          do 2 eexists; intuition eauto.
          do 2 eexists; intuition eauto.

          exfalso; eapply layer1_finished_not_crashed_app in H1; eauto.
          exfalso; eapply layer1_finished_not_crashed_app in H1; eauto.
          eapply exec_finished_deterministic in H1; eauto; cleanup.
          do 2 eexists; intuition eauto.
        
      + (* Failed *)
        exfalso; eapply H3; eauto.
  Qed.

(*
  Lemma Axiom2:
    forall T p2 oh sl sh sh',
      refines_to sl sh ->
      (exists o, oracle_ok (compile p2) o sl) ->
      Layer2.exec oh sh p2 sh' ->
      exists ol, oracle_refines_to T sl p2 ol oh.
  Proof.
    induction p2; simpl; intros.
    - (* Read *)
      inversion H1; clear H1; cleanup.
      
      + (* Finished *)
        unfold refines_to in *; cleanup.
        edestruct read_ok.
        pred_apply' H; norm.
        cancel.
        intuition eauto.

        cleanup.
        split_ors; destruct_lifts; cleanup; eauto.
        edestruct H4.
        
        split_ors; cleanup.
        
        edestruct read_ok.
        pred_apply' H; cancel.
      
Abort.
*)

  Theorem sbs_read :
    forall a,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of
        refines_to
        oracle_refines_to
        (Read a).              
  Proof.
    constructor; intros.
    
    unfold refines_to,
    compiles_to_valid, compilation_of in *; intros.
    simpl in *;
      split.
    
    + (* Low to High *)
      intros; cleanup.
      edestruct (read_ok a); eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *; cleanup;
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
      
      * (* Finished *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
        intuition (cleanup; eauto).
        unfold rep in *.
        destruct_lifts.          
        symmetry; eauto.
  
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct (read_ok a); cleanup.
      pred_apply' H; norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
        
      split_ors; cleanup;
      destruct_lifts;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end.
      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
        intuition (cleanup; eauto).
        unfold rep in *.
        destruct_lifts;          
        symmetry; eauto.
          
      * (* Crashed *)
          eexists; split.
          eauto.
          simpl in *.
          repeat split; eauto.
  Qed.

  Theorem sbs_write :
    forall a v,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to
        (Write a v).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct write_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished 1 *)
        eexists; split.
        eapply ExecWriteFail; eauto.
        simpl in *.
        repeat split; eauto.

      * (* Finished 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct write_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Finished 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
Qed.

  Theorem sbs_free :
    forall a,
    StrongBisimulationForProgram
      layer1_lts layer2_lts
      compilation_of refines_to
      oracle_refines_to
      (Free a).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct free_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct free_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
  Qed.
 

  Theorem sbs_ret :
    forall T (v: T),
    StrongBisimulationForProgram
      layer1_lts layer2_lts
      compilation_of refines_to
      oracle_refines_to
      (Ret v).              
  Proof.
        constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      invert_exec; cleanup;
      unfold oracle_refines_to in *;
      cleanup; simpl in *;
      try split_ors; intuition; try congruence.

      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
          
    + (*High to low*)
      intros; cleanup.
      
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence;
      unfold oracle_refines_to, oracle_ok in *;
      cleanup; simpl in *;
      repeat (split_ors; cleanup; simpl in *);
      intuition; try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed *)
        eexists; split.
        econstructor; eauto.
        intros; congruence.
        simpl in *.
        repeat split; eauto.
  Qed.

   Theorem sbs_alloc :
     forall v,
      StrongBisimulationForProgram
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to
        (Alloc v).              
  Proof.
    constructor; intros.
    cleanup; try tauto.    
    unfold refines_to, compiles_to_valid, compilation_of in *; intros.
    simpl in *; split.

    + (* Low to High *)
      intros; cleanup.
      edestruct alloc_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      eapply_fresh deterministic_prog in H2; eauto; cleanup.        
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Finished  *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
      * (* Crashed 1 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 2 *)
        eexists; split.
        econstructor; eauto.
        simpl in *.
        repeat split; eauto.
          
    + (*High to low*)
      intros; cleanup.
      edestruct alloc_ok; eauto.
      pred_apply' H. norm.
      cancel.
      unfold oracle_refines_to in *.
      intuition eauto.
      cleanup.
      
      split_ors; cleanup;
      destruct_lifts;
      try split_ors; cleanup;
      match goal with
      |[H: oracle_refines_to _ _ _ ?o _,
        H0: oracle_refines_to _ _ _ ?o _ |- _] =>
       eapply oracle_refines_to_deterministic in H; eauto; cleanup
      end;
      match goal with
      | [H: Layer2.exec _ _ _ _ |- _] =>
        inversion H; sigT_eq; simpl in *; cleanup
      end;
      try congruence.

      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Finished *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
        
      * (* Crashed 1 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.

      * (* Crashed 2 *)
        eexists; split.
        eauto.
        simpl in *.
        repeat split; eauto.
  Qed.

  Theorem sbs_bind:
    forall T1 T2 (p1: Layer2.prog T1) (p2: T1 -> Layer2.prog T2),
      StrongBisimulationForProgram layer1_lts layer2_lts
          compilation_of refines_to oracle_refines_to p1 ->
    (forall t,
      StrongBisimulationForProgram layer1_lts layer2_lts
        compilation_of refines_to oracle_refines_to 
        (p2 t)) ->
    StrongBisimulationForProgram layer1_lts layer2_lts
          compilation_of refines_to oracle_refines_to (Layer2.Bind p1 p2).
  Proof.
    intros.
    edestruct H.
    constructor; intros.
    unfold compilation_of, oracle_refines_to in *;
    simpl in *; cleanup;
    fold oracle_refines_to in *.
    unfold oracle_ok in *; simpl in *; cleanup.
    fold (@oracle_ok T1) in *; fold (@oracle_ok T2) in *.

    split; intros.
    - (* Low to High *)
      invert_exec; cleanup; intuition.
      eapply_fresh oracle_ok_finished_length in H9; eauto.
      eapply ListUtils.app_split_length_eq_l in Hx; eauto; cleanup.
      specialize H4 with (1:= H9).
      (* Oct 18: Fix oracle_refines_to definition for Bind *)
  Admitted.
    
  Hint Resolve sbs_alloc sbs_free sbs_read sbs_ret sbs_write sbs_bind.
  
  Theorem sbs :
      StrongBisimulation
        layer1_lts layer2_lts
        compilation_of refines_to
        oracle_refines_to.              
  Proof.
    apply bisimulation_restrict_prog.
    induction p; eauto.
  Qed.

  Hint Resolve sbs.

  Theorem sbs_general:
    forall valid_state_h valid_prog_h,
      exec_compiled_preserves_validity layer1_lts layer2_lts
    compilation_of (refines_to_valid refines_to valid_state_h) ->
    exec_preserves_validity layer2_lts valid_state_h ->
      StrongBisimulationForValidStates
        layer1_lts layer2_lts
        (refines_to_valid refines_to valid_state_h)
        (compiles_to_valid valid_prog_h compilation_of)
        valid_state_h
        valid_prog_h
        compilation_of refines_to
        oracle_refines_to.  
  Proof.
    intros.
    eapply bisimulation_restrict_state; eauto.
  Qed.
    
End Layer1to2Refinement.