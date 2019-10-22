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

  Lemma oracle_ok_nonempty:
    forall T (p: Layer1.prog T) s,
      ~oracle_ok p [] s.
  Proof.
    unfold not, oracle_ok;
    induction p; simpl; intros; try intuition congruence.
    cleanup.
    symmetry in H0; apply app_eq_nil in H0; cleanup; eauto.
  Qed.

  Lemma oracle_ok_bind_assoc:
    forall T T' T'' (p1: Layer1.prog T) (p2: T -> Layer1.prog T') (p3: T' -> Layer1.prog T'') o sl,
      oracle_ok (Layer1.Bind (Layer1.Bind p1 p2) p3) o sl ->
      oracle_ok (Layer1.Bind p1 (fun x => (Layer1.Bind (p2 x) p3))) o sl.      
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
    specialize H5 with (1:= H).
    do 2 eexists; intuition eauto.
    erewrite H6, H2; eauto.
    erewrite H6; eauto.
    rewrite app_nil_r.
    eapply Layer1.ExecBindCrash; eauto.

    erewrite H7, H3; eauto.
    erewrite H7; eauto.
    rewrite app_nil_r.
    eapply Layer1.ExecBindFail; eauto.
  Qed.
  
  Lemma oracle_ok_bind_finished_split:
    forall T T' (p1: Layer1.prog T) (p2: T -> Layer1.prog T') o1 o2 sl sl' r ret,
      Layer1.exec o1 sl p1 (Finished sl' r) ->
      Layer1.exec o2 sl' (p2 r) ret ->
      oracle_ok (Layer1.Bind p1 p2) (o1 ++ o2) sl ->
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
    specialize (IHp1 (fun x => Layer1.Bind (p x) p2)) with (1:=H0)(3:= H2).
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
    eapply deterministic_prog in H0; eauto; cleanup.
  Qed.

  Lemma oracle_ok_finished_eq:
    forall T (p: Layer1.prog T) o1 o2 o1' o2' s s' r,
      Layer1.exec o1 s p (Finished s' r) ->
      o1 ++ o2 = o1' ++ o2' ->
      oracle_ok p o1' s ->
      o1 = o1' /\ o2 = o2'.
  Proof.
    induction p; simpl; intros;
    try solve [ unfold oracle_ok in *; intuition;
                invert_exec; simpl in *; cleanup; eauto ].
    invert_exec; cleanup.
     unfold oracle_ok in H2; cleanup;
         fold (@oracle_ok T) in *;
         fold (@oracle_ok T') in *.
     repeat rewrite <- app_assoc in H1.
     specialize IHp with (1:= H0)(2:= H1)(3:=H4); cleanup.
     specialize H5 with (1:= H0).
     specialize H with (1:= H3)(2:= H8)(3:=H5); cleanup; eauto.
  Qed.     

  Lemma oracle_ok_exec_crashed_app_nil:
    forall T (p: Layer1.prog T) o1 o2 s s',
      Layer1.exec (o1++o2) s p (Crashed s') ->
      oracle_ok p o1 s ->
      o2=[].
  Proof.
     induction p; simpl; intros;
     try solve [ unfold oracle_ok in *; intuition;
        invert_exec; simpl in *; cleanup; eauto].
     invert_exec; split_ors; cleanup.

     -
       unfold oracle_ok in H1; cleanup;
         fold (@oracle_ok T) in *;
         fold (@oracle_ok T') in *.
       rewrite <- app_assoc in H0.
       specialize IHp with (1:= H0)(2:=H2).
       apply app_eq_nil in IHp; cleanup; eauto.

     -
       unfold oracle_ok in H1; cleanup;
         fold (@oracle_ok T) in *;
         fold (@oracle_ok T') in *.
       rewrite <- app_assoc in H3.
       symmetry in H3.
       eapply_fresh oracle_ok_finished_eq in H0; eauto; cleanup.
       specialize H5 with (1:=H0).
       specialize H with (1:= H2)(2:=H5); eauto.
  Qed.

  Lemma oracle_ok_exec_failed_app_nil:
    forall T (p: Layer1.prog T) o1 o2 s s',
      Layer1.exec (o1++o2) s p (Failed s') ->
      oracle_ok p o1 s ->
      o2=[].
  Proof.
     induction p; simpl; intros;
     try solve [ unfold oracle_ok in *; intuition;
        invert_exec; simpl in *; cleanup; eauto].
     invert_exec; split_ors; cleanup.

     -
       unfold oracle_ok in H1; cleanup;
         fold (@oracle_ok T) in *;
         fold (@oracle_ok T') in *.
       rewrite <- app_assoc in H0.
       specialize IHp with (1:= H0)(2:=H2).
       apply app_eq_nil in IHp; cleanup; eauto.

     -
       unfold oracle_ok in H1; cleanup;
         fold (@oracle_ok T) in *;
         fold (@oracle_ok T') in *.
       rewrite <- app_assoc in H3.
       symmetry in H3.
       eapply_fresh oracle_ok_finished_eq in H0; eauto; cleanup.
       specialize H5 with (1:=H0).
       specialize H with (1:= H2)(2:=H5); eauto.
  Qed.

   Lemma oracle_ok_bind_crashed_split:
    forall T T' (p1: Layer1.prog T) (p2: T -> Layer1.prog T') o1 sl sl',
      Layer1.exec o1 sl p1 (Crashed sl') ->
      oracle_ok (Layer1.Bind p1 p2) o1 sl ->
      oracle_ok p1 o1 sl.      
  Proof.
    intros; unfold oracle_ok in *; cleanup;
    fold (@oracle_ok T) in *;
    fold (@oracle_ok T') in *.
    eapply_fresh oracle_ok_exec_crashed_app_nil in H; eauto; cleanup.
    rewrite app_nil_r; eauto.
  Qed.

  Lemma oracle_ok_bind_failed_split:
    forall T T' (p1: Layer1.prog T) (p2: T -> Layer1.prog T') o1 sl sl',
      Layer1.exec o1 sl p1 (Failed sl') ->
      oracle_ok (Layer1.Bind p1 p2) o1 sl ->
      oracle_ok p1 o1 sl.      
  Proof.
    intros; unfold oracle_ok in *; cleanup;
    fold (@oracle_ok T) in *;
    fold (@oracle_ok T') in *.
    eapply_fresh oracle_ok_exec_failed_app_nil in H; eauto; cleanup.
    rewrite app_nil_r; eauto.
  Qed.
  
  Lemma crash_in_oracle_then_crashed:
    forall T (p: Layer1.prog T) s o,
      In Layer1.Crash o ->
      oracle_ok p o s ->
      exists s', Layer1.exec o s p (Crashed s').
  Proof.
    induction p; simpl; intros; cleanup; eauto;
    try (unfold oracle_ok in *; try split_ors; cleanup; simpl in *; try intuition congruence);
    try (eexists; econstructor; eauto;
         intros; congruence).
    fold (@oracle_ok T) in *;
    fold (@oracle_ok T') in *.
    eexists; econstructor; eauto;
    intros; congruence.
    eexists; econstructor; eauto;
    intros; congruence.
  
  Lemma oracle_refines_to_deterministic:
    forall T (p: Layer2.prog T) s o o1 o2,
      oracle_refines_to T s p o o1 ->
      oracle_refines_to T s p o o2 ->
      o1 = o2.
  Proof.
    induction p; simpl; intros; cleanup; eauto.
    

  
  Axiom layer1_exec_compiled_preserves_refines_to:
    forall T (p2: Layer2.prog T) o1 s1 s1',
      Layer1.exec o1 s1 (compile p2) s1' ->
      (exists s2, refines_to s1 s2) ->
      (exists s2', refines_to (extract_state s1') s2').
  
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
        eapply_fresh oracle_ok_bind_finished_split in H1; eauto; cleanup.
        edestruct IHp2; eauto.
        (* intros d Hx; inversion Hx. *)
        edestruct layer1_exec_compiled_preserves_refines_to; try apply H2; eauto.
        unfold refines_to; eauto.
        edestruct H; eauto; simpl in *.
        exists (x5++x7).
        unfold oracle_refines_to; simpl; fold oracle_refines_to.
        split; eauto.
        
        do 2 eexists; intuition eauto.
        match goal with
        | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
          eapply_fresh oracle_ok_exec_crashed_app_nil in H;
          eauto; cleanup
        end.
        exfalso; eapply oracle_ok_nonempty; eauto.
        match goal with
        | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
          eapply_fresh oracle_ok_exec_crashed_app_nil in H;
          eauto; cleanup
        end.
        repeat match goal with
        | [H: Layer1.exec _ _ _ (Finished _ _),
           H0: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
          eapply deterministic_prog in H;
          try apply H0; eauto; cleanup
        end.
        
        do 2 eexists; intuition eauto.
        
      + (* Crashed *)
        split_ors; cleanup.
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_crashed_split in H;
          eauto; cleanup
          end.
          
          edestruct IHp2; eauto.
          (* intros d Ha; inversion Ha. *)
          exists x1.
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split.
          unfold oracle_ok; simpl;
          fold (@oracle_ok T); fold (@oracle_ok T').

          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Crashed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Crashed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
        
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_finished_split in H;
          eauto; cleanup
          end.
          edestruct IHp2; eauto.
          (* intros d Hx; inversion Hx. *)
          
          edestruct H;
          try match goal with
          | [H: oracle_ok (compile (_ _)) _ _ |- _ ] =>
            apply H
          end; eauto; simpl in *.

          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply layer1_exec_compiled_preserves_refines_to in H;
            eauto; cleanup
          end.
          unfold refines_to; eauto.
          
          exists (x5++x6).
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split; eauto.

          do 2 eexists; intuition eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          exfalso; eapply oracle_ok_nonempty; eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _),
             H0: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply deterministic_prog in H;
            try apply H0; eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
        
      + (* Failed *)
        split_ors; cleanup.
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_failed_split in H;
          eauto; cleanup
          end.
          
          edestruct IHp2; eauto.
          (* intros d Ha; inversion Ha. *)
          exists x1.
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split.
          unfold oracle_ok; simpl;
          fold (@oracle_ok T); fold (@oracle_ok T').

          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Failed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
          rewrite app_nil_r; eauto.
          match goal with
          | [H: Layer1.exec _ _ _ (Failed _) |- _ ] =>
            eapply deterministic_prog in H;
            eauto; cleanup
          end.
        
        *
          match goal with
          | [H: oracle_ok _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_bind_finished_split in H;
          eauto; cleanup
          end.
          edestruct IHp2; eauto.
          (* intros d Hx; inversion Hx. *)
          
          edestruct H;
          try match goal with
          | [H: oracle_ok (compile (_ _)) _ _ |- _ ] =>
            apply H
          end; eauto; simpl in *.

          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply layer1_exec_compiled_preserves_refines_to in H;
            eauto; cleanup
          end.
          unfold refines_to; eauto.
          
          exists (x5++x6).
          unfold oracle_refines_to; simpl; fold oracle_refines_to.
          split; eauto.

          do 2 eexists; intuition eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          exfalso; eapply oracle_ok_nonempty; eauto.
          match goal with
          | [H: Layer1.exec (_++_) _ _ _ |- _ ] =>
            eapply_fresh oracle_ok_exec_crashed_app_nil in H;
            eauto; cleanup
          end.
          match goal with
          | [H: Layer1.exec _ _ _ (Finished _ _),
             H0: Layer1.exec _ _ _ (Finished _ _) |- _ ] =>
            eapply deterministic_prog in H;
            try apply H0; eauto; cleanup
          end.
          do 2 eexists; intuition eauto.
  Qed.

  Lemma Axiom :
     forall T p2 ol1 ol2 oh s1 s2,
       oracle_refines_to T s1 p2 ol1 oh ->
       oracle_refines_to T s2 p2 ol2 oh ->
       ol1 = ol2.
  Proof.
    induction p2; simpl; intros.
    unfold oracle_refines_to in *; simpl in *; cleanup.
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
      try match goal with
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
      eapply_fresh oracle_ok_finished_eq in H9; eauto; cleanup.
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