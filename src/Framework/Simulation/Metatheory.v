Require Import List Primitives Layer.
Require Import Simulation.Definitions Simulation.WeakestPreconditions.

Theorem transfer_high_to_low:
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH)
    related_states_h
    valid_state_h
    valid_prog_h,
    
    SelfSimulation
      LH
      valid_state_h
      valid_prog_h
      related_states_h ->
    
    StrongBisimulation R ->

    high_oracle_exists R ->
    
    oracle_refines_to_same_from_related R related_states_h ->

    exec_compiled_preserves_validity  R                           
    (refines_to_valid R valid_state_h) ->
    
    SelfSimulation
      LL
      (refines_to_valid R valid_state_h)
      (compiles_to_valid R valid_prog_h)
      (refines_to_related R related_states_h).
Proof.
  unfold refines_to_related, compiles_to_valid; intros.
  destruct H, H0.
  
  eapply Build_SelfSimulation;  intros; cleanup.
  match goal with
  | [H: high_oracle_exists _,
     H0: exec LL _ _ _ _ |- _] =>
    edestruct H; try apply H0; eauto
  end.
  
  match goal with
  | [H: refines_to _ s1 _ |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec LL _ _ _ _ -> _,
       H0: exec LL _ _ _ _,
       H1: forall _, exec LH _ _ _ _ -> _ |- _] =>
      eapply_fresh H in H0; cleanup; clear H H1
  end.


  match goal with
  | [H: refines_to_valid _ _ ?s,
     H0: refines_to _ ?s _,
     H1: refines_to_valid _ _ ?t,
     H2: refines_to _ ?t _ |- _] =>
    eapply_fresh H in H0;
      eapply_fresh H1 in H2; cleanup
  end.

  match goal with
    | [H: exec LH _ _ _ _ |- _] =>
      eapply_fresh self_simulation_correct in H; eauto; cleanup
  end.
  
  match goal with
  | [H: exec LH _ ?x2 _ _,
     H0: refines_to _ ?s1 ?x1,
     H1: refines_to _ ?s2 ?x2,      
     H2: refines_to_valid _ _ ?s2 |- _] =>
      eapply_fresh strong_bisimulation_correct in H1; eauto; cleanup
  end.
  
  match goal with
    | [H: forall _, exec LL _ _ _ _ -> _,
       H0: exec LH _ _ _ _,
       H1: forall _, exec LH _ _ _ _ -> _ |- _] =>
      eapply_fresh H1 in H0; cleanup; clear H H1
  end.  
  
  do 2 eexists; intuition eauto.

  match goal with
  |[ H0: oracle_refines_to_same_from_related _ _ |- _] =>
      eapply H0; eauto
  end.
  unfold refines_to_related; eauto. 
Qed.

Local Theorem bisimulation_to_comp_preserve:
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH),
    StrongBisimulation R ->
    forall T (p1 p2: LH.(prog) T),
       R.(compile) p1 = R.(compile) p2 ->
       (forall s o1 o2, R.(oracle_refines_to) s p1 o1 o2 -> R.(oracle_refines_to) s p2 o1 o2) ->
       (forall o s ret1 ret2,
          (exists s1 o1, R.(refines_to) s1 s /\
          R.(oracle_refines_to) s1 p1 o1 o) ->
          exec LH o s p1 ret1 ->
          exec LH o s p2 ret2 ->
          extract_ret ret1 = extract_ret ret2 /\
          exists s1', refines_to R s1'(extract_state ret1) /\
                 refines_to R s1'(extract_state ret2)).
Proof.
  intros.
  destruct H; cleanup.
  match goal with
  | [H: refines_to _ _ s |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec LL _ _ _ _ -> _,
       H0: exec LH _ _ _ _,
       H1: forall _, exec LH _ _ _ _ -> _ |- _] =>
      eapply_fresh H1 in H0; cleanup; clear H H1
  end.

  match goal with
  | [H: refines_to _ _ s |- _] =>
    eapply_fresh strong_bisimulation_correct in H
  end.

  2: apply H1; eauto.
  cleanup.
  match goal with
    | [H: forall _, exec LL _ _ _ _ -> _,
       H0: exec LL _ _ _ _,
       H1: forall _, exec LH _ _ _ _ -> _ |- _] =>
      eapply_fresh H in H0; cleanup; clear H H1
  end.

  destruct ret1, ret2, x1, x2; simpl in *; cleanup;
  eapply exec_deterministic_wrt_oracle in H4; eauto; cleanup;
  intuition eauto; cleanup; eauto.
Qed.
  

Theorem transfer_high_to_low_secret:
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH)
    related_states_h
    valid_state_h
    valid_prog_h
    T T' (p: T -> LH.(prog) T'),
    
    SelfSimulationForSecretInputs
      LH
      valid_state_h
      valid_prog_h
      related_states_h p ->
    
    StrongBisimulation R ->

    high_oracle_exists R ->

    (** We need compilation validity **)
    (forall T (p1 p2: LH.(prog) T),
       compile R p1 = compile R p2 ->
       valid_prog_h T p1 ->
       valid_prog_h T p2) ->
         
    (** 
        We need oracle refinement being invariant on high input.
        Merge this with oracle_refines_to_same_from_related 
        to get a statement that says
        "Oracle refinement is invariant on secrets." 
     **)
    (forall s t1 t2 o1 o2, R.(oracle_refines_to) s (p t1) o1 o2 -> R.(oracle_refines_to) s (p t2) o1 o2) ->
    
    SelfSimulationForSecretInputs
      LL
      (fun s => exists s', R.(refines_to) s s' /\ valid_state_h s')
      (compiles_to_valid R valid_prog_h)
      (refines_to_related R related_states_h)
      (fun t => R.(compile) (p t)).
Proof.
  unfold SelfSimulationForSecretInputs, refines_to_related, compiles_to_valid; intros.
  pose proof bisimulation_to_comp_preserve  as Hx.
  specialize Hx with (1:=H0).
  destruct H0; cleanup.

  rewrite <- H5 in H7. 
  match goal with
  | [H: high_oracle_exists _,
     H0: exec LL _ _ _ _ |- _] =>
    pose proof H; edestruct H; try apply H0; eauto
  end.

  match goal with
  | [H: refines_to _ s _ |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec LL _ _ _ _ -> _,
       H0: exec LL _ _ _ _,
       H1: forall _, exec LH _ _ _ _ -> _ |- _] =>
      eapply_fresh H in H0; cleanup; clear H H1
  end.

  eapply H in H10; try apply H9; eauto; cleanup.
  
  match goal with
  | [H: exec LH _ ?x2 _ _,
     H1: refines_to _ ?s2 ?x2  |- _] =>
      eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.
  
  eexists; intuition eauto.
Qed.









(*
Theorem transfer_high_to_low_for_valid_states :
  forall O1 O2 (low: Language O1) (high: Language O2)low high

    related_states_h
    refines_to
    compilation_of
    oracle_refines_to

    valid_state_h
    valid_prog_h,
    
    SelfSimulation
      high
      valid_state_h
      valid_prog_h
      related_states_h ->
    
    StrongBisimulationForValidStates
      low
      high
      (refines_to_valid
         refines_to
         valid_state_h)
      (compiles_to_valid
         valid_prog_h
         compilation_of)
      valid_state_h
      valid_prog_h
      compilation_of
      refines_to
      oracle_refines_to ->

    high_oracle_exists refines_to compilation_of oracle_refines_to ->
    
    SelfSimulation
      low
      (refines_to_valid
         refines_to
         valid_state_h)
      (compiles_to_valid
         valid_prog_h
         compilation_of)
      (refines_to_related
         refines_to
         related_states_h).
Proof.
  unfold refines_to_related, compiles_to_valid; intros.
  destruct H, H0.
  
  eapply Build_SelfSimulation;  intros; cleanup.

  (* PROBLEM: this requires for us to know that low oracle refines to some high oracle for s1 *)
  (* SUGGESTION : exec low -> existence of high oracle *)
  assume (Axiom1 : (forall T o1 s1 s1' p1 p2,
             exec low T o1 s1 p1 s1' ->
             compilation_of T p1 p2 ->
             exists o2, oracle_refines_to T s1 p2 o1 o2)).
  edestruct Axiom1; eauto.
  (*
  match goal with
  | [H: refines_to ?s _,
     H0: compilation_of _ ?p _,
     H1: forall _ _,
       refines_to ?s _ ->
       compilation_of _ ?p _ -> _ |- _] =>
    specialize H1 with (1:=H)(2:=H0); cleanup
  end.  
  *)
  
  match goal with
  | [H: refines_to s1 _ |- _] =>
    eapply_fresh strong_bisimulation_for_valid_states_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec low _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply_fresh  H in H0; cleanup; clear H H1
  end.

  match goal with
  | [H: refines_to_valid _ _ ?s,
     H0: refines_to ?s _,
     H1: refines_to_valid _ _ ?t,
     H2: refines_to ?t _ |- _] =>
    eapply_fresh H in H0;
      eapply_fresh H1 in H2; cleanup
  end.

  match goal with
    | [H: exec high _ _ _ _ _ |- _] =>
      eapply_fresh self_simulation_correct in H; eauto; cleanup
  end.

  (* PROBLEM: this requires for us to know that low oracle refines to some high oracle for s2 *)
  (* SUGGESTION : exec high -> existence of low oracle *)
  assume (Axiom2 : (forall T o2 s2 s2' l2 p2,
             exec high T o2 s2 p2 s2' ->
             refines_to l2 s2 ->
             exists o1, oracle_refines_to T l2 p2 o1 o2)).
  edestruct Axiom2; eauto.
  
  match goal with
  | [H: exec high _ _ ?x2 _ _,
     H0: refines_to ?s1 ?x1,
     H1: refines_to ?s2 ?x2,      
     H2: refines_to_valid _ _ ?s2 |- _] =>
      eapply_fresh strong_bisimulation_for_valid_states_correct in H1; eauto; cleanup
  end.
  
  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec high _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply_fresh H1 in H0; cleanup; clear H H1
  end.

  (* PROBLEM: two low oracles need to be the same *)
  (* SUGGESTION : oracle refinement is deterministic *)
  assume (Axiom3 : (forall T ol1 ol2 oh s1 s2 p2,
             oracle_refines_to T s1 p2 ol1 oh ->
             oracle_refines_to T s2 p2 ol2 oh ->
             ol1 = ol2)).
  
  match goal with
    | [H: oracle_refines_to _ _ _ _ _,
       H0: oracle_refines_to _ _ _ _ _ |- _] =>
      specialize Axiom3 with (1:=H)(2:=H0); cleanup
  end.
  
  
  do 2 eexists; intuition eauto.
  do 2 (eapply result_same_transitive; eauto).
  apply result_same_symmetric; auto.
  
  repeat match goal with
  | [H: forall _, extract_ret _ ?a = _ |- extract_ret _ ?a = _] =>
    rewrite H; auto
  end.
Abort.



Lemma bisimulation_weaken_valid_prog:
  forall O1 O2 (low: Language O1) (high: Language O2)low high

    refines_to
    compilation_of
    oracle_refines_to

    valid_state_h
    (valid_prog_h1
    valid_prog_h2: forall T, high.(prog) T -> Prop),

    (forall (T: Type) (p: Prog high T), valid_prog_h1 T p -> valid_prog_h2 T p) ->
    
    StrongBisimulationForValidStates
      low
      high
      (refines_to_valid
         refines_to
         valid_state_h)
      (compiles_to_valid
         valid_prog_h2
         compilation_of)
      valid_state_h
      valid_prog_h2
      compilation_of
      refines_to
      oracle_refines_to ->

    StrongBisimulationForValidStates
      low
      high
      (refines_to_valid
         refines_to
         valid_state_h)
      (compiles_to_valid
         valid_prog_h1
         compilation_of)
      valid_state_h
      valid_prog_h1
      compilation_of
      refines_to
      oracle_refines_to.
Proof.
  intros.
  destruct H0.
  constructor; intros.
  eapply strong_bisimulation_for_valid_states_correct; eauto.
  unfold compiles_to_valid in *; cleanup.
  eexists; eauto.
Qed.
*)

Lemma bisimulation_restrict_state:
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH)
    valid_state_h
    valid_prog_h,
    
  StrongBisimulation R ->

  exec_compiled_preserves_validity R                             
    (refines_to_valid R valid_state_h) ->

  exec_preserves_validity LH valid_state_h -> 
  
  StrongBisimulationForValidStates R
     (refines_to_valid R valid_state_h)
     valid_state_h
     valid_prog_h.
Proof.
  intros.
  destruct H.
  constructor; intros.
  edestruct strong_bisimulation_correct; eauto.
  split; intros.
  edestruct H4; eauto; cleanup.
  eexists; intuition (eauto).

  edestruct H5; eauto; cleanup.
  eexists; intuition (eauto).
Qed.

Lemma bisimulation_restrict_prog:
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH),
    (forall T (p: LH.(prog) T), StrongBisimulationForProgram R p) ->
    StrongBisimulation R.
Proof.
  intros.
  constructor; intros.
  specialize (H T p2).
  destruct H.
  edestruct strong_bisimulation_for_program_correct; eauto.
Qed.


