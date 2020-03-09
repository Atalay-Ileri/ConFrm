Require Import List Primitives Simulation.Definitions.

Theorem transfer_high_to_low:
  forall low high

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
    
    StrongBisimulation
      low
      high
      compilation_of
      refines_to
      oracle_refines_to ->

    high_oracle_exists refines_to compilation_of oracle_refines_to ->
    
    oracle_refines_to_same_from_related refines_to related_states_h oracle_refines_to ->

    exec_compiled_preserves_validity
    low
    high
    compilation_of                               
    (refines_to_valid
       refines_to
       valid_state_h) ->
    
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
  match goal with
  | [H: high_oracle_exists _ _ _,
     H0: exec low _ _ _ _ _ |- _] =>
    edestruct H; try apply H0; eauto
  end.
  
  match goal with
  | [H: refines_to s1 _ |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec low _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply_fresh H in H0; cleanup; clear H H1
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
  
  match goal with
  | [H: exec high _ _ ?x2 _ _,
     H0: refines_to ?s1 ?x1,
     H1: refines_to ?s2 ?x2,      
     H2: refines_to_valid _ _ ?s2 |- _] =>
      eapply_fresh strong_bisimulation_correct in H1; eauto; cleanup
  end.
  
  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec high _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply_fresh H1 in H0; cleanup; clear H H1
  end.  
  
  do 2 eexists; intuition eauto.
  do 2 (eapply result_same_transitive; eauto).
  apply result_same_symmetric; auto.
  
  repeat match goal with
  | [H: forall _, extract_ret _ ?a = _ |- extract_ret _ ?a = _] =>
    rewrite H; auto
         end.

  match goal with
  |[ H0: oracle_refines_to_same_from_related _ _ _ |- _] =>
      eapply H0; eauto
  end.
  unfold refines_to_related; eauto. 
Qed.




Theorem transfer_high_to_low_for_valid_states :
  forall low high

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
  forall low high

    refines_to
    compilation_of
    oracle_refines_to

    valid_state_h
    (valid_prog_h1
    valid_prog_h2: forall T, Prog high T -> Prop),

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


Lemma bisimulation_restrict_state:
  forall low high

    refines_to
    compilation_of
    oracle_refines_to

    valid_state_h
    valid_prog_h,
    
  StrongBisimulation
      low
      high
      compilation_of
      refines_to
      oracle_refines_to ->

  exec_compiled_preserves_validity
    low
    high
    compilation_of                               
    (refines_to_valid
       refines_to
       valid_state_h) ->

  exec_preserves_validity high valid_state_h -> 
  
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
      oracle_refines_to.
Proof.
  intros.
  destruct H.
  constructor; intros.
  edestruct strong_bisimulation_correct; eauto.
  split; intros.
  edestruct H6; eauto; cleanup.
  eexists; intuition (eauto).

  edestruct H7; eauto; cleanup.
  eexists; intuition (eauto).
Qed.


Lemma bisimulation_restrict_prog:
  forall low high

    refines_to
    compilation_of
    oracle_refines_to,
    
    (forall T (p: Prog high T),
      StrongBisimulationForProgram
      low
      high
      compilation_of
      refines_to
      oracle_refines_to
      p) ->
  
  StrongBisimulation
      low
      high
      compilation_of
      refines_to
      oracle_refines_to.
Proof.
  intros.
  constructor; intros.
  specialize (H T p2).
  destruct H.
  edestruct strong_bisimulation_for_program_correct; eauto.
Qed.