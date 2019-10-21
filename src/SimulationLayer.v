Require Import List CommonAutomation Simulation.

Record LTS :=
  {
    Oracle : Type;
    State : Type;
    Prog : Type -> Type;
    exec : forall T, Oracle -> State -> Prog T -> @Result State T -> Prop;
  }.


(* 
A relation that takes 
   - two input states (sl1 and sl2), 
   - a refinement realiton (refines_to), and
   - a relation (related_h)
and asserts that 
    - there are two other states (sh1 and sh2) such that,
    - sl1 (sl2) refines to sh1 (sh2) via refines_to relation, and
    - sh1 and sh2 are related via related_h
*)
Definition refines_to_related {State_L State_H: Type}
           (refines_to: State_L -> State_H -> Prop)
           (related_h: State_H -> State_H -> Prop)
           (sl1 sl2: State_L)
  : Prop :=
  exists (sh1 sh2: State_H),
    refines_to sl1 sh1 /\
    refines_to sl2 sh2 /\
    related_h sh1 sh2.

(* 
A relation that takes 
   - an input state (sl), 
   - a refinement realiton (refines_to), and
   - a validity predicate (valid_state_h)
and asserts that 
    - for all states sh,
    - if sl refines to sh via refines_to relation,
    - then sh is a valid state (satisfies valid_state_h)
*)
Definition refines_to_valid {State_L State_H: Type}
           (refines_to: State_L -> State_H -> Prop)
           (valid_state_h: State_H -> Prop)
           (sl: State_L)
  : Prop :=
  forall (sh: State_H),
    refines_to sl sh ->
    valid_state_h sh.

(* 
A relation that takes 
   - an input program (pl), 
   - a refinement realiton (refines_to), and
   - a validity predicate (valid_prog_h)
and asserts that 
    - there is a program ph such that,
    - pl is compilation of ph, and
    - ph is a valid program (satisafies valid_prog_h)
*)
Definition compiles_to_valid {Prog_L Prog_H: Type -> Type} 
           (valid_prog_h: forall T, Prog_H T -> Prop)
           (compilation_of: forall T, Prog_L T -> Prog_H T -> Prop)
           (T: Type)
           (pl: Prog_L T)
  : Prop :=
  exists (ph: Prog_H T),
    compilation_of T pl ph /\
    valid_prog_h T ph.

Definition exec_preserves_validity lts valid_state :=
    forall T (p: Prog lts T) o s ret,
      valid_state s ->
      exec lts T o s p ret ->
      valid_state (extract_state ret).

Definition exec_compiled_preserves_validity lts1 lts2 (compilation_of: forall T, Prog lts1 T -> Prog lts2 T -> Prop) valid_state :=
    forall T (p1: Prog lts1 T) (p2: Prog lts2 T) o s ret,
      compilation_of T p1 p2 ->
      valid_state s ->
      exec lts1 T o s p1 ret ->
      valid_state (extract_state ret).

(*
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
*)
Record SelfSimulation (lts: LTS)
       (valid_state: State lts -> Prop)
       (valid_prog: forall T, Prog lts T -> Prop)
       (R: State lts -> State lts -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_prog T p ->
        (exec lts) T o s1 p s1' ->
        R s1 s2 ->
        exists s2',
          (exec lts) T o s2 p s2' /\
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2') /\
          valid_state (extract_state s1') /\
          valid_state (extract_state s2') ;
  }.

Record StrongBisimulationForValidStates
       (lts1 lts2 : LTS)
       (valid_state1 : State lts1 -> Prop)
       (valid_prog1: forall T, Prog lts1 T -> Prop)
       (valid_state2 : State lts2 -> Prop)
       (valid_prog2: forall T, Prog lts2 T -> Prop)
       (compilation_of: forall T, Prog lts1 T -> Prog lts2 T -> Prop)
       (refines_to: State lts1 -> State lts2 -> Prop)
       (oracle_refines_to: forall T, State lts1 -> Prog lts2 T -> Oracle lts1 -> Oracle lts2 -> Prop)
  :=
  {
    strong_bisimulation_for_valid_states_correct:
      (forall T p1 p2 s1 s2 o1 o2,
          valid_state1 s1 ->
          valid_prog1 T p1 ->
          
          valid_state2 s2 ->
          valid_prog2 T p2 ->
          
          refines_to s1 s2 ->
          compilation_of T p1 p2 ->
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              (exec lts1) T o1 s1 p1 s1' ->
              exists s2',
                (exec lts2) T o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2') /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')) /\
          (forall s2',
              (exec lts2) T o2 s2 p2 s2' ->
              exists s1',
                (exec lts1) T o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')/\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')))
  }.


Record StrongBisimulationForProgram
       (lts1 lts2 : LTS)
       (compilation_of: forall T, Prog lts1 T -> Prog lts2 T -> Prop)
       (refines_to: State lts1 -> State lts2 -> Prop)
       (oracle_refines_to: forall T, State lts1 -> Prog lts2 T -> Oracle lts1 -> Oracle lts2 -> Prop)
       {T} (p2: Prog lts2 T)
  :=
  {
    strong_bisimulation_for_program_correct:
      (forall p1 s1 s2 o1 o2,
          
          refines_to s1 s2 ->
          compilation_of T p1 p2 ->
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              (exec lts1) T o1 s1 p1 s1' ->
              exists s2',
                (exec lts2) T o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              (exec lts2) T o2 s2 p2 s2' ->
              exists s1',
                (exec lts1) T o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.

Record StrongBisimulation
       (lts1 lts2 : LTS)
       (compilation_of: forall T, Prog lts1 T -> Prog lts2 T -> Prop)
       (refines_to: State lts1 -> State lts2 -> Prop)
       (oracle_refines_to: forall T, State lts1 -> Prog lts2 T -> Oracle lts1 -> Oracle lts2 -> Prop)
  :=
  {
    strong_bisimulation_correct:
      (forall T p1 (p2: Prog lts2 T) s1 s2 o1 o2,
          
          refines_to s1 s2 ->
          compilation_of T p1 p2 ->
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              (exec lts1) T o1 s1 p1 s1' ->
              exists s2',
                (exec lts2) T o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              (exec lts2) T o2 s2 p2 s2' ->
              exists s1',
                (exec lts1) T o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.

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
  edestruct strong_bisimulation_correct0; eauto.
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
  edestruct strong_bisimulation_for_program_correct0; eauto.
Qed.

Theorem transfer_high_to_low :
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
  rename self_simulation_correct0 into self_simulation_correct.
  rename strong_bisimulation_for_valid_states_correct0 into strong_bisimulation_correct.
  
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
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
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
      eapply_fresh strong_bisimulation_correct in H1; eauto; cleanup
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
  eapply strong_bisimulation_for_valid_states_correct0; eauto.
  unfold compiles_to_valid in *; cleanup.
  eexists; eauto.
Qed.
