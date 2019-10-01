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

Definition oracle_refines_to_valid
           {State1 State2 Oracle1 Oracle2: Type} {Op1 Op2: Type -> Type}
           (oracle_refines_to: forall T, State1 -> Op2 T -> Oracle1 -> Oracle2 -> Prop)
           (refines_to: State1 -> State2 -> Prop)
           (compilation_of: forall T, Op1 T -> Op2 T -> Prop)
           (valid_oracle2: forall T, Oracle2 -> State2 -> Op2 T -> Prop)
           T (o1: Oracle1) (st1: State1) (p1: Op1 T) :=
  forall st2 p2,
    refines_to st1 st2 ->
    compilation_of T p1 p2 ->
    exists o2, oracle_refines_to T st1 p2 o1 o2 /\
    valid_oracle2 T o2 st2 p2.

Record SelfSimulation (lts: LTS)
       (valid_state: State lts -> Prop)
       (valid_op: forall T, Prog lts T -> Prop)
       (R: State lts -> State lts -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_op T p ->
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

Record StrongBisimulation
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
    strong_bisimulation_correct:
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
    
    StrongBisimulation
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
  unfold refines_to_related, compiles_to_valid, oracle_refines_to_valid; intros.
  destruct H, H0.
  rename self_simulation_correct0 into self_simulation_correct.
  rename strong_bisimulation_correct0 into strong_bisimulation_correct.
  
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







(*
Definition oracle_refines_to_valid
           {State1 State2 Oracle1 Oracle2: Type} {Op1 Op2: Type -> Type}
           (oracle_refines_to: forall T, State1 -> Op2 T -> Oracle1 -> Oracle2 -> Prop)
           (refines_to: State1 -> State2 -> Prop)
           (compilation_of: forall T, Op1 T -> Op2 T -> Prop)
           (valid_oracle2: forall T, Oracle2 -> State2 -> Op2 T -> Prop)
           T (o1: Oracle1) (st1: State1) (p1: Op1 T) :=
  forall st2 p2,
    refines_to st1 st2 ->
    compilation_of T p1 p2 ->
    exists o2, oracle_refines_to T st1 p2 o1 o2 /\
    valid_oracle2 T o2 st2 p2.



Definition oracle_equal_with_respect_to
           {State Oracle1 Oracle2: Type} {Op: Type -> Type}
           (related: State -> State -> Prop)
           (oracle_refines_to: forall T, State -> Op T -> Oracle1 -> Oracle2 -> Prop):=
  forall T o1 o2 o2' st1 st2 p,
    oracle_refines_to T st1 p o1 o2 ->
    oracle_refines_to T st2 p o1 o2' ->
    related st1 st2 ->
    o2 = o2'.


Record SelfSimulation (lts: LTS)
       (valid_state: State lts -> Prop)
       (valid_op: forall T, Prog lts T -> Prop)
       (valid_oracle: forall T, list (Token lts) -> State lts -> Prog lts T -> Prop)
       (R: State lts -> State lts -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_op T p ->
        valid_oracle T o s1 p ->
        valid_oracle T o s2 p ->
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

Record StrongBisimulation
       (lts1 lts2 : LTS)
       (valid_state1 : State lts1 -> Prop)
       (valid_op1: forall T, Prog lts1 T -> Prop)
       (valid_state2 : State lts2 -> Prop)
       (valid_op2: forall T, Prog lts2 T -> Prop)
       (compilation_of: forall T, Prog lts1 T -> Prog lts2 T -> Prop)
       (refines_to: State lts1 -> State lts2 -> Prop)
       (oracle_refines_to: forall T, State lts1 -> Prog lts2 T -> list (Token lts1) -> list (Token lts2) -> Prop)
  :=
  {
    strong_bisimulation_correct:
      (forall T p1 p2 o1 o2 s1 s2,
          valid_state1 s1 ->
          valid_op1 T p1 ->
          
          valid_state2 s2 ->
          valid_op2 T p2 ->
          
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

Theorem transfer_high_to_low :
  forall low high

    eqv_h
    refines_to
    compilation_of
    oracle_refines_to

    valid_h
    valid_op_h
    valid_oracle_h,
    
    SelfSimulation
      high
      valid_h
      valid_op_h
      valid_oracle_h
      eqv_h ->
    
    StrongBisimulation
      low
      high
      (refines_to_valid
         refines_to
         valid_h)
      (compiles_to_valid
         valid_op_h
         compilation_of)
      valid_h
      valid_op_h
      compilation_of
      refines_to
      oracle_refines_to ->

    oracle_equal_with_respect_to
      (refines_to_related
         refines_to
         eqv_h)
      oracle_refines_to ->
    
    SelfSimulation
      low
      (refines_to_valid
         refines_to
         valid_h)
      (compiles_to_valid
         valid_op_h
         compilation_of)
      (oracle_refines_to_valid
         oracle_refines_to
         refines_to
         compilation_of
         valid_oracle_h)
      (refines_to_related
         refines_to
         eqv_h).
Proof.
  unfold refines_to_related, compiles_to_valid, oracle_refines_to_valid, oracle_equal_with_respect_to; intros.
  destruct H, H0.
  rename self_simulation_correct0 into self_simulation_correct.
  rename strong_bisimulation_correct0 into strong_bisimulation_correct.
  rename H1 into oracle_equal.
  
  eapply Build_SelfSimulation;  intros; cleanup.
  repeat match goal with
    | [H: forall (_ : State high) (_ : Prog high _), _ |- _] =>
      edestruct H; eauto; cleanup; clear H
         end.
  
  match goal with
  | [H: oracle_refines_to _ _ _ _ _,
     H0: oracle_refines_to _ _ _ _ _ |- _] =>
    eapply_fresh oracle_equal in H;
      try apply H0; eauto; cleanup
  end.
  
  match goal with
  | [H: refines_to s1 _ |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec low _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply H in H0; cleanup; clear H H1
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
      eapply self_simulation_correct in H; eauto; cleanup
  end.

  match goal with
  | [H: exec high _ _ ?x2 _ _,
     H0: refines_to ?s1 ?x1,
     H1: refines_to ?s2 ?x2,      
     H2: refines_to_valid _ _ ?s2 |- _] =>
      eapply strong_bisimulation_correct in H1; eauto; cleanup
  end.
  
  match goal with
    | [H: forall _, exec low _ _ _ _ _ -> _,
       H0: exec high _ _ _ _ _,
       H1: forall _, exec high _ _ _ _ _ -> _ |- _] =>
      eapply H1 in H0; cleanup; clear H H1
  end.

  eexists; intuition eauto.
  do 2 (eapply result_same_transitive; eauto).
  apply result_same_symmetric; auto.
  
  repeat match goal with
  | [H: forall _, extract_ret _ ?a = _ |- extract_ret _ ?a = _] =>
    rewrite H; auto
  end.
Qed.
*)