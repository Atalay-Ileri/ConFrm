Require Import List CommonAutomation Simulation.

Lemma result_same_transitive:
  forall State1 State2 State3 T1 T2 T3
    (res1: @Result State1 T1)
    (res2: @Result State2 T2)
    (res3: @Result State3 T3),
    result_same res1 res2 ->
    result_same res2 res3 ->
    result_same res1 res3.
Proof.
  unfold result_same; intros.
  destruct res1, res2, res3; intuition.
Qed.

Lemma result_same_symmetric:
  forall State1 State2 T1 T2
    (res1: @Result State1 T1)
    (res2: @Result State2 T2),
    result_same res1 res2 ->
    result_same res2 res1.
Proof.
  unfold result_same; intros.
  destruct res1, res2; intuition.
Qed.

Record LTS :=
  {
    Token : Type;
    State : Type;
    Op : Type -> Type;
    transition : forall T, list Token -> State -> Op T -> @Result State T -> Prop;
  }.

Definition refines_to_related {T1 T2} refines_to (R: T2 -> T2 -> Prop) (st1 st2: T1) :=
  exists (sr1 sr2: T2),
    refines_to st1 sr1 /\
    refines_to st2 sr2 /\
    R sr1 sr2.

Definition refines_to_valid {T1 T2} (refines_to: T1 -> T2 -> Prop) (valid2: T2 -> Prop) (st1: T1) : Prop :=
  forall (st2: T2),
    refines_to st1 st2 ->
    valid2 st2.

Definition oracle_refines_to_valid
           {State1 State2 Oracle1 Oracle2: Type} {Op1 Op2: Type -> Type}
           (oracle_refines_to: forall T, State1 -> Op2 T -> Oracle1 -> Oracle2 -> Prop)
           (refines_to: State1 -> State2 -> Prop)
           (compiles_to: forall T, Op2 T -> Op1 T -> Prop)
           (valid_oracle2: forall T, Oracle2 -> State2 -> Op2 T -> Prop)
           T (o1: Oracle1) (st1: State1) (p1: Op1 T) :=
  forall st2 p2,
    refines_to st1 st2 ->
    compiles_to T p2 p1 ->
    exists o2, oracle_refines_to T st1 p2 o1 o2 /\
    valid_oracle2 T o2 st2 p2.

Definition compiles_to_valid {Op1 Op2: Type -> Type}
           (valid_op2: forall T, Op2 T -> Prop)
           (compiles_to: forall T, Op2 T -> Op1 T -> Prop)  T (o1: Op1 T) :=
  exists o2, compiles_to T o2 o1 /\ valid_op2 T o2.

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
       (valid_op: forall T, Op lts T -> Prop)
       (valid_oracle: forall T, list (Token lts) -> State lts -> Op lts T -> Prop)
       (R: State lts -> State lts -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_op T p ->
        valid_oracle T o s1 p ->
        valid_oracle T o s2 p ->
        (transition lts) T o s1 p s1' ->
        R s1 s2 ->
        exists s2',
          (transition lts) T o s2 p s2' /\
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2') /\
          valid_state (extract_state s1') /\
          valid_state (extract_state s2') ;
  }.

Record StrongBisimulation
       (lts1 lts2 : LTS)
       (valid_state1 : State lts1 -> Prop)
       (valid_op1: forall T, Op lts1 T -> Prop)
       (valid_state2 : State lts2 -> Prop)
       (valid_op2: forall T, Op lts2 T -> Prop)
       (compiles_to: forall T, Op lts2 T -> Op lts1 T -> Prop)
       (refines_to: State lts1 -> State lts2 -> Prop)
       (oracle_refines_to: forall T, State lts1 -> Op lts2 T -> list (Token lts1) -> list (Token lts2) -> Prop)
  :=
  {
    strong_bisimulation_correct:
      (forall T p1 p2 o1 o2 s1 s2,
          valid_state1 s1 ->
          valid_op1 T p1 ->
          
          valid_state2 s2 ->
          valid_op2 T p2 ->
          
          refines_to s1 s2 ->
          compiles_to T p2 p1 ->
          
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              (transition lts1) T o1 s1 p1 s1' ->
              exists s2',
                (transition lts2) T o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2') /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')) /\
          (forall s2',
              (transition lts2) T o2 s2 p2 s2' ->
              exists s1',
                (transition lts1) T o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')/\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')))
  }.

Theorem transfer_high_to_low :
  forall low high

    eqv_h
    refines_to
    compiles_to
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
         compiles_to)
      valid_h
      valid_op_h
      compiles_to
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
         compiles_to)
      (oracle_refines_to_valid
         oracle_refines_to
         refines_to
         compiles_to
         valid_oracle_h)
      (refines_to_related
         refines_to
         eqv_h).
Proof.
  unfold refines_to_related, compiles_to_valid, oracle_refines_to_valid, oracle_equal_with_respect_to; intros.
  destruct H, H0.
  rename self_simulation_correct0 into self_simulation_correct.
  rename strong_bisimulation_correct0 into strong_bisimulation_correct.
  
  eapply Build_SelfSimulation;  intros; cleanup.
  repeat match goal with
    | [H: forall (st2 : State high) (p2 : Op high T), _ |- _] =>
      edestruct H; eauto; cleanup; clear H
  end.
  eapply_fresh H1 in H10; eauto; cleanup.

  match goal with
  | [H: refines_to s1 _ |- _] =>
    eapply_fresh strong_bisimulation_correct in H; eauto; cleanup
  end.

  match goal with
    | [H: forall _, transition low _ _ _ _ _ -> _,
       H0: transition low _ _ _ _ _,
       H1: forall _, transition high _ _ _ _ _ -> _ |- _] =>
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
    | [H: transition high _ _ _ _ _ |- _] =>
      eapply self_simulation_correct in H; eauto; cleanup
  end.

  match goal with
  | [H: transition high _ _ ?x2 _ _,
     H0: refines_to ?s1 ?x1,
     H1: refines_to ?s2 ?x2,      
     H2: refines_to_valid _ _ ?s2 |- _] =>
      eapply strong_bisimulation_correct in H1; eauto; cleanup
  end.
  
  match goal with
    | [H: forall _, transition low _ _ _ _ _ -> _,
       H0: transition high _ _ _ _ _,
       H1: forall _, transition high _ _ _ _ _ -> _ |- _] =>
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