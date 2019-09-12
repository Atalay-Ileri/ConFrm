Require Import List CommonAutomation.

Inductive Result {State T: Type} :=
| Finished : State -> T -> @Result State T
| Crashed : State -> @Result State T.

Definition extract_state {State T} (res: @Result State T) :=
  match res with
  | Finished s _ | Crashed s => s
  end.

Definition extract_ret {State T} def (res: @Result State T) :=
  match res with
  | Finished _ r => r
  | Crashed _ => def
  end.

Definition result_same {State1 State2 T1 T2} (res1: @Result State1 T1) (res2: @Result State2 T2) :=
  match res1, res2 with
  | Finished _ _, Finished _ _ | Crashed _, Crashed _ => True
  | _, _ => False
  end.

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
    State : Type;
    Op : Type -> Type;
    transition : forall T, State -> Op T -> @Result State T -> Prop;
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

Definition compiles_to_valid {Op1 Op2: Type -> Type}
           (valid_op2: forall T, Op2 T -> Prop)
           (compiles_to: forall T, Op2 T -> Op1 T -> Prop)  T (o1: Op1 T) :=
  exists o2, compiles_to T o2 o1 /\ valid_op2 T o2.


Record SelfSimulation (lts: LTS)
       (valid_state: State lts -> Prop)
       (valid_op: forall T, Op lts T -> Prop)
       (R: State lts -> State lts -> Prop) :=
  {
    self_simulation_correct:
      forall T o s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_op T o ->
        (transition lts) T s1 o s1' ->
        R s1 s2 ->
        exists s2',
          (transition lts) T s2 o s2' /\
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
       (refines_to: State lts1 -> State lts2 -> Prop):=
  {
    strong_bisimulation_correct:
      (forall T o1 o2 s1 s2,
          valid_state1 s1 ->
          valid_op1 T o1 ->
          
          valid_state2 s2 ->
          valid_op2 T o2 ->
          
          refines_to s1 s2 ->
          compiles_to T o2 o1 ->
          
          (forall s1',
              (transition lts1) T s1 o1 s1' ->
              exists s2',
                (transition lts2) T s2 o2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2') /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')) /\
          (forall s2',
              (transition lts2) T s2 o2 s2' ->
              exists s1',
                (transition lts1) T s1 o1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')/\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')))
  }.

Theorem transfer_high_to_low :
  forall low high eqv_h refines_to compiles_to valid_h valid_op_h,
    SelfSimulation high
                   valid_h
                   valid_op_h
                   eqv_h ->
    StrongBisimulation low high
                       (refines_to_valid refines_to valid_h)
                       (compiles_to_valid valid_op_h compiles_to)
                       valid_h
                       valid_op_h
                       compiles_to refines_to ->
    SelfSimulation low
                   (refines_to_valid refines_to valid_h)
                   (compiles_to_valid  valid_op_h compiles_to)
                   (refines_to_related refines_to eqv_h).
Proof.
  unfold refines_to_related, compiles_to_valid; intros.
  destruct H, H0.
  rename self_simulation_correct0 into self_simulation_correct.
  rename strong_bisimulation_correct0 into strong_bisimulation_correct.
  
  eapply Build_SelfSimulation;  intros; cleanup.
  eapply strong_bisimulation_correct in H3 as Hx; eauto; cleanup.
  eapply H7 in H2; cleanup.
  clear H7 H8.

  eapply_fresh H in H3.
  eapply_fresh H0 in H4.
  eapply self_simulation_correct in H2; eauto; cleanup.  
  
  eapply_fresh strong_bisimulation_correct in H4; eauto; cleanup.
  apply H17 in H2; cleanup.
  clear H15 H17.
  eexists; intuition eauto.
  do 2 (eapply result_same_transitive; eauto).
  apply result_same_symmetric; auto.
  rewrite H11, H20; auto.  
Qed.