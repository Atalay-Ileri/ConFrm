Require Import List.

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

Record SelfSimulation (lts: LTS) (R: State lts -> State lts -> Prop):=
  {
    self_simulation_correct:
      forall T o s1 s1' s2,
        (transition lts) T s1 o s1' ->
        R s1 s2 ->
        exists s2',
          (transition lts) T s2 o s2' /\
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2');
  }.

Record StrongBisimulation  (lts1 lts2 : LTS) (compile: forall T, Op lts2 T -> Op lts1 T) (refines_to: State lts1 -> State lts2 -> Prop):=
  {
    strong_bisimulation_correct:
      (forall T o2 s1 s2,
          refines_to s1 s2 ->
          (forall s1',
              (transition lts1) T s1 (compile T o2) s1' ->
              exists s2',
                (transition lts2) T s2 o2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              (transition lts2) T s2 o2 s2' ->
              exists s1',
                (transition lts1) T s1 (compile T o2) s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.



Definition right_total {T1 T2: Type} (R: T1 -> T2 -> Prop) :=
  forall t2, exists t1, R t1 t2.

Definition refines_to_related {T1 T2} refines_to eqv_h (st1 st2: T1) :=
  exists (sr1 sr2: T2),
    refines_to st1 sr1 /\
    refines_to st2 sr2 /\
    eqv_h sr1 sr2.

Definition deterministic_refinement {T1 T2} refines_to eqv_h :=
  forall (s:T1) (sr1 sr2: T2),
    refines_to s sr1 ->
    refines_to s sr2 ->
    eqv_h sr1 sr2.

Definition transitive {T} (R: T -> T -> Prop) :=
  forall t t' t'', R t t' -> R t' t'' -> R t t''.




Theorem transfer_low_to_high :
  forall low high eqv_h refines_to compile,
    SelfSimulation low (refines_to_related refines_to eqv_h) ->
    StrongBisimulation low high compile refines_to ->
    right_total refines_to ->
    deterministic_refinement refines_to eqv_h ->
    transitive eqv_h ->
    SelfSimulation high eqv_h.
Proof.
  unfold right_total, refines_to_related, deterministic_refinement; intros.
  destruct H, H0.
  rename self_simulation_correct0 into self_simulation_correct.
  rename H1 into right_total_state.
  rename strong_bisimulation_correct0 into strong_bisimulation_correct.
  
  eapply Build_SelfSimulation;  intros.
  edestruct (right_total_state s1), (right_total_state s2).
  eapply strong_bisimulation_correct in H1 as Hx; destruct Hx.
  apply H6 in H.
  repeat destruct H. destruct H7, H8.
  
  eapply self_simulation_correct in H; eauto; repeat destruct H. destruct H10, H11.
  repeat destruct H11.
  destruct H13.
  
  eapply strong_bisimulation_correct in H4 as Hx; destruct Hx.
  apply H15 in H.
  destruct H, H, H17, H18.
  eexists; intuition eauto.
  do 2 (eapply result_same_transitive; eauto).
  apply result_same_symmetric; auto.
  rewrite <- H9, H12; auto.
Qed.

