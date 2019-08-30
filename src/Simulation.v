Require Import List.

Record Equivalence (T: Type) :=
  {
    eq : T -> T -> Prop;
    
    eq_refl: forall t, eq t t;
    eq_sym: forall t t', eq t t' -> eq t' t;
    eq_trans: forall t t' t'', eq t t' -> eq t' t'' -> eq t t'';
  }.

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

Definition map_state {State1 State2 T} (f:State1 -> State2) (res: @Result State1 T) :=
  match res with
  | Finished s v => Finished (f s) v
  | Crashed s => Crashed (f s)
  end.

Lemma extract_state_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T),
    extract_state (map_state R r) = R (extract_state r).
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Lemma extract_ret_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T) def,
    extract_ret def (map_state R r) = extract_ret def r.
Proof.
  intros; destruct r; simpl; eauto.
Qed.

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

Definition flip {T1 T2} (R: T1 -> T2 -> Prop) := fun t2 t1 => R t1 t2.

Record LTS :=
  {
    State : Type;
    Op : Type -> Type;
    transition : forall T, State -> Op T -> @Result State T -> Prop;
  }.

Record Simulation (lts1 lts2 : LTS) (R: State lts1 -> State lts2 -> Prop):=
  {
    simulation_correct:
      forall T o1 s1 s1' s2,
        (transition lts1) T s1 o1 s1' ->
        R s1 s2 ->
        exists o2 s2',
          (transition lts2) T s2 o2 s2' /\
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2');
  }.

Record Bisimulation  (lts1 lts2 : LTS) (R: State lts1 -> State lts2 -> Prop):=
  {
    bisimulation_correct:
      Simulation lts1 lts2 R /\
      Simulation lts2 lts1 (flip R)
  }.

Definition right_total {T1 T2: Type} (R: T1 -> T2 -> Prop) :=
  forall t2, exists t1, R t1 t2.

Definition left_total {T1 T2: Type} (R: T1 -> T2 -> Prop) :=
  forall t1, exists t2, R t1 t2.

Definition simulation_preserving {T1 T2: Type} (S1: T1 -> T1 -> Prop) (S2: T2 -> T2 -> Prop)(R: T1 -> T2 -> Prop) :=
  forall t1 t1' t2 t2',
    R t1 t2 ->
    R t1' t2' ->
    S1 t1 t1' <-> S2 t2 t2'.

Theorem transfer_low_to_high :
  forall low high SL SH R,
  Simulation low low SL ->
  Bisimulation low high R ->
  right_total R ->
  simulation_preserving SL SH R ->
  Simulation high high SH.
Proof.
  unfold right_total, simulation_preserving; intros.
  destruct H, H0.
  rename simulation_correct0 into simulation_correct.
  rename H2 into simulation_preserving.
  rename H1 into right_total.
  destruct bisimulation_correct0
    as [bisimulation_forward bisimulation_backwards].
 
  eexists; auto.
  eapply Build_Simulation; intros.
  edestruct (right_total s1), (right_total s2).
  eapply bisimulation_backwards in H; eauto.
  repeat destruct H; destruct H3, H4.
  eapply simulation_preserving in H0; eauto.
  
  eapply simulation_correct in H; eauto.
  repeat destruct H; destruct H6, H7.
  eapply bisimulation_forward in H; eauto.
  repeat destruct H; destruct H9, H10.
  eapply simulation_preserving in H7; eauto.
  do 2 eexists; split; eauto.
  split; eauto.
  repeat (eapply result_same_transitive; eauto).
  split; eauto.
  intros; rewrite H5, H8; eauto.
Qed.


Theorem transfer_high_to_low :
  forall low high SL SH R,
    Simulation high high SH ->
    Bisimulation low high R ->
    left_total R ->
    simulation_preserving SL SH R ->
    Simulation low low SL.
Proof.
  unfold left_total, simulation_preserving; intros.
  destruct H, H0.
  rename simulation_correct0 into simulation_correct.
  rename H2 into simulation_preserving.
  rename H1 into left_total.
  destruct bisimulation_correct0
    as [bisimulation_forward bisimulation_backwards].
 
  eexists; auto.
  eapply Build_Simulation; intros.
  edestruct (left_total s1), (left_total s2).
  eapply bisimulation_forward in H; eauto.
  repeat destruct H; destruct H3, H4.
  eapply simulation_preserving in H0; eauto.
  
  eapply simulation_correct in H; eauto.
  repeat destruct H; destruct H6, H7.
  eapply bisimulation_backwards in H; eauto.
  repeat destruct H; destruct H9, H10.
  eapply simulation_preserving in H7; eauto.
  do 2 eexists; split; eauto.
  split; eauto.
  repeat (eapply result_same_transitive; eauto).
  split; eauto.
  intros; rewrite H5, H8; eauto.
Qed.


Definition refines_to_related {T1 T2} refines_to eqv_h (st1 st2: T1) := exists (sr1 sr2: T2), refines_to st1 sr1 /\ refines_to st2 sr2 /\ eqv_h sr1 sr2.

Definition deterministic_refinement {T1 T2} refines_to eqv_h :=
  forall (s:T1) (sr1 sr2: T2),
    refines_to s sr1 ->
    refines_to s sr2 ->
    eqv_h sr1 sr2.

Definition transitive {T} (R: T -> T -> Prop) :=
  forall t t' t'', R t t' -> R t' t'' -> R t t''.

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

  Record StrongBisimulation  (lts1 lts2 : LTS) (compile: forall T, Op lts2 T -> Op lts1 T)(refines_to: State lts1 -> State lts2 -> Prop):=
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

Theorem transfer_low_to_high_self :
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


Definition invariant (lts: LTS) (inv: State lts -> Prop):=
 forall T p st ret,
   inv st ->
   transition lts T st p ret ->
   inv (extract_state ret).


Theorem self_simulation_transfer :
  forall lts (S1 S2: State lts -> State lts -> Prop),
    SelfSimulation lts S1 ->
    (forall s1 s2,
       (exists T o s1', transition lts T s1 o s1') ->
         S2 s1 s2 ->
         S1 s1 s2) ->
    (forall T s1 s1' s2 s2',
        (exists o, transition lts T s1 o s1') ->
        S2 s1 s2 ->
        (exists o, transition lts T s2 o s2') ->
        result_same s1' s2' ->
        S1 (extract_state s1') (extract_state s2') ->
        (forall def, extract_ret def s1' = extract_ret def s2') ->
        S2 (extract_state s1') (extract_state s2')) ->
    SelfSimulation lts S2.
Proof.
  intros; eapply Build_SelfSimulation; intros.
  destruct H.
  eapply self_simulation_correct0 in H2 as Hx; eauto.
  destruct Hx; intuition.
  eexists; intuition eauto.
Qed.




(*
Section Functional.
  Record FunctionalBisimulation (lts1 lts2 : LTS) (RP: forall T, Op lts2 T -> Op lts1 T) (RS: State lts2 -> State lts1):=
  {
    functional_bisimulation_correct:
      forall T o2 s2 s2',
        (transition lts2) T s2 o2 s2' <->
        (transition lts1) T (RS s2) (RP T o2) (map_state RS s2');
      rs_preserving:
        forall T o2 s2 s1',
          (transition lts1) T (RS s2) (RP T o2) s1' ->
          exists s2', s1' = (map_state RS s2')
  }.

  Definition functional_simulation_preserving {T1 T2: Type} (S1: T1 -> T1 -> Prop) (S2: T2 -> T2 -> Prop)(R: T2 -> T1) :=
    forall t2 t2', S1 (R t2) (R t2') <-> S2 t2 t2'.

  Theorem transfer_low_to_high_functional :
  forall low high SL SH RS RP,
  SelfSimulation low SL ->
  FunctionalBisimulation low high RP RS ->
  functional_simulation_preserving SL SH RS ->
  SelfSimulation high SH.
  Proof.
    unfold functional_simulation_preserving; intros; cleanup.
    destruct H, H0.
    rename H1 into functional_simulation_preserving. 
    rename self_simulation_correct0 into self_simulation_correct.
    rename functional_bisimulation_correct0 into functional_bisimulation_correct.
    rename rs_preserving0 into rs_preserving.
  
    eapply Build_SelfSimulation; intros.
    apply functional_bisimulation_correct in H; cleanup.
    apply functional_simulation_preserving in H0.
    eapply self_simulation_correct in H; eauto; cleanup.
    eapply_fresh rs_preserving in H; cleanup.
    apply functional_bisimulation_correct in H.
    repeat rewrite extract_state_map_state_elim in H1.
    repeat setoid_rewrite extract_ret_map_state_elim in H2.
    apply functional_simulation_preserving in H1; eauto.
  Qed.  
End Functional.
 
Definition image_finite (lts : LTS) :=
  forall s,
  exists sl,
  forall o s',
    (transition lts) s o s' ->
    In s' sl.

Fixpoint bisimilar_up_to_level n (lts1 lts2: LTS) s1 s2:=
  match n with
  | 0 =>
    True
  | S n' =>
    (forall s1' o1,
      (transition lts1) s1 o1 s1' ->
      exists s2' o2,
        (transition lts2) s2 o2 s2' /\
        bisimilar_up_to_level n' lts1 lts2 s1' s2') /\
    (forall s2' o2,
      (transition lts2) s2 o2 s2' ->
      exists s1' o1,
        (transition lts1) s1 o1 s1' /\
        bisimilar_up_to_level n' lts1 lts2 s1' s2')
  end.

Definition bisimilar_up_to_omega (lts1 lts2: LTS) s t :=
  forall n, bisimilar_up_to_level n lts1 lts2 s t.

Lemma weak_image_finite_bisimilar_impl:
  forall lts1 lts2 s1 s2,
    image_finite lts1 ->
    image_finite lts2 ->
    bisimilar lts1 lts2 s1 s2 ->
    bisimilar_up_to_omega lts1 lts2 s1 s2.
Proof.
  unfold image_finite, bisimilar_up_to_omega,
  bisimilar; intros.
  specialize (H s1); destruct H.
  specialize (H0 s2); destruct H0.
  generalize dependent x.
  induction x; intros.
  { (* Base Case *)
    destruct n; simpl; auto.
    split; intros.
    edestruct H; eauto.
    repeat destruct H1.  
    destruct bisimulation_correct0
      as [bisimulation_forward bisimulation_backwards].
    edestruct bisimulation_backwards; eauto.
    repeat destruct H1.
    edestruct H; eauto.
  }

  { (* Inductive Case *)
    generalize dependent n.
    induction n; simpl; auto.
    split; intros.
    destruct IHx.
  specialize (bisimulation_forward o1 s1 s1' s2 H1 H2).
  repeat destruct bisimulation_forward.
  repeat destruct H3.
  do 2 eexists; split; eauto.
  
  
  
  destruct H1.
  eexists; econstructor.
  split; intros.
  specialize (H s1 o1); destruct H.
  specialize (H s1' H2).
  induction x0; simpl in *.
  inversion H.
  destruct H; subst.
  
  eauto.
  
  
  unfold 
  *)