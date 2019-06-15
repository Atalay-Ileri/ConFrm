Require Import List.

Record Equivalence (T: Type) :=
  {
    eq : T -> T -> Prop;
    
    eq_refl: forall t, eq t t;
    eq_sym: forall t t', eq t t' -> eq t' t;
    eq_trans: forall t t' t'', eq t t' -> eq t' t'' -> eq t t'';
  }.


Record LTS :=
  {
    State : Type;
    Op : Type;
    transition : State -> Op -> State -> Prop;
  }.

Record Simulation (lts1 lts2 : LTS) (R: State lts1 -> State lts2 -> Prop):=
  {
    simulation_correct:
      forall o1 s1 s1' s2,
        transition lts1 s1 o1 s1' ->
        R s1 s2 ->
        exists o2 s2',
          transition lts2 s2 o2 s2' /\
          R s1' s2';
  }.


Record Bisimulation  (lts1 lts2 : LTS) (R: State lts1 -> State lts2 -> Prop):=
  {
    bisimulation_correct:
      (forall o1 s1 s1' s2,
        transition lts1 s1 o1 s1' ->
        R s1 s2 ->
        exists o2 s2',
          transition lts2 s2 o2 s2' /\
          R s1' s2') /\
      (forall o2 s1 s2 s2',
        transition lts2 s2 o2 s2' ->
        R s1 s2 ->
        exists o1 s1',
          transition lts1 s1 o1 s1' /\
          R s1' s2')
  }.

Definition bisimilar (lts1 lts2 : LTS) s1 s2 :=
  exists R, Bisimulation lts1 lts2 R /\ R s1 s2.

Variable low high : LTS.

Definition habited (T : Type):=
  exists _ : T, True.

Definition right_total {T1 T2: Type} (R: T1 -> T2 -> Prop) :=
  forall t2, exists t1, R t1 t2.

Definition simulation_preserving {T1 T2: Type} (S1: T1 -> T1 -> Prop) (S2: T2 -> T2 -> Prop)(R: T1 -> T2 -> Prop) :=
  forall t1 t1' t2 t2',
    R t1 t2 ->
    R t1' t2' ->
    S1 t1 t1' <-> S2 t2 t2'.

Theorem transfer :
  forall SL SH R,
  Simulation low low SL ->
  Bisimulation low high R ->
  right_total R ->
  simulation_preserving SL SH R ->
  Simulation high high SH.
Proof.
  unfold right_total, simulation_preserving, habited; intros.
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
  repeat destruct H.
  eapply simulation_preserving in H0; eauto.
  
  eapply simulation_correct in H; eauto.
  repeat destruct H.
  eapply bisimulation_forward in H; eauto.
  repeat destruct H.
  eapply simulation_preserving in H4; eauto.
Qed.

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
  