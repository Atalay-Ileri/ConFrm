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
  | Crashed s  => Crashed (f s)
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