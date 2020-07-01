Require Import Primitives Layer.

Record OperationRefinement {O1} (L1: Language O1) (O2: Operation) :=
  {
    compile_op : forall T, O2.(Operation.prog) T -> L1.(prog) T;
    refines_to_op: L1.(state) -> O2.(Operation.state) -> Prop;
    oracle_refines_to_op: forall T, L1.(state) -> O2.(Operation.prog) T -> L1.(oracle) -> O2.(Operation.oracle) -> Prop;
  }.

Record Refinement {O1 O2} (L1: Language O1) (L2: Language O2) :=
  {
    compile : forall T, L2.(prog) T -> L1.(prog) T;
    refines_to: L1.(state) -> L2.(state) -> Prop;
    oracle_refines_to: forall T, L1.(state) -> L2.(prog) T -> L1.(oracle) -> L2.(oracle) -> Prop;
  }.

Arguments Build_OperationRefinement {_ _ _}.
Arguments compile_op {_ _ _} _ {_}.
Arguments refines_to_op {_ _ _}.
Arguments oracle_refines_to_op {_ _ _} _ {_} .

Arguments Build_Refinement {_ _ _ _}.
Arguments compile {_ _ _ _} _ {_}.
Arguments refines_to {_ _ _ _}.
Arguments oracle_refines_to {_ _ _ _} _ {_} .

Section Relations.
  Variable OL OH: Operation.
  Variable LL: Language OL.
  Variable LH: Language OH.
  Variable R : Refinement LL LH.

  
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
Definition refines_to_related 
           (related_h:  LH.(state) -> LH.(state) -> Prop)
           (sl1 sl2: LL.(state))
  : Prop :=
  exists (sh1 sh2: LH.(state)),
    R.(refines_to) sl1 sh1 /\
    R.(refines_to) sl2 sh2 /\
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
Definition refines_to_valid 
           (valid_state_h: LH.(state) -> Prop)
           (sl: LL.(state))
  : Prop :=
  forall (sh: LH.(state)),
    R.(refines_to) sl sh ->
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
Definition compiles_to_valid
           (valid_prog_h: forall T, LH.(prog) T -> Prop)
           (T: Type)
           (pl: LL.(prog) T)
  : Prop :=
  exists (ph: LH.(prog) T),
    pl = R.(compile) ph /\
    valid_prog_h T ph.


Definition exec_preserves_validity valid_state :=
    forall T (p: LH.(prog) T) o s ret,
      valid_state s ->
      exec LH o s p ret ->
      valid_state (extract_state ret).


Definition exec_compiled_preserves_validity valid_state:= 
    forall T (p2: LH.(prog) T) o s ret,
      valid_state s ->
      LL.(exec) o s (R.(compile) p2) ret ->
      valid_state (extract_state ret).

Definition high_oracle_exists :=
  forall T (p2: LH.(prog) T) o1 s1 s1',
    (exists sh, R.(refines_to) s1 sh) -> 
    LL.(exec) o1 s1 (R.(compile) p2) s1' ->
    exists o2, R.(oracle_refines_to) s1 p2 o1 o2.

Definition oracle_refines_to_same_from_related 
           (related_states_h: LH.(state) -> LH.(state) -> Prop) :=
  forall T o oh s1 s2 (p2: LH.(prog) T),
    refines_to_related related_states_h s1 s2 ->
    R.(oracle_refines_to) s1 p2 o oh ->
    R.(oracle_refines_to) s2 p2 o oh.

(*
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
*)
Record SelfSimulation 
       (valid_state: LH.(state) -> Prop)
       (valid_prog: forall T, LH.(prog) T -> Prop)
       (R: LH.(state) -> LH.(state) -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_prog T p ->
        LH.(exec) o s1 p s1' ->
        R s1 s2 ->
        exists s2',
          LH.(exec) o s2 p s2' /\
          R (extract_state s1') (extract_state s2') /\
          extract_ret s1' = extract_ret s2' /\
          valid_state (extract_state s1') /\
          valid_state (extract_state s2') ;
  }.

Definition SelfSimulationForSecretInputs 
       (valid_state: LH.(state) -> Prop)
       (valid_prog: forall T, LH.(prog) T -> Prop)
       (R: LH.(state) -> LH.(state) -> Prop)
       {T T'} (p: T -> LH.(prog) T'):=
  
      forall o s s1 t1 t2,
        valid_state s ->
        valid_prog T' (p t1) ->
        valid_prog T' (p t2) ->
        LH.(exec) o s (p t1) s1 ->
        exists s1',
          LH.(exec) o s (p t2) s1' /\
          R (extract_state s1) (extract_state s1') /\
          extract_ret s1 = extract_ret s1' /\
          valid_state (extract_state s1) /\
          valid_state (extract_state s1').

Record StrongBisimulation
  :=
  {
    strong_bisimulation_correct:
      (forall T (p2: LH.(prog) T) s1 s2 o1 o2,
          
          R.(refines_to) s1 s2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 (R.(compile) p2) s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2') /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 (R.(compile) p2) s1' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2'))
  }.

Record StrongBisimulationForValidStates
       (valid_state1 : LL.(state) -> Prop)
       (valid_state2 : LH.(state) -> Prop)
       (valid_prog2: forall T, LH.(prog) T -> Prop)
  :=
  {
    strong_bisimulation_for_valid_states_correct:
      (forall T p2 s1 s2 o1 o2,
          valid_state1 s1 ->
          
          valid_state2 s2 ->
          valid_prog2 T p2 ->
          
          R.(refines_to) s1 s2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 (R.(compile) p2) s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2' /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')) /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 (R.(compile) p2) s1' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2' /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')))
  }.

Record StrongBisimulationForProgram
       {T} (p2: LH.(prog) T)
  :=
  {
    strong_bisimulation_for_program_correct:
      (forall s1 s2 o1 o2,
          
          R.(refines_to) s1 s2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 (R.(compile) p2) s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2') /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 (R.(compile) p2) s1' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2'))
  }.
End Relations.

Arguments refines_to_related {_ _ _ _}.
Arguments refines_to_valid {_ _ _ _}.
Arguments compiles_to_valid {_ _ _ _}.
Arguments exec_preserves_validity {_}.
Arguments exec_compiled_preserves_validity {_ _ _ _}.
Arguments high_oracle_exists {_ _ _ _}.
Arguments oracle_refines_to_same_from_related {_ _ _ _}.
Arguments SelfSimulation {_}.
Arguments SelfSimulationForSecretInputs {_} _ _ _ _ {_ _}.
Arguments StrongBisimulation {_ _ _ _}.
Arguments StrongBisimulationForValidStates {_ _ _ _}.
Arguments StrongBisimulationForProgram {_ _ _ _} _ {_}.

(*
Theorem transfer_high_to_low':
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH)
    related_states_h,
    
    StrongBisimulation R ->

    (forall sl sh1 sh2,
       R.(refines_to) sl sh1 ->
       R.(refines_to) sl sh2 ->
       related_states_h sh1 sh2).
Proof.
  intros.
  destruct H.
  eapply strong_bisimulation_correct0 in H0.
  eapply strong_bisimulation_correct0 in H1.

  
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
*)
