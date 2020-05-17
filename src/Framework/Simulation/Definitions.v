Require Import Primitives Layer.

Record Refinement {O1 O2} (L1: Language O1) (L2: Language O2) :=
  {
    compilation_of : forall T, L1.(prog) T -> L2.(prog) T -> Prop;
    refines_to: L1.(state) -> L2.(state) -> Prop;
    oracle_refines_to: forall T, L1.(state) -> L2.(prog) T -> L1.(oracle) -> L2.(oracle) -> Prop;
  }.

Arguments Build_Refinement {_ _ _ _}.
Arguments compilation_of {_ _ _ _} _ {_}.
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
    R.(compilation_of) pl ph /\
    valid_prog_h T ph.


Definition exec_preserves_validity valid_state :=
    forall T (p: LH.(prog) T) o s ret,
      valid_state s ->
      exec LH o s p ret ->
      valid_state (extract_state ret).


Definition exec_compiled_preserves_validity valid_state:= 
    forall T (p1: LL.(prog) T) (p2: LH.(prog) T) o s ret,
      R.(compilation_of) p1 p2 ->
      valid_state s ->
      LL.(exec) o s p1 ret ->
      valid_state (extract_state ret).

Definition high_oracle_exists :=
  forall T o1 s1 s1' (p1: LL.(prog) T) p2,
    (exists sh, R.(refines_to) s1 sh) -> 
    LL.(exec) o1 s1 p1 s1' ->
    R.(compilation_of) p1 p2 ->
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
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2') /\
          valid_state (extract_state s1') /\
          valid_state (extract_state s2') ;
  }.

Record StrongBisimulation
  :=
  {
    strong_bisimulation_correct:
      (forall T p1 (p2: LH.(prog) T) s1 s2 o1 o2,
          
          R.(refines_to) s1 s2 ->
          R.(compilation_of) p1 p2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 p1 s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 p1 s1' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.

Record StrongBisimulationForValidStates
       (valid_state1 : LL.(state) -> Prop)
       (valid_state2 : LH.(state) -> Prop)
       (valid_prog1: forall T, LL.(prog) T -> Prop)
       (valid_prog2: forall T, LH.(prog) T -> Prop)
  :=
  {
    strong_bisimulation_for_valid_states_correct:
      (forall T p1 p2 s1 s2 o1 o2,
          valid_state1 s1 ->
          valid_prog1 T p1 ->
          
          valid_state2 s2 ->
          valid_prog2 T p2 ->
          
          R.(refines_to) s1 s2 ->
          R.(compilation_of) p1 p2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 p1 s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2') /\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')) /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 p1 s1' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')/\
                valid_state1 (extract_state s1') /\ valid_state2 (extract_state s2')))
  }.

Record StrongBisimulationForProgram
       {T} (p2: LH.(prog) T)
  :=
  {
    strong_bisimulation_for_program_correct:
      (forall p1 s1 s2 o1 o2,
          
          R.(refines_to) s1 s2 ->
          R.(compilation_of) p1 p2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              LL.(exec) o1 s1 p1 s1' ->
              exists s2',
                LH.(exec) o2 s2 p2 s2' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              LH.(exec) o2 s2 p2 s2' ->
              exists s1',
                LL.(exec) o1 s1 p1 s1' /\
                result_same s1' s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
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
Arguments StrongBisimulation {_ _ _ _}.
Arguments StrongBisimulationForValidStates {_ _ _ _}.
Arguments StrongBisimulationForProgram {_ _ _ _} _ {_}.

