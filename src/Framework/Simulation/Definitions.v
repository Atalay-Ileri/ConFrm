Require Import Primitives Layer.

(*
Record LTS :=
  {
    Oracle : Type;
    State : Type;
    Prog : Type -> Type;
    exec : forall T, Oracle -> State -> Prog T -> @Result State T -> Prop;
  }.
*)

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


Definition exec_preserves_validity {O} {L: Language O} valid_state :=
    forall T (p: L.(prog) T) o s ret,
      valid_state s ->
      exec L o s p ret ->
      valid_state (extract_state ret).


Definition exec_compiled_preserves_validity {O1 O2} {low: Language O1} {high: Language O2}
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop) valid_state :=
    forall T (p1: low.(prog) T) (p2: high.(prog) T) o s ret,
      compilation_of T p1 p2 ->
      valid_state s ->
      low.(exec) o s p1 ret ->
      valid_state (extract_state ret).

Definition exec_preserves_refinement {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop) :=
    forall T (p: high.(prog) T) o2 s2 ret,
      (exists s1, refines_to s1 s2) ->
      high.(exec) o2 s2 p ret ->
      (exists s1', refines_to s1' (extract_state ret)).

Definition exec_compiled_preserves_refinement {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop) :=
    forall T (p1: low.(prog) T) (p2: high.(prog) T) o1 s1 ret,
      compilation_of T p1 p2 ->
      (exists s2, refines_to s1 s2) ->
      low.(exec) o1 s1 p1 ret ->
      (exists s2', refines_to (extract_state ret) s2').

Definition high_oracle_exists {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o1 s1 s1' p1 p2,
    (exists sh, refines_to s1 sh) -> 
    low.(exec) o1 s1 p1 s1' ->
    compilation_of T p1 p2 ->
    exists o2, oracle_refines_to T s1 p2 o1 o2.

Definition oracle_refines_to_same_from_related {O1 O2} {low: Language O1} {high: Language O2}
           (refines_to: low.(state) -> high.(state) -> Prop)
           (related_states_h: high.(state) -> high.(state) -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop) :=
  forall T o oh s1 s2 p2,
    refines_to_related refines_to related_states_h s1 s2 ->
    oracle_refines_to T s1 p2 o oh ->
    oracle_refines_to T s2 p2 o oh.
  
(*
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
*)
Record SelfSimulation {O}(L: Language O)
       (valid_state: L.(state) -> Prop)
       (valid_prog: forall T, L.(prog) T -> Prop)
       (R: L.(state) -> L.(state) -> Prop) :=
  {
    self_simulation_correct:
      forall T o p s1 s1' s2,
        valid_state s1 ->
        valid_state s2 ->
        valid_prog T p ->
        L.(exec) o s1 p s1' ->
        R s1 s2 ->
        exists s2',
          L.(exec) o s2 p s2' /\
          result_same s1' s2' /\
          R (extract_state s1') (extract_state s2') /\
          (forall def, extract_ret def s1' = extract_ret def s2') /\
          valid_state (extract_state s1') /\
          valid_state (extract_state s2') ;
  }.

Record StrongBisimulation
        {O1 O2} (low: Language O1) (high: Language O2)
           (refines_to: low.(state) -> high.(state) -> Prop)
           (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
           (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop)
  :=
  {
    strong_bisimulation_correct:
      (forall T p1 (p2: high.(prog) T) s1 s2 o1 o2,
          
          refines_to s1 s2 ->
          compilation_of T p1 p2 ->
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              low.(exec) o1 s1 p1 s1' ->
              exists s2',
                high.(exec) o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              high.(exec) o2 s2 p2 s2' ->
              exists s1',
                low.(exec) o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.

(*
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
*)

Record StrongBisimulationForProgram
       {O1 O2} (low: Language O1) (high: Language O2)
       (refines_to: low.(state) -> high.(state) -> Prop)
       (compilation_of: forall T, low.(prog) T -> high.(prog) T -> Prop)
       (oracle_refines_to : forall T, low.(state) -> high.(prog) T -> low.(oracle) -> high.(oracle) -> Prop)
       {T} (p2: high.(prog) T)
  :=
  {
    strong_bisimulation_for_program_correct:
      (forall p1 s1 s2 o1 o2,
          
          refines_to s1 s2 ->
          compilation_of T p1 p2 ->
          oracle_refines_to T s1 p2 o1 o2 ->
          
          (forall s1',
              low.(exec) o1 s1 p1 s1' ->
              exists s2',
                high.(exec) o2 s2 p2 s2' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')) /\
          (forall s2',
              high.(exec) o2 s2 p2 s2' ->
              exists s1',
                low.(exec) o1 s1 p1 s1' /\
                result_same s1' s2' /\
                refines_to (extract_state s1') (extract_state s2') /\
                (forall def, extract_ret def s1' = extract_ret def s2')))
  }.
