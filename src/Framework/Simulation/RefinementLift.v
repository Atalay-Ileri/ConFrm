Require Import Primitives Layer Simulation.Definitions.

Section RefinementLift.
  Variable O1 O2: Operation.
  Variable L1: Language O1.
  Variable L2: Language O2.
  Variable OpRefinement : OperationRefinement L1 O2.

  Fixpoint compile T (p2: prog L2 T) : prog L1 T.
    destruct p2.
    exact (OpRefinement.(compile_op) p).
    exact (Ret t).
    exact (Bind (compile T p2) (fun x => compile T' (p x))).
  Defined.

  Fixpoint oracle_refines_to T (d1: state L1) (p: prog L2 T) o1 o2 : Prop :=
    match p with    
    |Op _ op =>
     exists o2',
     o2 =  [OpOracle O2 o2' ] /\
     OpRefinement.(oracle_refines_to_op) d1 op o1 o2'

    | Ret v =>
      (exists d1',
         exec L1 o1 d1 (Ret v) (Crashed d1') /\
         o2 = [Crash _]) \/
      (exists d1' r,
         exec L1 o1 d1 (Ret v) (Finished d1' r) /\
         o2 = [Cont _])

    | @Bind _ T1 T2 p1 p2 =>
      exists o1' o1'' o2' o2'',
      o1 = o1'++o1'' /\
      o2 = o2' ++ o2'' /\
     ((exists d1', exec L1 o1' d1 (compile T1 p1) (Crashed d1') /\
         oracle_refines_to T1 d1 p1 o1' o2') \/
      (exists d1' r ret,
         exec L1 o1' d1 (compile T1 p1) (Finished d1' r) /\
         exec L1 o1'' d1' (compile T2 (p2 r)) ret /\
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2''
         ))
    end.
  
  Definition LiftRefinement : Refinement L1 L2 := Build_Refinement compile OpRefinement.(refines_to_op) oracle_refines_to.

End RefinementLift.

Arguments LiftRefinement {_ _ _}.

