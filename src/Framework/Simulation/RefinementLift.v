Require Import Primitives Layer Simulation.Definitions.

Section RefinementLift.
  Variable O_imp O_abs: Operation.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable OpRefinement : OperationRefinement L_imp O_abs.

  Fixpoint compile T (p2: prog L_abs T) : prog L_imp T.
    destruct p2.
    exact (OpRefinement.(compile_op) p).
    exact (Ret t).
    exact (Bind (compile T p2) (fun x => compile T' (p x))).
  Defined.

  Fixpoint oracle_refines_to T (d1: state L_imp) (p: prog L_abs T) o1 o2 : Prop :=
    match p with    
    |Op _ op =>
     exists o2',
     o2 =  [OpOracle O_abs o2' ] /\
     OpRefinement.(oracle_refines_to_op) d1 op o1 o2'

    | Ret v =>
      (exists d1',
         exec L_imp o1 d1 (Ret v) (Crashed d1') /\
         o2 = [Crash _]) \/
      (exists d1' r,
         exec L_imp o1 d1 (Ret v) (Finished d1' r) /\
         o2 = [Cont _])

    | @Bind _ T1 T2 p1 p2 =>
      exists o1' o1'' o2' o2'',
      o1 = o1'++o1'' /\
      o2 = o2' ++ o2'' /\
     ((exists d1', exec L_imp o1' d1 (compile T1 p1) (Crashed d1') /\
         oracle_refines_to T1 d1 p1 o1' o2') \/
      (exists d1' r ret,
         exec L_imp o1' d1 (compile T1 p1) (Finished d1' r) /\
         exec L_imp o1'' d1' (compile T2 (p2 r)) ret /\
         oracle_refines_to T1 d1 p1 o1' o2' /\
         oracle_refines_to T2 d1' (p2 r) o1'' o2''
         ))
    end.
  (*
  Theorem exec_preserves_refinement:
    forall T (p: L_abs.(prog) T) o s_abs ret,
      (exists s_imp, OpRefinement.(refines_to_op) s_imp s_abs) ->
      L_abs.(exec) o s_abs p ret ->
      (exists s_imp', OpRefinement.(refines_to_op) s_imp' (extract_state ret)).
  Proof.
    induction p; simpl; intros;
    invert_exec; eauto;
    try solve [eapply OpRefinement.(exec_preserves_refinement_op); eauto].

    split_ors; cleanup; eauto.
    edestruct IHp; eauto.
  Qed.
   *)
  
  Theorem exec_compiled_preserves_refinement:
    forall T (p: L_abs.(prog) T) o s_imp ret,
      (exists s_abs, OpRefinement.(refines_to_op) s_imp s_abs) ->
      L_imp.(exec) o s_imp (compile T p) ret ->
      (exists s_abs', OpRefinement.(refines_to_op) (extract_state ret) s_abs').
  Proof.
    induction p; simpl; intros;
    try invert_exec; eauto;
    try solve [eapply OpRefinement.(exec_compiled_preserves_refinement_op); eauto].

    split_ors; cleanup; eauto.
    edestruct IHp; eauto.
  Qed.
  
  Definition LiftRefinement : Refinement L_imp L_abs := Build_Refinement compile OpRefinement.(refines_to_op) oracle_refines_to (* exec_preserves_refinement *)
exec_compiled_preserves_refinement.

End RefinementLift.

Arguments LiftRefinement {_ _ _}.

