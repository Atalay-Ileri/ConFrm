Require Import Primitives Layer Simulation.Definitions.

Section RefinementLift.
  Variable C_imp C_abs: Core.
  Variable L_imp: Language C_imp.
  Variable L_abs: Language C_abs.
  Variable CoreRefinement : CoreRefinement L_imp C_abs.

  Fixpoint compile T (p2: prog L_abs T) : prog L_imp T.
    destruct p2.
    exact (CoreRefinement.(compile_core) o).
    exact (Ret t).
    exact (Bind (compile T p2) (fun x => compile T' (p x))).
  Defined.

  Fixpoint oracle_refines_to T u (d1: state L_imp) (p: prog L_abs T) get_reboot_state_imp o1 o2 : Prop :=
    match p with    
    |Op _ op =>
     exists o2',
     o2 =  [OpToken C_abs o2'] /\
       CoreRefinement.(token_refines_to) u d1 op get_reboot_state_imp o1 o2'
    | Ret v =>
      (exists d1',
         exec L_imp u o1 d1 (Ret v) (Crashed d1') /\
         o2 = [Crash _]) \/
      (exists d1' r,
         exec L_imp u o1 d1 (Ret v) (Finished d1' r) /\
         o2 = [Cont _])

    | @Bind _ T1 T2 p1 p2 =>
      exists o1' o1'' o2' o2'',
      o1 = o1'++o1'' /\
      o2 = o2' ++ o2'' /\
     ((exists d1', exec L_imp u o1' d1 (compile T1 p1) (Crashed d1') /\
         oracle_refines_to T1 u d1 p1 get_reboot_state_imp o1' o2') \/
      (exists d1' r ret,
         exec L_imp u o1' d1 (compile T1 p1) (Finished d1' r) /\
         exec L_imp u o1'' d1' (compile T2 (p2 r)) ret /\
         oracle_refines_to T1 u d1 p1 (fun s => s) o1' o2' /\
         oracle_refines_to T2 u d1' (p2 r) get_reboot_state_imp o1'' o2''
         ))
    end.

  Theorem exec_compiled_preserves_refinement_finished:
    forall T (p: L_abs.(prog) T) o s_imp s_imp' r u,
      (exists s_abs, CoreRefinement.(refines_to_core) s_imp s_abs) ->
      L_imp.(exec) u o s_imp (compile T p) (Finished s_imp' r) ->
      (exists s_abs', CoreRefinement.(refines_to_core) s_imp' s_abs').
  Proof.
    induction p; simpl; intros;
    try invert_exec; eauto;
    try solve [eapply CoreRefinement.(exec_compiled_preserves_refinement_finished_core); eauto].
  Qed.

  (*
  Theorem exec_compiled_preserves_refinement_crashed:
    forall T (p: L_abs.(prog) T) o s_imp s_imp',
      (exists s_abs, CoreRefinement.(refines_to_core) s_imp s_abs) ->
      L_imp.(exec) o s_imp (compile T p) (Crashed s_imp') ->
      (exists s_abs', CoreRefinement.(refines_to_crash_core) s_imp' s_abs').
  Proof.
    induction p; simpl; intros;
    try invert_exec; eauto;
    try solve [eapply CoreRefinement.(exec_compiled_preserves_refinement_crashed_core); eauto].
    apply refines_to_then_refines_to_crash_core; eauto.
    split_ors; cleanup; eauto.
    eapply exec_compiled_preserves_refinement_finished in H1; eauto.
  Qed.
  *)
  Definition LiftRefinement : Refinement L_imp L_abs :=
    Build_Refinement
      compile
      CoreRefinement.(refines_to_core)
      oracle_refines_to
      exec_compiled_preserves_refinement_finished.

End RefinementLift.

Arguments LiftRefinement {_ _ _}.

