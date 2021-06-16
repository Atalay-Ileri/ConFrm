Require Import Primitives Layer Simulation.Definitions Lia.

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

  Fixpoint oracle_refines T u (d1: state L_imp) (p: prog L_abs T) get_reboot_state_imp o1 o2 : Prop :=
    match p with    
    |Op _ op =>
     exists o2',
     o2 =  [OpToken C_abs o2'] /\
       CoreRefinement.(token_refines) u d1 op get_reboot_state_imp o1 o2'
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
         oracle_refines T1 u d1 p1 get_reboot_state_imp o1' o2') \/
      (exists d1' r ret,
         exec L_imp u o1' d1 (compile T1 p1) (Finished d1' r) /\
         exec L_imp u o1'' d1' (compile T2 (p2 r)) ret /\
         oracle_refines T1 u d1 p1 (fun s => s) o1' o2' /\
         oracle_refines T2 u d1' (p2 r) get_reboot_state_imp o1'' o2''
         ))
    end.

  Theorem exec_compiled_preserves_refinement_finished:
    forall T (p: L_abs.(prog) T) o s_imp s_imp' r u,
      (exists s_abs, CoreRefinement.(refines_core) s_imp s_abs) ->
      L_imp.(exec) u o s_imp (compile T p) (Finished s_imp' r) ->
      (exists s_abs', CoreRefinement.(refines_core) s_imp' s_abs').
  Proof.
    induction p; simpl; intros;
    try invert_exec; eauto;
    try solve [eapply CoreRefinement.(exec_compiled_preserves_refinement_finished_core); eauto].
  Qed.

  Definition LiftRefinement : Refinement L_imp L_abs :=
    Build_Refinement
      compile
      CoreRefinement.(refines_core)
      oracle_refines
      exec_compiled_preserves_refinement_finished.

(*
Theorem SimulationForProgram_compositional_lifted:
      forall u l_grsi_1  l_grsa_1  T (p1_abs: L_abs.(prog) T) 
      T' (p2_abs: T -> L_abs.(prog) T') (rec_abs : L_abs.(prog) unit),
      SimulationForProgram LiftRefinement u p1_abs rec_abs [] [] ->
      SimulationForProgram LiftRefinement u p1_abs rec_abs l_grsi_1 l_grsa_1 ->
      (forall t, SimulationForProgram LiftRefinement u (p2_abs t) rec_abs l_grsi_1 l_grsa_1) ->
      SimulationForProgram LiftRefinement u (Bind p1_abs p2_abs) rec_abs l_grsi_1 l_grsa_1.
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; intros.
  simpl in *. repeat invert_exec; simpl in *.
  {
    cleanup; try intuition; try lia; simpl in *.
    {
      destruct l; simpl in *; try lia.
      cleanup; unify_execs; cleanup.
      invert_exec'' H13.
      split_ors; cleanup; repeat unify_execs; cleanup.
      eapply exec_deterministic_wrt_oracle_prefix in H4; eauto; cleanup.
      eapply exec_finished_deterministic_prefix in H4; eauto; cleanup.
      unify_execs; cleanup.

      edestruct H0; eauto.
      instantiate (1:= [x3]).
      instantiate (1:= [x1]).
      simpl; eauto.
      split; eauto.
      left; do 2 eexists; 
      split; eauto.
      econstructor; eauto.
      simpl in *; cleanup.
      destruct x7; simpl in *; cleanup.

      edestruct H1; eauto.
      instantiate (1:= [x4]).
      instantiate (1:= [x2]).
      simpl; eauto.
      split; eauto.
      left; do 2 eexists; 
      split; eauto.
      econstructor; eauto.
      simpl in *; cleanup.
      destruct x6; simpl in *; cleanup.

      exists (RFinished s0 t0).
      inversion H2; cleanup.
      inversion H5; cleanup.
      split; simpl; eauto.
      eapply ExecFinished; eauto.
      econstructor; eauto.
  }
  cleanup; intuition.
}
{
  cleanup; try intuition; simpl in *;
  cleanup; unify_execs; cleanup.
  invert_exec'' H12.
  {
    split_ors; cleanup; repeat unify_execs; cleanup.
    eapply exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup.
    eapply exec_finished_deterministic_prefix in H5; eauto; cleanup.
    unify_execs; cleanup.

    edestruct H; eauto.
    instantiate (1:= [x2]).
    instantiate (1:= [x0]).
    simpl; eauto.
    split; eauto.
    left; do 2 eexists; 
    split; eauto.
    econstructor; eauto.
    simpl in *; cleanup.
    destruct x6; simpl in *; cleanup.

    edestruct H1; eauto.
    instantiate (1:= x3 :: l).
    instantiate (1:= x1 :: lo).
    simpl; eauto.
    split; eauto.
    econstructor; eauto.
    simpl in *; cleanup.
    destruct x5; simpl in *; cleanup.

    exists (Recovered s0); split; eauto.
    inversion H4; cleanup.
    inversion H7; cleanup.
    econstructor; eauto.
    econstructor; eauto.
  }
  {
    split_ors; cleanup; repeat unify_execs; cleanup.
    eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup.

    edestruct H0; eauto.
    instantiate (1:= x2::l).
    instantiate (1:= x0::lo).
    simpl; eauto.
    split; eauto.
    econstructor; eauto.
    simpl in *; cleanup.
    destruct x; simpl in *; cleanup.

    exists (Recovered s); split; eauto.
    inversion H8; cleanup.
    econstructor; eauto.
    eapply ExecBindCrash; eauto.
  }
}
Qed.
*)
Lemma abstract_oracles_exist_wrt_compositional:
forall u l_grs T (p1: prog L_abs T) T' (p2: T -> prog L_abs T') rec, 
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(refines) u p1 rec [] ->
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(refines) u p1 rec l_grs ->
(forall t, abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(refines) u (p2 t) rec l_grs) ->
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(refines) u (Bind p1 p2) rec l_grs.
Proof.
    unfold abstract_oracles_exist_wrt; 
    simpl; intros;
    repeat invert_exec.
    {
        invert_exec'' H12.
        edestruct H; eauto.
        econstructor; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

        edestruct H1; eauto.
        econstructor; eauto.

        simpl in *; cleanup; try intuition; simpl in *; try congruence;
        cleanup; repeat unify_execs; cleanup.
        exists [o0++o].
        simpl; split; eauto.
        repeat left.
        do 2 eexists; econstructor; eauto.
        econstructor; eauto.
        intuition eauto.
        do 4 eexists; intuition eauto. 
        right; do 3 eexists; intuition eauto.
    }
    {
        invert_exec'' H11.
        {
            edestruct H; eauto.
            econstructor; eauto.

            eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

            edestruct H1; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists ((o0++o)::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            econstructor; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            right; do 3 eexists; intuition eauto.
        }
        {
            edestruct H0; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            eexists (_::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            eapply ExecBindCrash; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            rewrite app_nil_r; eauto.
        }
    }
    Unshelve.
    eauto.
Qed.

(*
Lemma oracle_refines_same_from_related_compositional:
forall u R l_grs T (p1 p2: prog L_abs T) T' (p3 p4: T -> prog L_abs T') rec, 
oracle_refines_same_from_related LiftRefinement u p1 p2 rec [] R ->
oracle_refines_same_from_related LiftRefinement u p1 p2 rec l_grs R ->
(forall t t', oracle_refines_same_from_related LiftRefinement u (p3 t) (p4 t') rec l_grs R) ->
oracle_refines_same_from_related LiftRefinement u (Bind p1 p3) (Bind p2 p4) rec l_grs R.
Proof.
    unfold oracle_refines_same_from_related; 
    simpl; intros.
    destruct l_o_imp; simpl in *; intuition.

    cleanup; try intuition simpl in *; try congruence; try lia.
    {  
      repeat split_ors; cleanup.
      invert_exec'' H0.
      invert_exec'' H5.
      repeat split_ors; cleanup; repeat unify_execs; cleanup;
      eapply_fresh exec_deterministic_wrt_oracle_prefix in H5; eauto; cleanup;
      eapply_fresh exec_deterministic_wrt_oracle_prefix in H7; eauto; cleanup.
      rewrite H4; eauto.  
      eapply_fresh exec_finished_deterministic_prefix in H5; eauto; cleanup;
      eapply_fresh exec_finished_deterministic_prefix in H7; eauto; cleanup.
      rewrite <- H4 in H6; clear H4; cleanup; repeat unify_execs; cleanup.


      }
      invert_exec'' H12.
        edestruct H; eauto.
        econstructor; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

        edestruct H1; eauto.
        econstructor; eauto.

        simpl in *; cleanup; try intuition; simpl in *; try congruence;
        cleanup; repeat unify_execs; cleanup.
        exists [o0++o].
        simpl; split; eauto.
        repeat left.
        do 2 eexists; econstructor; eauto.
        econstructor; eauto.
        intuition eauto.
        do 4 eexists; intuition eauto. 
        right; do 3 eexists; intuition eauto.
    }
    {
        invert_exec'' H11.
        {
            edestruct H; eauto.
            econstructor; eauto.

            eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

            edestruct H1; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists ((o0++o)::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            econstructor; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            right; do 3 eexists; intuition eauto.
        }
        {
            edestruct H0; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists (o::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            eapply ExecBindCrash; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            rewrite app_nil_r; eauto.
        }
    }
Qed.
*)

End RefinementLift.

Arguments LiftRefinement {_ _ _}.
(* Arguments SimulationForProgram_compositional_lifted {_ _ _ _}. *)
Arguments abstract_oracles_exist_wrt_compositional {_ _ _ _}.