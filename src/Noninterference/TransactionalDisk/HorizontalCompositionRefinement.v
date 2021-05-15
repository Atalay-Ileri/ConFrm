Require Import Framework. 
Import ListNotations.

Set Implicit Arguments.

Section HC_Refinement.

Variable O O1 O2: Core.
Variable L1 : Language O1.
Variable L2 : Language O2.
Variable HCL1 : Language (HorizontalComposition O O1).
Variable HCL2 : Language (HorizontalComposition O O2).
Variable RC: CoreRefinement L1 O2.
Variable reboot_O: O.(Core.state) -> O.(Core.state).

Definition compile T (o: (HorizontalComposition O O2).(operation) T) : HCL1.(prog) T := 
    match o with
    | P1 p1 => Op (HorizontalComposition O O1) (P1 p1)
    | P2 p2 => lift_L2 _ (RC.(compile_core) p2)
    end.

Definition HC_refines := fun (si: HCL1.(state)) (sa: HCL2.(state)) => 
fst si = fst sa /\ RC.(refines_core) (snd si) (snd sa).

Lemma HC_exec_compiled_preserves_refinement_finished_core :
forall T (p2: (HorizontalComposition O O2).(operation) T) o1 s1 s1' r u,
  (exists s2, HC_refines s1 s2) ->
  HCL1.(exec) u o1 s1 (compile p2) (Finished s1' r) ->
  (exists s2', HC_refines s1' s2').
  Proof.
    destruct p2; simpl; intros.
    {
        unfold HC_refines in *; cleanup;
        repeat invert_exec.
        simpl; exists (s0, snd x); split; eauto.
    }
    {
        unfold HC_refines in *; cleanup; 
        repeat invert_exec; eauto.
        eapply RC.(exec_compiled_preserves_refinement_finished_core) in H3; eauto.
        cleanup.
        simpl; exists (fst s1, x1); split; eauto.
    }
Qed.

Fixpoint HC_oracle_transformation (o1: oracle HCL1) (o2: oracle L1) :=
match o1 with
| [] => o2 = []
| t1::o1' => 
    match t1 with
    | OpToken _ t =>
        exists t' o2', 
        t = Token2 _ _ t' /\
        o2 = (OpToken _ t') :: o2' /\
        HC_oracle_transformation o1' o2'
    | Cont _ =>
        exists o2', 
        o2 = (Cont _):: o2' /\
        HC_oracle_transformation o1' o2'
    | Crash _ =>
        exists o2', 
        o2 = (Crash _):: o2' /\
        HC_oracle_transformation o1' o2'
    end
end.


(* Problem Here is A single token in abstract turns into an oracle for implementation, it is like flattened *)
Definition HC_token_refines T u (d1: HCL1.(state)) 
(p: (HorizontalComposition O O2).(operation) T) 
(get_reboot_state: HCL1.(state) -> HCL1.(state)) (o1: oracle HCL1) t2 : Prop :=
match p with
| P1 p1 => exists t , t2 = Token1 _ _ t /\ o1 = [OpToken (HorizontalComposition O O1) (Token1 O O1 t)] 
| P2 p2 =>
    exists t o grs1, t2 = Token2 _ _ t /\ 
    HC_oracle_transformation o1 o /\
    (forall s, snd (get_reboot_state s) = grs1 (snd s)) /\
    RC.(token_refines) u (snd d1) p2 grs1 o t
end.
    

Definition HC_Core_Refinement : CoreRefinement HCL1 (HorizontalComposition O O2) :=
Build_CoreRefinement compile HC_refines
HC_token_refines
HC_exec_compiled_preserves_refinement_finished_core.

Definition HC_Refinement := LiftRefinement HCL2 HC_Core_Refinement.


Lemma ss_transfer_horizontal_composition:
  forall valid_state related_states cond 
  get_reboot_list transformer u 
  (n: nat) T (p1 p2: HCL2.(prog) T) rec,

  SelfSimulation u p1 p2 rec 
    valid_state
    related_states cond
    (get_reboot_list n) ->

    abstract_oracles_exist_wrt HC_Refinement HC_Refinement.(Simulation.Definitions.refines) u p1 rec (transformer get_reboot_list n) ->
    abstract_oracles_exist_wrt HC_Refinement HC_Refinement.(Simulation.Definitions.refines) u p2 rec (transformer get_reboot_list n) ->
    
    oracle_refines_same_from_related HC_Refinement u p1 p2 rec (transformer get_reboot_list n) related_states ->


    @SelfSimulation _ HCL1 u _ (HC_Refinement.(Simulation.Definitions.compile) p1) 
      (HC_Refinement.(Simulation.Definitions.compile) p2) 
      (HC_Refinement.(Simulation.Definitions.compile) rec) 
      (refines_valid HC_Refinement valid_state)
      (refines_related HC_Refinement related_states)
      cond (transformer get_reboot_list n).
    Proof.
        intros.
  (** Convert to weak self_simulation **)
  eapply Self_Simulation_Weak_to_Self_Simulation; eauto.
  unfold SelfSimulation_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: recovery_exec _ _ _ _ _ (compile _ ?p1) _ _,
     H0: recovery_exec _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine_to _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine_to _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: recovery_exec _ _ _ _ _ (compile _ ?p1) _ _,
     H0: recovery_exec _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: recovery_exec L_abs _ _ _ _ p1_abs _ _,
     H0: recovery_exec L_abs _ _ _ _ _ _ _,
     H1: SelfSimulation _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: recovery_exec L_abs _ _ _ _ p2_abs _ _,
     H0: recovery_exec L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply recovery_exec_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.


End HC_Refinement.




