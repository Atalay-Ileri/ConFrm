Require Import List Primitives Layer.
Require Import Simulation.Definitions RefinementLift. 
Import ListNotations.

Set Implicit Arguments.

(* This module automates the construction of a refinement
L1 refines L3 if L1 refines L2 and L2 refines L3*)
Section VC_Refinement.

Variable O1 O2 O3: Core.
Variable L1 : Layer O1.
Variable L2 : Layer O2.
Variable L3 : Layer O3.
Variable R1: Refinement L1 L2.
Variable R2: Refinement L2 L3.

Definition compile T (p: L3.(prog) T) : L1.(prog) T := 
  R1.(Definitions.compile) (R2.(Definitions.compile) p).


Definition VC_refines := fun (s1: L1.(state)) (s3: L3.(state)) => 
exists s2, R1.(refines) s1 s2 /\ R2.(refines) s2 s3.

Lemma VC_exec_compiled_preserves_refinement_finished:
forall T (p3: L3.(prog) T) o1 s1 s1' r u,
  (exists s3, VC_refines s1 s3) ->
  L1.(exec) u o1 s1 (compile p3) (Finished s1' r) ->
  (exists rec, SimulationForProgram R1 u (R2.(Definitions.compile) p3) rec nil nil) ->
  (forall x1,
  exec L1 u o1 s1 (Definitions.compile R1 (Definitions.compile R2 p3))
  (Finished s1' r) ->
  refines R1 s1 x1 ->
  exists o2,  
  forall grs, Definitions.oracle_refines R1 u s1 (Definitions.compile R2 p3) grs o1 o2) ->
  (exists s3', VC_refines s1' s3').
  Proof.
    unfold SimulationForProgram, 
    SimulationForProgramGeneral, 
    compile, VC_refines; intros; cleanup.
    edestruct H2; eauto.
    
    edestruct H1; eauto.
    2: econstructor; eauto.
    simpl; eauto.
    instantiate (1:= [_]); simpl.
    intuition eauto.
    left; do 2 eexists; intuition eauto.
    
    simpl in *; cleanup.
    invert_exec; simpl in *; cleanup.
    eapply_fresh R2.(Definitions.exec_compiled_preserves_refinement_finished) in H14; eauto.
    cleanup.
    do 2 eexists; eauto.
  Qed.

(* Problem Here is A single token in abstract turns into an oracle for implementation, it is like flattened *)
Definition oracle_refines T u (d1: L1.(state)) 
(p: L3.(prog) T) 
(get_reboot_state1: L1.(state) -> L1.(state)) 
(get_reboot_state2: L2.(state) -> L2.(state)) 
(o1: oracle L1) o3 : Prop :=
forall d2, 
R1.(refines) d1 d2 ->
exists o2, 
R1.(Definitions.oracle_refines) u d1 (R2.(Definitions.compile) p) get_reboot_state1 o1 o2 /\
R2.(Definitions.oracle_refines) u d2 p get_reboot_state2 o2 o3.

End VC_Refinement.



