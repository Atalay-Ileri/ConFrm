Require Import Lia Primitives Layer.

Record CoreRefinement {O_imp} (L_imp: Language O_imp) (O_abs: Core) :=
  {
    compile_core : forall T, O_abs.(Core.operation) T -> L_imp.(prog) T;
    refines_to_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    token_refines_to: forall T, L_imp.(state) -> O_abs.(Core.operation) T -> (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> O_abs.(Core.token) -> Prop;
  }.

Record Refinement {O_imp O_abs} (L_imp: Language O_imp) (L_abs: Language O_abs) :=
  {
    compile : forall T, L_abs.(prog) T -> L_imp.(prog) T;
    refines_to: L_imp.(state) -> L_abs.(state) -> Prop;
    oracle_refines_to: forall T, L_imp.(state) -> L_abs.(prog) T -> (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> L_abs.(oracle) -> Prop;
  }.

Arguments Build_CoreRefinement {_ _ _}.
Arguments compile_core {_ _ _} _ {_}.
Arguments refines_to_core {_ _ _}.
Arguments token_refines_to {_ _ _} _ {_}.

Arguments Build_Refinement {_ _ _ _}.
Arguments compile {_ _ _ _} _ {_}.
Arguments refines_to {_ _ _ _}.
Arguments oracle_refines_to {_ _ _ _} _ {_}.

Section Relations.
  Variable O_imp O_abs: Core.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable R : Refinement L_imp L_abs.
  
  Fixpoint recovery_oracles_refine_to {T}
           (s: L_imp.(state)) (p_abs: L_abs.(prog) T) (rec_abs: L_abs.(prog) unit)
           (l_get_reboot_state_imp: list (L_imp.(state) -> L_imp.(state)))
           (lo_imp: list L_imp.(oracle)) (lo_abs: list L_abs.(oracle)) {struct lo_imp} :=
    match lo_imp, lo_abs with
    | o_imp :: loi, o_abs :: loa =>
      length lo_imp = length lo_abs /\
      (forall s' t,
         L_imp.(exec) o_imp s (R.(compile) p_abs) (Finished s' t) ->
         R.(oracle_refines_to) s p_abs (fun s => s) o_imp o_abs) /\
      (forall s',
         L_imp.(exec) o_imp s (R.(compile) p_abs) (Crashed s') ->
         match l_get_reboot_state_imp with
         | get_reboot_state_imp :: lgrsi =>
           R.(oracle_refines_to) s p_abs get_reboot_state_imp o_imp o_abs /\
           recovery_oracles_refine_to (get_reboot_state_imp s') rec_abs rec_abs lgrsi loi loa
         | _ => False
         end)
    | _, _ => False
    end.

Definition abstract_oracles_exist_wrt Rel {T} (p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state :=
  forall l_oi si si',
    (exists sa: L_abs.(state), Rel si sa) -> 
    L_imp.(recovery_exec) l_oi si l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) si' ->
    exists l_oa, recovery_oracles_refine_to si p_abs rec_abs l_get_reboot_state l_oi l_oa.

(** 
A relation that takes 
   - two input states (si1 and si2), 
   - a refinement realiton (refines_to), and
   - a relation (related_abs)
and asserts that 
    - there are two other abstract states (sa1 and sa2) such that,
    - si1 (si2) refines to sa1 (sa2) via refines_to relation, and
    - sa1 and sa2 are related via related_abs
**)
  Definition refines_to_related 
             (related_abs:  L_abs.(state) -> L_abs.(state) -> Prop)
             (si1 si2: L_imp.(state))
    : Prop :=
    exists (sa1 sa2: L_abs.(state)),
      R.(refines_to) si1 sa1 /\
      R.(refines_to) si2 sa2 /\
      related_abs sa1 sa2.


Definition refines_to_valid 
           (valid_state_abs: L_abs.(state) -> Prop)
           (si: L_imp.(state))
  : Prop :=
  forall (sa: L_abs.(state)),
    R.(refines_to) si sa ->
    valid_state_abs sa.


Definition exec_compiled_preserves_validity  {T} (p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state (valid_state: L_imp.(state) -> Prop) := 
    forall l_oi s ret,
      valid_state s ->
      L_imp.(recovery_exec) l_oi s l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) ret ->
      valid_state (extract_state_r ret).


Definition oracle_refines_to_same_from_related
            {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_to_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine_to s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine_to s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.

(** Self Simulation **)
(**
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
**)

Definition SelfSimulation {T} (p1 p2: L_abs.(prog) T)
       (rec: L_abs.(prog) unit)
       (valid_state: L_abs.(state) -> Prop)
       (R: L_abs.(state) -> L_abs.(state) -> Prop)
       l_get_reboot_state :=
  forall lo s1 s1',
    L_abs.(recovery_exec) lo s1 l_get_reboot_state p1 rec s1' ->
    valid_state s1 ->
    forall s2,
    valid_state s2 ->
    R s1 s2 ->
    exists s2',
      L_abs.(recovery_exec) lo s2 l_get_reboot_state p2 rec s2' /\
      R (extract_state_r s1') (extract_state_r s2') /\
      extract_ret_r s1' = extract_ret_r s2' /\
      valid_state (extract_state_r s1') /\
      valid_state (extract_state_r s2').

Definition SelfSimulation_Exists  {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           l_get_reboot_state :=
  forall s1 s1' s2 lo,
    valid_state s1 ->
    valid_state s2 -> 
    L_abs.(recovery_exec) lo s1 l_get_reboot_state p1 rec s1' ->
    R s1 s2 ->
    exists s2', 
      L_abs.(recovery_exec) lo s2 l_get_reboot_state p2 rec s2'.

Definition SelfSimulation_Weak {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           l_get_reboot_state :=
  forall lo s1 s1' s2 s2',
    L_abs.(recovery_exec) lo s1 l_get_reboot_state p1 rec s1' ->
    L_abs.(recovery_exec) lo s2 l_get_reboot_state p2 rec s2' ->
    valid_state s1 ->
    valid_state s2 ->
    R s1 s2 ->
    R (extract_state_r s1') (extract_state_r s2') /\
    extract_ret_r s1' = extract_ret_r s2' /\
    valid_state (extract_state_r s1') /\
    valid_state (extract_state_r s2').

Lemma Self_Simulation_Weak_to_Self_Simulation:
  forall T (p1 p2: L_abs.(prog) T) R
    valid_state rec l_get_reboot_state,

    SelfSimulation_Exists p1 p2 rec valid_state R l_get_reboot_state ->
    SelfSimulation_Weak p1 p2 rec valid_state R l_get_reboot_state ->
    
    SelfSimulation p1 p2 rec valid_state R l_get_reboot_state.
Proof.
  unfold SelfSimulation_Exists, SelfSimulation_Weak, SelfSimulation; intros.
  edestruct H.
  3: eauto.
  all: eauto.
Qed.



(** Simulation **)
Definition SimulationForProgramGeneral
           T (p_abs: L_abs.(prog) T) (rec_abs : L_abs.(prog) unit)
           l_get_reboot_state_imp
           l_get_reboot_state_abs
           R_begin R_end :=
  forall l_o_imp l_o_abs s_imp s_abs,
    recovery_oracles_refine_to s_imp p_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    R_begin s_imp s_abs ->

    (forall s_imp',
       L_imp.(recovery_exec) l_o_imp s_imp
                             l_get_reboot_state_imp (R.(compile) p_abs)
                             (R.(compile) rec_abs) s_imp' ->
       exists s_abs',
         L_abs.(recovery_exec) l_o_abs s_abs l_get_reboot_state_abs p_abs rec_abs s_abs' /\
         R_end (extract_state_r s_imp') (extract_state_r s_abs') /\
         extract_ret_r s_imp' = extract_ret_r s_abs'
    ).

 Definition SimulationForProgram T (p_abs: L_abs.(prog) T) (rec_abs : L_abs.(prog) unit)
           l_get_reboot_state_imp
           l_get_reboot_state_abs :=
    SimulationForProgramGeneral T p_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs R.(refines_to) R.(refines_to).

Definition Simulation rec_abs l_get_reboot_state_imp l_get_reboot_state_abs
    := forall T (p_abs: L_abs.(prog) T),
         SimulationForProgram T p_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs.

End Relations.

Arguments recovery_oracles_refine_to {_ _ _ _} _ {_}.
Arguments refines_to_related {_ _ _ _}.
Arguments refines_to_valid {_ _ _ _}.
Arguments exec_compiled_preserves_validity {_ _ _ _} _ {_}.
Arguments abstract_oracles_exist_wrt {_ _ _ _} _ _ {_}.
Arguments oracle_refines_to_same_from_related {_ _ _ _} _ {_}.
Arguments SelfSimulation {_ _ _}.
Arguments SelfSimulation_Weak {_ _ _}.
Arguments SelfSimulation_Exists {_ _ _}.
Arguments Simulation {_ _ _ _}.
Arguments SimulationForProgram {_ _ _ _} _ {_}.


Lemma SS_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs,

    SelfSimulation
      p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      l_get_reboot_state_abs ->
    
    SimulationForProgram R p1_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    SimulationForProgram R p2_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracles_exist_wrt R R.(refines_to) p1_abs rec_abs l_get_reboot_state_imp ->
    abstract_oracles_exist_wrt R R.(refines_to) p2_abs rec_abs l_get_reboot_state_imp ->
    
    oracle_refines_to_same_from_related R p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    exec_compiled_preserves_validity R
    p1_abs rec_abs l_get_reboot_state_imp
    (refines_to_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    p2_abs rec_abs l_get_reboot_state_imp
    (refines_to_valid R valid_state_abs) ->

    SelfSimulation_Exists (compile R p1_abs)
    (compile R p2_abs) (compile R rec_abs)
    (refines_to_valid R valid_state_abs)
    (refines_to_related R equivalent_states_abs)
    l_get_reboot_state_imp ->
    
    SelfSimulation
      (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_to_valid R valid_state_abs)
      (refines_to_related R equivalent_states_abs)
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  eapply Self_Simulation_Weak_to_Self_Simulation; eauto.
  unfold SelfSimulation_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_to_valid, refines_to_related in *; cleanup. *)

  match goal with
  | [H: recovery_exec _ _ _ _ (compile _ ?p1) _ _,
     H0: recovery_exec _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_to_valid, refines_to_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine_to _ _ _ _ _ _ _,
     H0: recovery_oracles_refine_to _ _ _ _ _ _ _,
     H1: oracle_refines_to_same_from_related _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_to_related in *; cleanup.
  
  match goal with
  | [H: recovery_exec _ _ _ _ (compile _ ?p1) _ _,
     H0: recovery_exec _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ ?p1 _ _ _,
     H2: SimulationForProgram _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: recovery_exec L_abs _ _ _ p1_abs _ _,
     H0: recovery_exec L_abs _ _ _ _ _ _,
     H1: SelfSimulation _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: recovery_exec L_abs _ _ _ p2_abs _ _,
     H0: recovery_exec L_abs _ _ _ p2_abs _ _ |- _ ] =>
    eapply recovery_exec_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.
