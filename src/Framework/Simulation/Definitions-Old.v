Require Import Lia Primitives Layer.

Record CoreRefinement {O_imp} (L_imp: Language O_imp) (O_abs: Core) :=
  {
    compile_core : forall T, O_abs.(Core.operation) T -> L_imp.(prog) T;
    refines_to_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    refines_to_crash_core : L_imp.(state) -> O_abs.(Core.state) -> Prop;
    token_refines_to: forall T, L_imp.(state) -> O_abs.(Core.operation) T -> L_imp.(oracle) -> O_abs.(Core.token) -> Prop;

    (** We need this to lift Ret automatically **)
    refines_to_then_refines_to_crash_core:
      forall s1,
        (exists s2, refines_to_core s1 s2) ->
        (exists s2, refines_to_crash_core s1 s2);
    
    exec_compiled_preserves_refinement_finished_core :
      forall T (p2: O_abs.(Core.operation) T) o1 s1 s1' r,
        (exists s2, refines_to_core s1 s2) ->
        L_imp.(exec) o1 s1 (compile_core T p2) (Finished s1' r) ->
        (exists s2', refines_to_core s1' s2');

    exec_compiled_preserves_refinement_crashed_core :
      forall T (p2: O_abs.(Core.operation) T) o1 s1 s1',
        (exists s2, refines_to_core s1 s2) ->
        L_imp.(exec) o1 s1 (compile_core T p2) (Crashed s1') ->
        (exists s2', refines_to_crash_core s1' s2');
  }.


Arguments Build_CoreRefinement {_ _ _}.
Arguments compile_core {_ _ _} _ {_}.
Arguments refines_to_core {_ _ _}.
Arguments refines_to_crash_core {_ _ _}.
Arguments token_refines_to {_ _ _} _ {_}.
Arguments refines_to_then_refines_to_crash_core {_ _ _}.
Arguments exec_compiled_preserves_refinement_finished_core {_ _ _}.
Arguments exec_compiled_preserves_refinement_crashed_core {_ _ _}. 


Record Refinement {O_imp O_abs} (L_imp: Language O_imp) (L_abs: Language O_abs) :=
  {
    compile : forall T, L_abs.(prog) T -> L_imp.(prog) T;
    refines_to: L_imp.(state) -> L_abs.(state) -> Prop;
    refines_to_crash: L_imp.(state) -> L_abs.(state) -> Prop;
    oracle_refines_to: forall T, L_imp.(state) -> L_abs.(prog) T -> L_imp.(oracle) -> L_abs.(oracle) -> Prop;
    
    exec_compiled_preserves_refinement_finished :
      forall T (p2: L_abs.(prog) T) o1 s1 s1' r,
        (exists s2, refines_to s1 s2) ->
        L_imp.(exec) o1 s1 (compile T p2) (Finished s1' r) ->
        (exists s2', refines_to s1' s2');
    
    exec_compiled_preserves_refinement_crashed :
      forall T (p2: L_abs.(prog) T) o1 s1 s1',
        (exists s2, refines_to s1 s2) ->
        L_imp.(exec) o1 s1 (compile T p2) (Crashed s1') ->
        (exists s2', refines_to_crash s1' s2');
  }.


Arguments Build_Refinement {_ _ _ _}.
Arguments compile {_ _ _ _} _ {_}.
Arguments refines_to {_ _ _ _}.
Arguments refines_to_crash {_ _ _ _}.
Arguments oracle_refines_to {_ _ _ _} _ {_}.
Arguments exec_compiled_preserves_refinement_finished {_ _ _ _}.
Arguments exec_compiled_preserves_refinement_crashed {_ _ _ _}.

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
      R.(oracle_refines_to) s p_abs o_imp o_abs /\
      (forall s',
         L_imp.(exec) o_imp s (R.(compile) p_abs) (Crashed s') ->
         match l_get_reboot_state_imp with
         | get_reboot_state_imp :: lgrsi =>
           recovery_oracles_refine_to (get_reboot_state_imp s') rec_abs rec_abs lgrsi loi loa
         | _ => False
         end)
    | _, _ => False
    end.
  
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

(** 
A relation that takes 
   - an input state (si), 
   - a refinement realiton (refines_to), and
   - a validity predicate (valid_state_abs)
and asserts that 
    - for all states sa,
    - if si refines to sa via refines_to relation,
    - then sa is a valid state (satisfies valid_state_abs)
 **)
Definition refines_to_valid 
           (valid_state_abs: L_abs.(state) -> Prop)
           (si: L_imp.(state))
  : Prop :=
  forall (sa: L_abs.(state)),
    R.(refines_to) si sa ->
    valid_state_abs sa.

Definition refines_to_valid_crash 
           (valid_crash_state_abs: L_abs.(state) -> Prop)
           (si: L_imp.(state))
  : Prop :=
  forall (sa: L_abs.(state)),
    R.(refines_to_crash) si sa ->
    valid_crash_state_abs sa.

Definition exec_preserves_validity (valid_state valid_crash_state: L_abs.(state) -> Prop) :=
    forall T (p: L_abs.(prog) T) o s ret,
      valid_state s ->
      exec L_abs o s p ret ->
      (exists s' r, ret = Finished s' r /\ valid_state s') \/
      (exists s', ret = Crashed s' /\ valid_crash_state s').


Definition exec_compiled_preserves_validity (valid_state valid_crash_state: L_imp.(state) -> Prop) := 
    forall T (p2: L_abs.(prog) T) o s ret,
      valid_state s ->
      L_imp.(exec) o s (R.(compile) p2) ret ->
      (exists s' r, ret = Finished s' r /\ valid_state s') \/
      (exists s', ret = Crashed s' /\ valid_crash_state s').

Definition abstract_oracle_exists :=
  forall T (p_abs: L_abs.(prog) T) oi si si',
    (exists sa, R.(refines_to) si sa) -> 
    L_imp.(exec) oi si (R.(compile) p_abs) si' ->
    exists oa, R.(oracle_refines_to) si p_abs oi oa.

Definition oracle_refines_to_same_from_related 
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall T oi oa si1 si2 (p_abs: L_abs.(prog) T),
    refines_to_related related_states_abs si1 si2 ->
    R.(oracle_refines_to) si1 p_abs oi oa ->
    R.(oracle_refines_to) si2 p_abs oi oa.


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


(** Simulation **)
Definition SimulationForProgram
           {T} (p_abs: L_abs.(prog) T) (rec_abs : L_abs.(prog) unit)
           l_get_reboot_state_imp
           l_get_reboot_state_abs :=
  forall l_o_imp l_o_abs s_imp s_abs,
    recovery_oracles_refine_to s_imp p_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    R.(refines_to) s_imp s_abs ->
    
    (forall s_imp',
       L_imp.(recovery_exec) l_o_imp s_imp l_get_reboot_state_imp (R.(compile) p_abs) (R.(compile) rec_abs) s_imp' ->
       exists s_abs',
         L_abs.(recovery_exec) l_o_abs s_abs l_get_reboot_state_abs p_abs rec_abs s_abs' /\
         R.(refines_to) (extract_state_r s_imp') (extract_state_r s_abs') /\
         extract_ret_r s_imp' = extract_ret_r s_abs'
    ).

Definition Simulation rec_abs l_get_reboot_state_imp l_get_reboot_state_abs
  := forall T (p_abs: L_abs.(prog) T), SimulationForProgram p_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs.


(** Bisimulation 

Definition StrongBisimulationForValidStates
       (valid_state1 : L_imp.(state) -> Prop)
       (valid_state2 : L_abs.(state) -> Prop)
       (valid_prog2: forall T, L_abs.(prog) T -> Prop)
  :=
      forall T p2 s1 s2 o1 o2,
          valid_state1 s1 ->          
          valid_state2 s2 ->
          valid_prog2 T p2 ->
          
          R.(refines_to) s1 s2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->

          (forall s1',
          L_imp.(exec) o1 s1 (R.(compile) p2) s1' ->
          match s1' with
          | Finished s1' t =>
            exists s2',
            L_abs.(exec) o2 s2 p2 (Finished s2' t) /\
            R.(refines_to) s1' s2' /\
            valid_state1 s1' /\
            valid_state2 s2'
                         
          | Crashed s1' =>
            exists s2',
            L_abs.(exec) o2 s2 p2 (Crashed s2') /\
            R.(refines_to) s1' s2' /\
            forall s1r,
              L_imp.(after_reboot) s1' s1r ->
              exists s2r,
                L_abs.(after_reboot) s2' s2r /\
                R.(refines_to) s1r s2r /\
                valid_state1 s1r /\
                valid_state2 s2r
          end
          ) /\
          (forall s2',
             L_abs.(exec) o2 s2 p2 s2' ->
             match s2' with
             | Finished s2' t =>
               exists s1',
               L_imp.(exec) o1 s1 (R.(compile) p2) (Finished s1' t) /\
               R.(refines_to) s1' s2' /\
               valid_state1 s1' /\
               valid_state2 s2'
             | Crashed s2' =>
               exists s1',
               L_imp.(exec) o1 s1 (R.(compile) p2) (Crashed s1') /\
               R.(refines_to) s1' s2' /\
               forall s2r,
                 L_abs.(after_reboot) s2' s2r ->
                 exists s1r,
                   L_imp.(after_reboot) s1' s1r /\
                   R.(refines_to) s1r s2r /\
                   valid_state1 s1r /\
                   valid_state2 s2r
             end).


Definition StrongBisimulationForProgram_exec
       {T} (p2: L_abs.(prog) T) :=
      (forall s1 s2 o1 o2,
          
          R.(refines_to) s1 s2 ->
          R.(oracle_refines_to) s1 p2 o1 o2 ->
          
          (forall s1',
              L_imp.(exec) o1 s1 (R.(compile) p2) s1' ->
              exists s2',
                L_abs.(exec) o2 s2 p2 s2' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2') /\
          (forall s2',
              L_abs.(exec) o2 s2 p2 s2' ->
              exists s1',
                L_imp.(exec) o1 s1 (R.(compile) p2) s1' /\
                R.(refines_to) (extract_state s1') (extract_state s2') /\
                extract_ret s1' = extract_ret s2')).

Definition StrongBisimulation_exec 
  := forall T (p2: L_abs.(prog) T), StrongBisimulationForProgram_exec p2.

Definition StrongBisimulationForProgram
           {T} (p2: L_abs.(prog) T) (rec : L_abs.(prog) unit)
           get_reboot_state_l
           get_reboot_state_h :=
  forall s1 s2 o1 o2 o1r o2r,
      R.(refines_to) s1 s2 ->
      R.(oracle_refines_to) s1 p2 o1 o2 ->

      (** TODO: Verbally explain what this is and why it is here **)
      (forall s1c,
         L_imp.(exec) o1 s1 (R.(compile) p2) (Crashed s1c) ->
         R.(oracle_refines_to) (get_reboot_state_l s1c) rec o1r o2r) ->

      (forall s1',
          L_imp.(recovery_exec) o1 o1r s1 (R.(compile) p2) get_reboot_state_l (R.(compile) rec) s1' ->
          exists s2',
            L_abs.(recovery_exec) o2 o2r s2 p2 get_reboot_state_h rec s2' /\
            R.(refines_to) (extract_state_r s1') (extract_state_r s2') /\
            extract_ret_r s1' = extract_ret_r s2'
       ) /\
       (forall s2',
          L_abs.(recovery_exec) o2 o2r s2 p2 get_reboot_state_h rec s2' ->
          exists s1',
            L_imp.(recovery_exec) o1 o1r s1 (R.(compile) p2) get_reboot_state_l (R.(compile) rec) s1' /\
            R.(refines_to) (extract_state_r s1') (extract_state_r s2') /\
            extract_ret_r s1' = extract_ret_r s2').

Definition StrongBisimulation rec get_reboot_state_l get_reboot_state_h
  := forall T (p2: L_abs.(prog) T), StrongBisimulationForProgram p2 rec get_reboot_state_l get_reboot_state_h.
**)

End Relations.


Arguments recovery_oracles_refine_to {_ _ _ _} _ {_}.
Arguments refines_to_related {_ _ _ _}.
Arguments refines_to_valid {_ _ _ _}.
Arguments refines_to_valid_crash {_ _ _ _}.
Arguments exec_preserves_validity {_}.
Arguments exec_compiled_preserves_validity {_ _ _ _}.
Arguments abstract_oracle_exists {_ _ _ _}.
Arguments oracle_refines_to_same_from_related {_ _ _ _}.
Arguments SelfSimulation {_ _ _}.
Arguments SelfSimulation_Weak {_ _ _}.
Arguments Simulation {_ _ _ _}.
Arguments SimulationForProgram {_ _ _ _} _ {_}.



Lemma Self_Simulation_Weak_to_Self_Simulation:
  forall O (L: Language O) T (p1 p2: L.(prog) T) R
    valid_state rec l_get_reboot_state,
    
    SelfSimulation_Weak p1 p2 rec valid_state R l_get_reboot_state ->
    
    (forall s1 s1' s2 lo,
       valid_state s1 ->
       valid_state s2 -> 
       recovery_exec L lo s1 l_get_reboot_state p1 rec s1' ->
       R s1 s2 ->
       exists s2', 
         recovery_exec L lo s2 l_get_reboot_state p2 rec s2') ->
    
    SelfSimulation p1 p2 rec valid_state R l_get_reboot_state.
Proof.
  unfold SelfSimulation_Weak, SelfSimulation; intros.
  edestruct H0.
  3: eauto.
  all: eauto.
Qed.

Lemma abstract_oracle_exists_recovery_exec:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    l_o_imp T (p_abs: L_abs.(prog) T) rec_abs s_imp ret_imp l_get_reboot_state_imp,
    
    (exists s_abs, R.(refines_to) s_imp s_abs) -> 
    abstract_oracle_exists R  ->
    
    (forall s_imp' get_reboot_state_imp,
       In get_reboot_state_imp l_get_reboot_state_imp ->
       (exists s_abs', R.(refines_to_crash) s_imp' s_abs') ->
       (exists s_abs_r, R.(refines_to) (get_reboot_state_imp s_imp') s_abs_r)) ->
    (forall s1, (exists s2, refines_to R s1 s2) ->
           exists s2, refines_to_crash R s1 s2) ->
    recovery_exec L_imp l_o_imp s_imp l_get_reboot_state_imp (compile R p_abs) (compile R rec_abs) ret_imp ->
    exists l_o_abs, recovery_oracles_refine_to R s_imp p_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs.
Proof.
  induction l_o_imp; simpl; intros; invert_exec; eauto.
  simpl in *.
  eapply_fresh H0 in H11; eauto.
  cleanup.
  exists [x]; repeat split; intros; eauto.
  eapply exec_deterministic_wrt_oracle in H11; eauto; cleanup.
  
  eapply_fresh H0 in H12; eauto.
  cleanup.
  eapply exec_compiled_preserves_refinement_crashed in H12 as Hx; eauto.
  simpl in *.
  edestruct IHl_o_imp.
  5: eauto.
  all: eauto.
  exists (x::x1); repeat split; intros; eauto.
  destruct l_o_imp, x1; simpl in *; try intuition.
  eapply exec_deterministic_wrt_oracle in H12; eauto; cleanup; eauto.  
Qed.


Lemma exec_compiled_preserves_validity_recovery_exec:
    forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
      l_o_imp T (p_abs: L_abs.(prog) T) rec_abs (valid_state_imp: L_imp.(state) -> Prop) (valid_crash_state_imp: L_imp.(state) -> Prop) s_imp l_get_reboot_state_imp ret_imp,
      recovery_exec L_imp l_o_imp s_imp l_get_reboot_state_imp (compile R p_abs) (compile R rec_abs) ret_imp ->
      (exec_compiled_preserves_validity R valid_state_imp valid_crash_state_imp ->
      valid_state_imp s_imp ->
      
      (forall s get_reboot_state_imp,
         In get_reboot_state_imp l_get_reboot_state_imp ->
         valid_crash_state_imp s ->
         valid_state_imp (get_reboot_state_imp s)) ->
      
      valid_state_imp (extract_state_r ret_imp)).
Proof.
  induction l_o_imp; simpl; intros; invert_exec.
  eapply H0 in H10; eauto.
  split_ors; cleanup.
  simpl; eauto.
  eapply_fresh H0 in H11; eauto.
  split_ors; cleanup.
  
  eapply_fresh H2 in H3; [|left; eauto].
  destruct ret.
  inversion H12; cleanup.
  eapply H0 in H10; try split_ors; cleanup; eauto.
  specialize (IHl_o_imp unit);
  eapply IHl_o_imp; simpl; eauto.
  intros; eapply H2; eauto.
  right; eauto.
Qed.

Lemma SS_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
      T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      valid_crash_state_abs,

    SelfSimulation
      p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      l_get_reboot_state_abs ->
    
    Simulation R rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracle_exists R ->
    
    oracle_refines_to_same_from_related R equivalent_states_abs ->

    exec_compiled_preserves_validity R                           
    (refines_to_valid R valid_state_abs)
    (refines_to_valid_crash R valid_crash_state_abs) ->
    
    (** This is needed to ensure that oracle doesn't expose secret data in the program. 
        TODO: Turn into a definition **)      
    (forall s1_imp s2_imp l_o_imp l_o_abs l_o_abs',
       refines_to_valid R valid_state_abs s1_imp ->
       refines_to_valid R valid_state_abs s2_imp ->
       refines_to_related R equivalent_states_abs s1_imp s2_imp ->
       recovery_oracles_refine_to R s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
       recovery_oracles_refine_to R s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
       l_o_abs = l_o_abs') ->

    (** TODO: Turn into a definition. It can be named get_reboot_state_preserves_validity. **)
    (forall s_imp get_reboot_state_imp,
       In get_reboot_state_imp l_get_reboot_state_imp ->
       (forall s_abs, refines_to_crash R s_imp s_abs -> valid_crash_state_abs s_abs) ->
       forall s_abs', refines_to R (get_reboot_state_imp s_imp) s_abs' -> valid_state_abs s_abs') ->

    (** TODO: Turn into a definition. It can be named get_reboot_state_preserves_refinement. **)
    (forall s_imp' get_reboot_state_imp,
       In get_reboot_state_imp l_get_reboot_state_imp ->
       (exists s_abs', refines_to_crash R s_imp' s_abs') ->
       exists s_abs_r, refines_to R (get_reboot_state_imp s_imp') s_abs_r) ->

    (** TODO: Turn into a definition. **)
    (forall s1_imp s2_imp ret1_imp l_o_imp,
       refines_to_valid R valid_state_abs s1_imp ->
       refines_to_valid R valid_state_abs s2_imp ->
       refines_to_related R equivalent_states_abs s1_imp s2_imp ->
       recovery_exec L_imp l_o_imp s1_imp l_get_reboot_state_imp (compile R p1_abs) (compile R rec_abs) ret1_imp ->
       
       exists ret2_imp,
         recovery_exec L_imp l_o_imp s2_imp l_get_reboot_state_imp (compile R p2_abs) (compile R rec_abs) ret2_imp) ->

    (forall s_imp,
       (exists s_abs, refines_to R s_imp s_abs) ->
       exists s_abs, refines_to_crash R s_imp s_abs) ->
    
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
  unfold refines_to_valid, refines_to_related in *; cleanup.
  match goal with
  | [H: recovery_exec _ _ _ _ _ _ _,
     H0: recovery_exec _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh abstract_oracle_exists_recovery_exec in H; eauto; cleanup;
    eapply_fresh abstract_oracle_exists_recovery_exec in H0; eauto; cleanup
  end.
  
  match goal with
  | [H: recovery_oracles_refine_to _ _ _ _ _ _ _,
     H0: recovery_oracles_refine_to _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H4 in H; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  match goal with
  | [H: recovery_exec _ _ _ _ _ _ _,
     H0: recovery_exec _ _ _ _ _ _ _,
     H1: Simulation _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H1 in H0; eauto; cleanup
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

  - pose proof exec_compiled_preserves_validity_recovery_exec as Hy.
    specialize Hy with (1:= H9) (2:= H3).
    simpl in *.
    eapply Hy; eauto.
    
  - pose proof exec_compiled_preserves_validity_recovery_exec as Hy.
    specialize Hy with (1:= H10) (2:=H3).
    simpl in *.
    eapply Hy; eauto.
Qed.


(** Theorems for breaking down SelfSimulation proofs **)

Section Relations.
  Variable O_abs: Core.
  Variable L_abs: Language O_abs.
  
  Definition SelfSimulation_Exec {T}
             (p1 p2: L_abs.(prog) T)
             (valid_state: L_abs.(state) -> Prop)
             (valid_crash_state: L_abs.(state) -> Prop)
             (R: L_abs.(state) -> L_abs.(state) -> Prop)
             (R_crash: L_abs.(state) -> L_abs.(state) -> Prop) :=
    forall o s1_abs ret1_abs s2_abs,
      valid_state s1_abs ->
      valid_state s2_abs ->
      L_abs.(exec) o s1_abs p1 ret1_abs ->
      R s1_abs s2_abs ->
      exists ret2_abs,
        L_abs.(exec) o s2_abs p2 ret2_abs /\
        extract_ret ret1_abs = extract_ret ret2_abs /\
        ((exists s r,  ret2_abs = Finished s r /\
                 R (extract_state ret1_abs) (extract_state ret2_abs) /\
                 valid_state (extract_state ret1_abs) /\
                 valid_state (extract_state ret2_abs)) \/
         (exists s,  ret2_abs = Crashed s /\
                 R_crash (extract_state ret1_abs) (extract_state ret2_abs) /\
                 valid_crash_state (extract_state ret1_abs) /\
                 valid_crash_state (extract_state ret2_abs)) ).
  End Relations.

  Theorem SSE_to_SS :
    forall T O (L: Language O) (p1 p2: L.(prog) T) rec
      l_get_reboot_state simulation_relation simulation_relation_crash
    valid_state valid_crash_state,
      SelfSimulation_Exec _ L p1 p2 valid_state valid_crash_state simulation_relation simulation_relation_crash->
      SelfSimulation_Exec _ L rec rec valid_state valid_crash_state simulation_relation simulation_relation_crash->

      (** TODO: Turn this into a definition **)
      (forall get_reboot_state,
         In get_reboot_state l_get_reboot_state ->
         forall s,
           valid_crash_state s ->
           valid_state (get_reboot_state s)) ->

      (** TODO: Turn this into a definition **)
      (forall get_reboot_state,
         In get_reboot_state l_get_reboot_state ->
         forall s s',
           simulation_relation_crash s s' ->
           simulation_relation (get_reboot_state s) (get_reboot_state s')) ->
      
      SelfSimulation p1 p2 rec valid_state simulation_relation l_get_reboot_state.
  Proof.
    unfold SelfSimulation.
    induction 5; intros.
    {
      eapply H in H3.
      specialize H3 with (1:= H6); cleanup.
      split_ors; cleanup;
      simpl in *; cleanup.
      eexists; repeat (split; eauto).    
      econstructor; eauto.
      all: simpl; eauto.      
    }
    
    {
      eapply H in H3.
      specialize H3 with (1:= H7); cleanup.
      split_ors; cleanup;
      simpl in *; cleanup.     

      edestruct IHrecovery_exec'; cleanup.
      6: instantiate (1:=get_reboot_state x0).
      all: eauto.
      
      eexists; repeat (split; eauto).    
      econstructor; eauto.
      all: simpl; eauto.
    }
  Qed.

  
(** Proofs about simplifying StrongSimulation proofs **)

(** WP reasoning for proving Simulations *)
Section LanguageWP.
  Variable O_imp O_abs: Core.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable R: Refinement L_imp L_abs.

  
(* Per prog ones *)
Definition wp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1' v,
     L_imp.(weakest_precondition) (R.(compile) p2)  (fun r s => exists s2', R.(refines_to) s s2' /\ r = v) o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Finished s1' v) ->
     L_abs.(weakest_precondition) p2 (fun r s => R.(refines_to) s1' s /\ r = v) o2 s2.

Definition wcp_low_to_high_prog' T (p2: L_abs.(prog) T) :=
  forall o1 o2 s1 s2 s1',
     L_imp.(weakest_crash_precondition) (R.(compile) p2) (fun s => exists s2', R.(refines_to_crash) s s2') o1 s1 ->
     R.(refines_to) s1 s2 ->
     R.(oracle_refines_to) s1 p2 o1 o2 ->
     L_imp.(exec) o1 s1 (R.(compile) p2) (Crashed s1') ->
     L_abs.(weakest_crash_precondition) p2 (fun s => R.(refines_to_crash) s1' s) o2 s2.

Record WP_Simulation_prog T p2:=
  {
    wp_low_to_high_prog : wp_low_to_high_prog' T p2;
    wcp_low_to_high_prog : wcp_low_to_high_prog' T p2;
  }.


End LanguageWP.

Arguments WP_Simulation_prog {_ _ _ _} _ {_}.

Theorem Simulation_from_wp_prog :
  forall OL OH (LL: Language OL) (LH: Language OH) (R: Refinement LL LH) T (p2: LH.(prog) T) rec l_get_reboot_state_imp l_get_reboot_state_abs,
    
    WP_Simulation_prog R p2 ->

    WP_Simulation_prog R rec ->

    length l_get_reboot_state_imp = length l_get_reboot_state_abs ->

    (** TODO: turn this into definition **)
    (forall i,
       i < length l_get_reboot_state_imp ->
       let get_reboot_state_imp := seln l_get_reboot_state_imp i id in
       let get_reboot_state_abs := seln l_get_reboot_state_abs i id in
       forall s s',
         refines_to_crash R s s' ->
         refines_to R (get_reboot_state_imp s) (get_reboot_state_abs s')) ->
    
    SimulationForProgram R p2 rec l_get_reboot_state_imp l_get_reboot_state_abs.
Proof.  
  unfold SimulationForProgram.
  do 15 intro.
  generalize dependent rec.
  generalize dependent T.
  generalize dependent l_get_reboot_state_abs.
  generalize dependent l_get_reboot_state_imp.
  induction l_o_imp;
  intros; cleanup; invert_exec.
    
  { (** Finished **)
    pose proof exec_to_wp as Hx.
    match goal with
    |[H: Language.exec' _ _ _ _  |- _ ] =>
     specialize Hx with (1:= H); simpl in *
    end.
    cleanup; intuition.
    edestruct wp_to_exec.
    eapply wp_low_to_high_prog.
    apply H.
    all: eauto.
    eapply Hx; eauto.
    
    match goal with
    |[H: Language.exec' _ _ _ _  |- _ ] =>
     eapply exec_compiled_preserves_refinement_finished in H; eauto
    end.
    
    simpl in *; cleanup.
    eexists; eauto.
    cleanup.
    eexists; split; try econstructor; eauto.
    simpl in *.
    destruct l; simpl in *.
    econstructor; eauto.
    inversion H3.
    all: simpl; eauto.
  }
  { (** Crashed **)
    pose proof exec_to_wcp as Hx.
    match goal with
    |[H: Language.exec' _ _ _ _  |- _ ] =>
     specialize Hx with (1:= H); simpl in *
    end.
    cleanup; intuition.
    edestruct wcp_to_exec.
    eapply wcp_low_to_high_prog.
    apply H.
    all: eauto.
    eapply Hx; eauto.
    
    match goal with
    |[H: Language.exec' _ _ _ _  |- _ ] =>
     eapply exec_compiled_preserves_refinement_crashed in H; eauto
    end.
    
    simpl in *; cleanup.
    destruct l_get_reboot_state_abs; simpl in *; cleanup.
    inversion H1.
    edestruct IHl_o_imp; eauto.
    intros.
    specialize (H2 (S i)); simpl in *; eauto.    
    eapply H2; try lia.
    eauto.

    specialize (H2 0); simpl in *; eauto.    
    eapply H2; try lia.
    eauto.
   
    cleanup.
    eexists; split; try econstructor; eauto.
  }
Qed.
