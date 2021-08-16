Require Import Lia Primitives Layer.

Record CoreRefinement {O_imp} (L_imp: Language O_imp) (O_abs: Core) :=
  {
    compile_core : forall T, O_abs.(Core.operation) T -> L_imp.(prog) T;
    refines_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    refines_reboot_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    token_refines: forall T, user -> L_imp.(state) -> O_abs.(Core.operation) T -> (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> O_abs.(Core.token) -> Prop;
    exec_compiled_preserves_refinement_finished_core :
      forall T (p2: O_abs.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines_core s1 s2) ->
        L_imp.(exec) u o1 s1 (compile_core T p2) (Finished s1' r) ->
        (exists s2', refines_core s1' s2');
  }.

Record Refinement {O_imp O_abs} (L_imp: Language O_imp) (L_abs: Language O_abs) :=
  {
    compile : forall T, L_abs.(prog) T -> L_imp.(prog) T;
    refines: L_imp.(state) -> L_abs.(state) -> Prop;
    refines_reboot: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    oracle_refines: forall T, user -> L_imp.(state) -> L_abs.(prog) T -> (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> L_abs.(oracle) -> Prop;
    exec_compiled_preserves_refinement_finished :
      forall T (p2: L_abs.(prog) T) o1 s1 s1' r u,
        (exists s2, refines s1 s2) ->
        L_imp.(exec) u o1 s1 (compile T p2) (Finished s1' r) ->
        (exists s2', refines s1' s2');
  }.

Arguments Build_CoreRefinement {_ _ _}.
Arguments compile_core {_ _ _} _ {_}.
Arguments refines_core {_ _ _}.
Arguments refines_reboot_core {_ _ _}.
Arguments token_refines {_ _ _} _ {_}.
Arguments exec_compiled_preserves_refinement_finished_core {_ _ _}.

Arguments Build_Refinement {_ _ _ _}.
Arguments compile {_ _ _ _} _ {_}.
Arguments refines {_ _ _ _}.
Arguments refines_reboot {_ _ _ _}.
Arguments oracle_refines {_ _ _ _} _ {_}.
Arguments exec_compiled_preserves_refinement_finished {_ _ _ _}.

Section Relations.
  Variable O_imp O_abs: Core.
  Variable L_imp: Language O_imp.
  Variable L_abs: Language O_abs.
  Variable R : Refinement L_imp L_abs.
  
  Fixpoint recovery_oracles_refine_to {T}
           (u: user) (s: L_imp.(state)) (p_abs: L_abs.(prog) T) (rec_abs: L_abs.(prog) unit)
           (l_get_reboot_state_imp: list (L_imp.(state) -> L_imp.(state)))
           (lo_imp: list L_imp.(oracle)) (lo_abs: list L_abs.(oracle)) {struct lo_imp} :=
    match lo_imp, lo_abs with
    | o_imp :: loi, o_abs :: loa =>
      length lo_imp = length lo_abs /\
      ((exists s' t,
         L_imp.(exec) u o_imp s (R.(compile) p_abs) (Finished s' t) /\
         (forall grs_imp, R.(oracle_refines) u s p_abs grs_imp o_imp o_abs) /\
         loi = [] /\ loa = []) \/
      (exists s',
         L_imp.(exec) u o_imp s (R.(compile) p_abs) (Crashed s') /\
         match l_get_reboot_state_imp with
         | get_reboot_state_imp :: lgrsi =>
           R.(oracle_refines) u s p_abs get_reboot_state_imp o_imp o_abs /\
           recovery_oracles_refine_to u (get_reboot_state_imp s') rec_abs rec_abs lgrsi loi loa
           (*  /\ loi <> [] /\ loa <> [] *)
         | _ => False
         end))
    | _, _ => False
    end.

Definition abstract_oracles_exist_wrt Rel (u: user) {T} (p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state :=
  forall l_oi si si',
    (exists sa: L_abs.(state), Rel si sa) -> 
    L_imp.(recovery_exec) u l_oi si l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) si' ->
    exists l_oa, recovery_oracles_refine_to u si p_abs rec_abs l_get_reboot_state l_oi l_oa.

(** 
A relation that takes 
   - two input states (si1 and si2), 
   - a refinement realiton (refines), and
   - a relation (related_abs)
and asserts that 
    - there are two other abstract states (sa1 and sa2) such that,
    - si1 (si2) refines to sa1 (sa2) via refines relation, and
    - sa1 and sa2 are related via related_abs
**)
  Definition refines_related 
             (related_abs:  L_abs.(state) -> L_abs.(state) -> Prop)
             (si1 si2: L_imp.(state))
    : Prop :=
    exists (sa1 sa2: L_abs.(state)),
      R.(refines) si1 sa1 /\
      R.(refines) si2 sa2 /\
      related_abs sa1 sa2.

Definition refines_related_reboot
(related_abs:  L_abs.(state) -> L_abs.(state) -> Prop)
(si1 si2: L_imp.(state))
: Prop :=
exists (sa1 sa2: L_abs.(state)),
R.(refines_reboot) si1 sa1 /\
R.(refines_reboot) si2 sa2 /\
related_abs sa1 sa2.


Definition refines_valid 
           (valid_state_abs: L_abs.(state) -> Prop)
           (si: L_imp.(state))
  : Prop :=
  forall (sa: L_abs.(state)),
    R.(refines) si sa ->
    valid_state_abs sa.


Definition exec_compiled_preserves_validity  {T} (u: user)(p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state (valid_state: L_imp.(state) -> Prop) := 
    forall l_oi s ret,
      valid_state s ->
      L_imp.(recovery_exec) u l_oi s l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) ret ->
      valid_state (extract_state_r ret).


Definition oracle_refines_same_from_related
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine_to u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine_to u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.


Definition oracle_refines_same_from_related_reboot
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related_reboot related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine_to u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine_to u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.
(** Self Simulation **)
(**
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
**)

Definition SelfSimulation (u: user) {T} (p1 p2: L_abs.(prog) T)
       (rec: L_abs.(prog) unit)
       (valid_state: L_abs.(state) -> Prop)
       (R: L_abs.(state) -> L_abs.(state) -> Prop)
       (cond: user -> Prop)
       l_get_reboot_state :=
  forall lo s1 s1',
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    valid_state s1 ->
    forall s2,
    valid_state s2 ->
    R s1 s2 ->
    exists s2',
      L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2' /\
      R (extract_state_r s1') (extract_state_r s2') /\
      (cond u -> extract_ret_r s1' = extract_ret_r s2') /\
      valid_state (extract_state_r s1') /\
      valid_state (extract_state_r s2').

Definition Termination_Sensitive u {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           l_get_reboot_state :=
  forall s1 s1' s2 lo,
    valid_state s1 ->
    valid_state s2 -> 
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    R s1 s2 ->
    exists s2', 
      L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2'.

Definition SelfSimulation_Weak u {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           (cond: user -> Prop)
           l_get_reboot_state :=
  forall lo s1 s1' s2 s2',
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2' ->
    valid_state s1 ->
    valid_state s2 ->
    R s1 s2 ->
    R (extract_state_r s1') (extract_state_r s2') /\
    (cond u -> extract_ret_r s1' = extract_ret_r s2') /\
    valid_state (extract_state_r s1') /\
    valid_state (extract_state_r s2').

Lemma Self_Simulation_Weak_to_Self_Simulation:
  forall u T (p1 p2: L_abs.(prog) T) R
    valid_state rec cond l_get_reboot_state,

    Termination_Sensitive u p1 p2 rec valid_state R l_get_reboot_state ->
    SelfSimulation_Weak u p1 p2 rec valid_state R cond l_get_reboot_state ->
    
    SelfSimulation u p1 p2 rec valid_state R cond l_get_reboot_state.
Proof.
  unfold Termination_Sensitive, SelfSimulation_Weak, SelfSimulation; intros.
  edestruct H.
  3: eauto.
  all: eauto.
Qed.


(** Simulation **)
Definition SimulationForProgramGeneral
           u T (p_abs: L_abs.(prog) T) (rec_abs : L_abs.(prog) unit)
           l_get_reboot_state_imp
           l_get_reboot_state_abs
           R_begin R_end :=
  forall l_o_imp l_o_abs s_imp s_abs,
    recovery_oracles_refine_to u s_imp p_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    R_begin s_imp s_abs ->

    (forall s_imp',
       L_imp.(recovery_exec) u l_o_imp s_imp
        l_get_reboot_state_imp (R.(compile) p_abs)
        (R.(compile) rec_abs) s_imp' ->
       exists s_abs',
         L_abs.(recovery_exec) u l_o_abs s_abs l_get_reboot_state_abs p_abs rec_abs s_abs' /\
         R_end (extract_state_r s_imp') (extract_state_r s_abs') /\
         extract_ret_r s_imp' = extract_ret_r s_abs'
    ).

 Definition SimulationForProgram u T (p_abs: L_abs.(prog) T) (rec_abs : L_abs.(prog) unit)
           l_get_reboot_state_imp
           l_get_reboot_state_abs :=
    SimulationForProgramGeneral u T p_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs R.(refines) R.(refines).

Definition Simulation rec_abs l_get_reboot_state_imp l_get_reboot_state_abs
    := forall u T (p_abs: L_abs.(prog) T),
         SimulationForProgram u T p_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs.


(*** ALL VALID EXPERIMENT ***)
Definition SelfSimulation_All_Valid (u: user) {T} (p1 p2: L_abs.(prog) T)
       (rec: L_abs.(prog) unit)
       (R: L_abs.(state) -> L_abs.(state) -> Prop)
       (cond: user -> Prop)
       l_get_reboot_state :=
  forall lo s1 s1',
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    forall s2,
    R s1 s2 ->
    exists s2',
      L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2' /\
      R (extract_state_r s1') (extract_state_r s2') /\
      (cond u -> extract_ret_r s1' = extract_ret_r s2').

Definition Termination_Sensitive_All_Valid  u {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           l_get_reboot_state :=
  forall s1 s1' s2 lo,
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    R s1 s2 ->
    exists s2', 
      L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2'.

Definition SelfSimulation_Weak_All_Valid  u {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           (cond: user -> Prop)
           l_get_reboot_state :=
  forall lo s1 s1' s2 s2',
    L_abs.(recovery_exec) u lo s1 l_get_reboot_state p1 rec s1' ->
    L_abs.(recovery_exec) u lo s2 l_get_reboot_state p2 rec s2' ->
    R s1 s2 ->
    R (extract_state_r s1') (extract_state_r s2') /\
    (cond u -> extract_ret_r s1' = extract_ret_r s2').

Lemma Self_Simulation_Weak_to_Self_Simulation_All_Valid :
  forall u T (p1 p2: L_abs.(prog) T) R
    rec cond l_get_reboot_state,

    Termination_Sensitive_All_Valid  u p1 p2 rec R l_get_reboot_state ->
    SelfSimulation_Weak_All_Valid  u p1 p2 rec R cond l_get_reboot_state ->
    
    SelfSimulation_All_Valid  u p1 p2 rec R cond l_get_reboot_state.
Proof.
  unfold Termination_Sensitive_All_Valid , SelfSimulation_Weak_All_Valid ,
  SelfSimulation_All_Valid ; intros.
  edestruct H.
  3: eauto.
  all: eauto.
Qed.

(*** ALL VALID EXPERIMENT END ***)




(******TS EXPERIMENT BEGIN *****)
Definition TS_N u {T} (p1 p2: L_abs.(prog) T)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           :=
  forall s1 s1' s2 o,
    valid_state s1 ->
    valid_state s2 -> 
    L_abs.(exec) u o s1 p1 s1' ->
    R s1 s2 ->
    exists s2', 
      L_abs.(exec) u o s2 p2 s2'.

Definition TS_N_F u {T} {T'} (p1: L_abs.(prog) T) 
(p2: L_abs.(prog) T')
(valid_state: L_abs.(state) -> Prop)
(R: L_abs.(state) -> L_abs.(state) -> Prop)
:=
forall s1 s1' r1 s2 o,
valid_state s1 ->
valid_state s2 -> 
L_abs.(exec) u o s1 p1 (Finished s1' r1) ->
R s1 s2 ->
exists s2' r2, 
 L_abs.(exec) u o s2 p2 (Finished s2' r2).

 Definition TS_N_C u 
 {T} {T'} (p1: L_abs.(prog) T) 
(p2: L_abs.(prog) T')
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           :=
  forall s1 s1' s2 o,
    valid_state s1 ->
    valid_state s2 -> 
    L_abs.(exec) u o s1 p1 (Crashed s1') ->
    R s1 s2 ->
    exists s2', 
      L_abs.(exec) u o s2 p2 (Crashed s2').


(******* TS EXPERIMENT END ******)
End Relations.

Arguments recovery_oracles_refine_to {_ _ _ _} _ {_}.
Arguments refines_related {_ _ _ _}.
Arguments refines_valid {_ _ _ _}.
Arguments exec_compiled_preserves_validity {_ _ _ _} _ {_}.
Arguments abstract_oracles_exist_wrt {_ _ _ _} _ _ _ {_}.
Arguments oracle_refines_same_from_related {_ _ _ _} _ _ {_}.
Arguments SelfSimulation {_ _} _ {_}.
Arguments SelfSimulation_Weak {_ _} _ {_}.
Arguments Termination_Sensitive {_ _} _ {_}.

Arguments SelfSimulation_All_Valid {_ _} _ {_}.
Arguments SelfSimulation_Weak_All_Valid {_ _} _ {_}.
Arguments Termination_Sensitive_All_Valid {_ _} _ {_}.

Arguments Simulation {_ _ _ _}.
Arguments SimulationForProgram {_ _ _ _} _ _ {_}.

Lemma SS_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    SelfSimulation
      u p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs ->
    
    SimulationForProgram R u p1_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    SimulationForProgram R u p2_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracles_exist_wrt R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp ->
    abstract_oracles_exist_wrt R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp ->
    
    oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    Termination_Sensitive u (compile R p1_abs)
    (compile R p2_abs) (compile R rec_abs)
    (refines_valid R valid_state_abs)
    (refines_related R equivalent_states_abs)
    l_get_reboot_state_imp ->
    
    SelfSimulation
      u (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
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


Lemma SS_compositional:
  forall O (L: Language O) u 
  T (p1 p2: L.(prog) T) T' (p3 p4: T -> L.(prog) T') 
      rec
      l_get_reboot_state3
      equivalent_states valid_state
      cond1 cond2,

    (forall l_get_reboot_state1,
    SelfSimulation
      u p1 p2
      rec
      valid_state
      equivalent_states
      cond1
      l_get_reboot_state1) ->

    (forall l_get_reboot_state2 t t',
    SelfSimulation
      u (p3 t) (p4 t')
      rec
      valid_state
      equivalent_states
      cond2
      l_get_reboot_state2) ->

      
      SelfSimulation
      u (Bind p1 p3) (Bind p2 p4)
      rec
      valid_state
      equivalent_states
      (fun u => cond1 u /\ cond2 u)
      l_get_reboot_state3.
Proof.

  unfold SelfSimulation;
  intros; simpl in *.
  repeat invert_exec.
  {
    invert_exec'' H13.
    
    edestruct H. 
    4: eauto.
    repeat econstructor; eauto.
    all: eauto.
    cleanup.
    simpl in *.
    invert_exec; simpl in *.
    
    edestruct H0. 
    4: eauto.
    eapply ExecFinished; eauto.
    all: eauto.
    cleanup.
    simpl in *.

    repeat invert_exec.
    exists (RFinished
    d'1 t1).
    intuition eauto.
    simpl in *.
    repeat econstructor; eauto.
  }
  {
    invert_exec'' H12.
    {
        edestruct H. 
        4: eauto.
        repeat econstructor; eauto.
        all: eauto.
        cleanup.
        simpl in *.
        invert_exec; simpl in *.

        edestruct H0. 
        4: eauto.
        eapply ExecRecovered; eauto.
        all: eauto.
        cleanup; simpl in *.

        repeat invert_exec.
        exists (Recovered (extract_state_r ret0)).
        intuition eauto.
        simpl in *.
        repeat econstructor; eauto.
    }
    {
      edestruct H. 
      4: eauto.
      eapply ExecRecovered; eauto.
      all: eauto.
      cleanup.
      simpl in *.
      repeat invert_exec.
        exists (Recovered (extract_state_r ret0)).
        intuition eauto.
        simpl in *.
        econstructor; eauto.
        eapply ExecBindCrash; eauto.
    }
  }
Qed.




(*** EXPERIMENTAL ***)

(** If you don't care about termination, then you don't need Termination_Sensitive **)
Lemma SSW_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    SelfSimulation_Weak
      u p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs ->
    
    SimulationForProgram R u p1_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    SimulationForProgram R u p2_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracles_exist_wrt R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp ->
    abstract_oracles_exist_wrt R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp ->
    
    oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->
    
    SelfSimulation_Weak
      u (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
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

  edestruct H; eauto.
  do 2 eexists; intuition eauto.
Qed.


Lemma SS_All_Valid_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      cond,

    SelfSimulation_All_Valid
      u p1_abs p2_abs
      rec_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs ->
    
    SimulationForProgram R u p1_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    SimulationForProgram R u p2_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracles_exist_wrt R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp ->
    abstract_oracles_exist_wrt R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp ->
    
    oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    Termination_Sensitive_All_Valid u (compile R p1_abs)
    (compile R p2_abs) (compile R rec_abs)
    (refines_related R equivalent_states_abs)
    l_get_reboot_state_imp ->
    
    SelfSimulation_All_Valid
      u (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  eapply Self_Simulation_Weak_to_Self_Simulation_All_Valid; eauto.
  unfold SelfSimulation_Weak_All_Valid; simpl; intros.

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
     H1: SelfSimulation_All_Valid _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (1:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  repeat match goal with
  | [H: recovery_exec L_abs _ _ _ _ p2_abs _ _,
     H0: recovery_exec L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply recovery_exec_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.



Lemma SSW_All_Valid_transfer:
  forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      cond,

    SelfSimulation_Weak_All_Valid
      u p1_abs p2_abs
      rec_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs ->
    
    SimulationForProgram R u p1_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    SimulationForProgram R u p2_abs rec_abs 
      l_get_reboot_state_imp
      l_get_reboot_state_abs ->

    abstract_oracles_exist_wrt R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp ->
    abstract_oracles_exist_wrt R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp ->
    
    oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->
    
    SelfSimulation_Weak_All_Valid
      u (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  unfold SelfSimulation_Weak_All_Valid; simpl; intros.

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

  edestruct H; eauto.
  intuition eauto.
Qed.



