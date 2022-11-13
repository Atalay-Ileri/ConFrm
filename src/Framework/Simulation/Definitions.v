Require Import Lia Primitives Layer.

Record CoreRefinement {O_imp} (L_imp: Layer O_imp) (O_abs: Core) :=
  {
    compile_core : forall T, O_abs.(Core.operation) T -> L_imp.(prog) T;
    refines_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    refines_reboot_core: L_imp.(state) -> O_abs.(Core.state) -> Prop;
    token_refines: forall T, user -> L_imp.(state) -> O_abs.(Core.operation) T -> 
      (L_imp.(state) -> L_imp.(state)) -> L_imp.(oracle) -> O_abs.(Core.token) -> Prop;
    exec_compiled_preserves_refinement_finished_core :
      forall T (p2: O_abs.(Core.operation) T) o1 s1 s1' r u,
        (exists s2, refines_core s1 s2) ->
        L_imp.(exec) u o1 s1 (compile_core T p2) (Finished s1' r) ->
        (exists s2', refines_core s1' s2');
  }.

Record Refinement {O_imp O_abs} (L_imp: Layer O_imp) (L_abs: Layer O_abs) :=
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
  Variable L_imp: Layer O_imp.
  Variable L_abs: Layer O_abs.
  Variable R : Refinement L_imp L_abs.
  
  Fixpoint recovery_oracles_refine {T}
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
           recovery_oracles_refine u (get_reboot_state_imp s') rec_abs rec_abs lgrsi loi loa
         | _ => False
         end))
    | _, _ => False
    end.

Definition abstract_oracles_exist_wrt Rel (u: user) {T} (p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state :=
  forall l_oi si si',
    (exists sa: L_abs.(state), Rel si sa) -> 
    L_imp.(exec_with_recovery) u l_oi si l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) si' ->
    exists l_oa, recovery_oracles_refine u si p_abs rec_abs l_get_reboot_state l_oi l_oa.

Definition abstract_oracles_exist_wrt_explicit Rel (u: user) {T} (p_abs: L_abs.(prog) T) rec_abs l_get_reboot_state l_oi si si' :=
    (exists sa: L_abs.(state), Rel si sa) -> 
    L_imp.(exec_with_recovery) u l_oi si l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) si' ->
    exists l_oa, recovery_oracles_refine u si p_abs rec_abs l_get_reboot_state l_oi l_oa.
    

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
      L_imp.(exec_with_recovery) u l_oi s l_get_reboot_state (R.(compile) p_abs) (R.(compile) rec_abs) ret ->
      valid_state (extract_state_r ret).


Definition oracle_refines_same_from_related
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.

Definition oracle_refines_same_from_related_explicit
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) 
l_o_imp l_o_abs l_o_abs' s1_imp s2_imp :=
    refines_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.


Definition oracle_refines_same_from_related_reboot
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related_reboot related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.

Definition oracle_refines_same_from_related_test
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
            l_get_reboot_state_abs
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
(forall s1_abs ret1,
refines R s1_imp s1_abs -> 
L_abs.(exec_with_recovery) u l_o_abs s1_abs l_get_reboot_state_abs p1_abs rec_abs ret1 ->
L_abs.(exec_with_recovery) u l_o_abs' s1_abs l_get_reboot_state_abs p1_abs rec_abs ret1).


Definition oracle_refines_same_from_related_test2
            (u: user) {T} (p1_abs p2_abs: L_abs.(prog) T)
            rec_abs
            l_get_reboot_state_imp
           (related_states_abs: L_abs.(state) -> L_abs.(state) -> Prop) :=
  forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp,
    refines_related related_states_abs s1_imp s2_imp ->
    recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' ->
    (recovery_oracles_refine u s1_imp p1_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs' \/
    recovery_oracles_refine u s2_imp p2_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs) .

    (** RDNI **)
(**
  valid_state: This predicate restrict the statement to "well-formed" states.
  valid_op: This predicate restrict programs to valid ones
  R: This is the actual simulation relation
**)

Definition RDNI (u: user) {T} (p1 p2: L_abs.(prog) T)
       (rec: L_abs.(prog) unit)
       (valid_state: L_abs.(state) -> Prop)
       (R: L_abs.(state) -> L_abs.(state) -> Prop)
       (cond: user -> Prop)
       l_get_reboot_state :=
  forall lo s1 s1',
    L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
    valid_state s1 ->
    forall s2,
    valid_state s2 ->
    R s1 s2 ->
    exists s2',
      L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2' /\
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
    L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
    R s1 s2 ->
    exists s2', 
      L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2'.

Definition RDNI_Weak u {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           (cond: user -> Prop)
           l_get_reboot_state :=
  forall lo s1 s1' s2 s2',
    L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
    L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2' ->
    valid_state s1 ->
    valid_state s2 ->
    R s1 s2 ->
    R (extract_state_r s1') (extract_state_r s2') /\
    (cond u -> extract_ret_r s1' = extract_ret_r s2') /\
    valid_state (extract_state_r s1') /\
    valid_state (extract_state_r s2').

Lemma RDNI_Weak_to_RDNI:
  forall u T (p1 p2: L_abs.(prog) T) R
    valid_state rec cond l_get_reboot_state,

    Termination_Sensitive u p1 p2 rec valid_state R l_get_reboot_state ->
    RDNI_Weak u p1 p2 rec valid_state R cond l_get_reboot_state ->
    
    RDNI u p1 p2 rec valid_state R cond l_get_reboot_state.
Proof.
  unfold Termination_Sensitive, RDNI_Weak, RDNI; intros.
  edestruct H.
  3: eauto.
  all: eauto.
Qed.

Theorem RDNI_to_RDNIW:
forall u R V T (p1 p2: L_abs.(prog) T) rec cond l_grs,
 RDNI u p1 p2 rec V R cond l_grs ->
 RDNI_Weak u p1 p2 rec V R cond l_grs.
 Proof.
   unfold RDNI_Weak; intros.
   edestruct H; eauto.
   destruct H5.
   eapply exec_with_recovery_deterministic_wrt_reboot_state in H1; eauto.
   subst; eauto.
Qed.

Definition RDNI_explicit (u: user) lo s1 s2 {T} (p1 p2: L_abs.(prog) T)
       (rec: L_abs.(prog) unit)
       (valid_state: L_abs.(state) -> Prop)
       (R: L_abs.(state) -> L_abs.(state) -> Prop)
       (cond: user -> Prop)
       l_get_reboot_state :=
  forall s1',
    L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
    valid_state s1 ->
    valid_state s2 ->
    R s1 s2 ->
    exists s2',
      L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2' /\
      R (extract_state_r s1') (extract_state_r s2') /\
      (cond u -> extract_ret_r s1' = extract_ret_r s2') /\
      valid_state (extract_state_r s1') /\
      valid_state (extract_state_r s2').

Definition Termination_Sensitive_explicit u lo s1 s2 {T} (p1 p2: L_abs.(prog) T)
      (rec: L_abs.(prog) unit)
      (valid_state: L_abs.(state) -> Prop)
      (R: L_abs.(state) -> L_abs.(state) -> Prop)
      l_get_reboot_state :=
forall s1',
valid_state s1 ->
valid_state s2 -> 
L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
R s1 s2 ->
exists s2', 
 L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2'.

 Definition RDNI_Weak_explicit u lo s1 s2 {T} (p1 p2: L_abs.(prog) T)
           (rec: L_abs.(prog) unit)
           (valid_state: L_abs.(state) -> Prop)
           (R: L_abs.(state) -> L_abs.(state) -> Prop)
           (cond: user -> Prop)
           l_get_reboot_state :=
  forall s1' s2',
    L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state p1 rec s1' ->
    L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state p2 rec s2' ->
    valid_state s1 ->
    valid_state s2 ->
    R s1 s2 ->
    R (extract_state_r s1') (extract_state_r s2') /\
    (cond u -> extract_ret_r s1' = extract_ret_r s2') /\
    valid_state (extract_state_r s1') /\
    valid_state (extract_state_r s2').

Lemma RDNI_explicit_state_iff_RDNI:
  forall u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_abs
      (equivalent_states_abs : state L_abs -> state L_abs -> Prop)
      valid_state_abs
      cond,

    (forall lo s1 s2,
    equivalent_states_abs s1 s2 ->
    RDNI_explicit
      u lo s1 s2 
      p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs) <->

    RDNI
      u
      p1_abs p2_abs
      rec_abs
      valid_state_abs
      equivalent_states_abs
      cond
      l_get_reboot_state_abs.
Proof.
  unfold RDNI, RDNI_explicit; intros.
  intuition; try eapply H; eauto.
Qed.

Lemma RDNI_Weak_explicit_to_RDNI_explicit:
  forall u T (p1 p2: L_abs.(prog) T) R
    valid_state rec cond l_get_reboot_state lo s1 s2,

    Termination_Sensitive_explicit u lo s1 s2 p1 p2 rec valid_state R l_get_reboot_state ->
    RDNI_Weak_explicit u lo s1 s2 p1 p2 rec valid_state R cond l_get_reboot_state ->
    
    RDNI_explicit u lo s1 s2 p1 p2 rec valid_state R cond l_get_reboot_state.
Proof.
  unfold Termination_Sensitive_explicit, RDNI_Weak_explicit, RDNI_explicit; intros.
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
    recovery_oracles_refine u s_imp p_abs rec_abs l_get_reboot_state_imp l_o_imp l_o_abs ->
    R_begin s_imp s_abs ->

    (forall s_imp',
       L_imp.(exec_with_recovery) u l_o_imp s_imp
        l_get_reboot_state_imp (R.(compile) p_abs)
        (R.(compile) rec_abs) s_imp' ->
       exists s_abs',
         L_abs.(exec_with_recovery) u l_o_abs s_abs l_get_reboot_state_abs p_abs rec_abs s_abs' /\
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

Lemma RDNI_explicit_state_and_inject:
         forall u T (p1_abs p2_abs: L_abs.(prog) T)
             rec_abs
             l_get_reboot_state_abs
             (equivalent_states_abs1
             equivalent_states_abs2 : state L_abs -> state L_abs -> Prop)
             valid_state_abs
             cond lo s1 s2,

          ( equivalent_states_abs2 s1 s2 ->
           RDNI_explicit
             u lo s1 s2 
             p1_abs p2_abs
             rec_abs
             valid_state_abs
             (fun s1 s2 => equivalent_states_abs1 s1 s2)
             cond
             l_get_reboot_state_abs) ->

            (forall lo s1' s2',
            equivalent_states_abs2 s1 s2 ->
            L_abs.(exec_with_recovery) u lo s1 l_get_reboot_state_abs p1_abs rec_abs s1' ->
            L_abs.(exec_with_recovery) u lo s2 l_get_reboot_state_abs p2_abs rec_abs s2' ->
            equivalent_states_abs2 (extract_state_r s1') (extract_state_r s2')) ->

           RDNI_explicit
             u lo s1 s2
             p1_abs p2_abs
             rec_abs
             valid_state_abs
             (fun s1 s2 => equivalent_states_abs1 s1 s2 /\ equivalent_states_abs2 s1 s2)
             cond
             l_get_reboot_state_abs.
       Proof.
         unfold RDNI_explicit; intros.
         cleanup; edestruct H; eauto.
         cleanup.
         eexists; intuition eauto.
    Qed.

    Lemma RDNI_explicit_state_and_extract:
    forall u T (p1_abs p2_abs: L_abs.(prog) T)
        rec_abs
        l_get_reboot_state_abs
        (equivalent_states_abs1
        equivalent_states_abs2 : state L_abs -> state L_abs -> Prop)
        valid_state_abs
        cond lo s1 s2,

        RDNI_explicit
        u lo s1 s2
        p1_abs p2_abs
        rec_abs
        valid_state_abs
        (fun s1 s2 => equivalent_states_abs1 s1 s2 /\ equivalent_states_abs2 s1 s2)
        cond
        l_get_reboot_state_abs ->

        equivalent_states_abs2 s1 s2 ->

      RDNI_explicit
        u lo s1 s2 
        p1_abs p2_abs
        rec_abs
        valid_state_abs
        (fun s1 s2 => equivalent_states_abs1 s1 s2)
        cond
        l_get_reboot_state_abs.
  Proof.
    unfold RDNI_explicit; intros.
    cleanup; edestruct H; eauto.
    cleanup.
    eexists; intuition eauto.
Qed.


End Relations.

Arguments recovery_oracles_refine {_ _ _ _} _ {_}.
Arguments refines_related {_ _ _ _}.
Arguments refines_valid {_ _ _ _}.
Arguments exec_compiled_preserves_validity {_ _ _ _} _ {_}.
Arguments abstract_oracles_exist_wrt {_ _ _ _} _ _ _ {_}.
Arguments abstract_oracles_exist_wrt_explicit {_ _ _ _} _ _ _ {_}.
Arguments oracle_refines_same_from_related {_ _ _ _} _ _ {_}.
Arguments RDNI {_ _} _ {_}.
Arguments RDNI_Weak {_ _} _ {_}.
Arguments Termination_Sensitive {_ _} _ {_}.

Arguments RDNI_explicit {_ _} _ _ _ _ {_}.
Arguments RDNI_Weak_explicit {_ _} _ _ _ _ {_}.
Arguments Termination_Sensitive_explicit {_ _} _ _ _ _ {_}.

Arguments Simulation {_ _ _ _}.
Arguments SimulationForProgram {_ _ _ _} _ _ {_}.

Arguments oracle_refines_same_from_related_explicit {_ _ _ _} _ _ {_}.
Arguments oracle_refines_same_from_related_test2 {_ _ _ _} _ _ {_}.

(*
Lemma ORS_prefix_explicit_to_ORS_explicit:
forall O_imp O_abs (L_imp: Layer O_imp) 
(L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
u T (p1_abs p2_abs: L_abs.(prog) T)
  rec_abs
  l_get_reboot_state_imp
  l_get_reboot_state_abs
equivalent_states_abs 
  l_o_imp 
  l_o_abs1 l_o_abs2
  s1_imp s2_imp
  s1_abs s2_abs
  s1_abs' s2_abs',

(forall l_o_imp1 l_o_imp2,
oracle_refines_same_from_related_prefix_explicit R u
p1_abs
p2_abs
rec_abs
l_get_reboot_state_imp
equivalent_states_abs 
l_o_imp1 l_o_imp2
l_o_abs1 l_o_abs2 
s1_imp s2_imp) ->

(forall l_o_abs1 l_o_abs2 s1_abs s2_abs s1_abs' s2_abs',
(equivalent_states_abs s1_abs s2_abs ->
L_abs.(exec_with_recovery) u l_o_abs1 s1_abs l_get_reboot_state_abs p1_abs rec_abs s1_abs' ->
L_abs.(exec_with_recovery) u l_o_abs2 s2_abs l_get_reboot_state_abs p2_abs rec_abs s2_abs' ->
results_match_r s1_abs' s2_abs' ->
Forall2 (fun o_abs1 o_abs2 => exists oa1 oa2, o_abs1 ++ oa1 = o_abs2 ++ oa2) l_o_abs1 l_o_abs2->
l_o_abs1 = l_o_abs2)) ->

R.(refines) s1_imp s1_abs ->
R.(refines) s2_imp s2_abs ->
equivalent_states_abs s1_abs s2_abs ->
L_abs.(exec_with_recovery) u l_o_abs1 s1_abs l_get_reboot_state_abs p1_abs rec_abs s1_abs' ->
L_abs.(exec_with_recovery) u l_o_abs2 s2_abs l_get_reboot_state_abs p2_abs rec_abs s2_abs' ->
results_match_r s1_abs' s2_abs' ->

oracle_refines_same_from_related_explicit R u
p1_abs
p2_abs
rec_abs
l_get_reboot_state_imp
equivalent_states_abs
l_o_imp 
  l_o_abs1 l_o_abs2 
  s1_imp s2_imp.
Proof.
  unfold oracle_refines_same_from_related_explicit, 
  oracle_refines_same_from_related_prefix_explicit; intros.
  eapply_fresh H in H8; eauto.
  eapply forall_forall2; eauto.
  eapply Forall_forall; intros.
  apply in_combine_same in H10; cleanup; eauto.
  Unshelve.
  constructor.
Qed.
*)

Lemma RDNI_transfer_test2:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    RDNI
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

    oracle_refines_same_from_related_test2 R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

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
    
    RDNI
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
  eapply RDNI_Weak_to_RDNI; eauto.
  unfold RDNI_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related_test2 _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.

  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  split_ors.
  {
    match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p1_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ _ _ _,
     H1: RDNI _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p2_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply exec_with_recovery_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
  }
  {
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p1_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ _ _ _,
     H1: RDNI _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p2_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply exec_with_recovery_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
  }
Qed.


(*
Lemma ORS_to_ORST:
forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
u T (p1_abs p2_abs: L_abs.(prog) T)
  rec_abs
  l_get_reboot_state_imp
  l_get_reboot_state_abs
  equivalent_states_abs,
oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->
oracle_refines_same_from_related_test R u p1_abs p2_abs rec_abs l_get_reboot_state_imp l_get_reboot_state_abs equivalent_states_abs.
Proof.
  unfold oracle_refines_same_from_related, oracle_refines_same_from_related_test; intros.
  eapply H in H0; eauto.
  subst; eauto.
Qed.
*)

Lemma RDNI_transfer:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    RDNI
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
    
    RDNI
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
  eapply RDNI_Weak_to_RDNI; eauto.
  unfold RDNI_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p1_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ _ _ _,
     H1: RDNI _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p2_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply exec_with_recovery_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.

Lemma RDNI_compositional:
  forall O (L: Layer O) u 
  T (p1 p2: L.(prog) T) T' (p3 p4: T -> L.(prog) T') 
      rec
      l_get_reboot_state3
      equivalent_states valid_state
      cond1 cond2,

    (forall l_get_reboot_state1,
    RDNI
      u p1 p2
      rec
      valid_state
      equivalent_states
      cond1
      l_get_reboot_state1) ->

    (forall l_get_reboot_state2 t t',
    RDNI
      u (p3 t) (p4 t')
      rec
      valid_state
      equivalent_states
      cond2
      l_get_reboot_state2) ->

      
      RDNI
      u (Bind p1 p3) (Bind p2 p4)
      rec
      valid_state
      equivalent_states
      (fun u => cond1 u /\ cond2 u)
      l_get_reboot_state3.
Proof.

  unfold RDNI;
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




Lemma RDNI_explicit_transfer:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond l_o s1_imp s2_imp,

    RDNI
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

    (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp l_o s1_imp s_abs)->
    (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp l_o s2_imp s_abs)->
    
    oracle_refines_same_from_related R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    Termination_Sensitive_explicit u l_o s1_imp s2_imp
    (compile R p1_abs)
    (compile R p2_abs) (compile R rec_abs)
    (refines_valid R valid_state_abs)
    (refines_related R equivalent_states_abs)
    l_get_reboot_state_imp ->
    
    RDNI_explicit
      u l_o s1_imp s2_imp
      (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  eapply RDNI_Weak_explicit_to_RDNI_explicit; eauto.
  unfold RDNI_Weak_explicit; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  specialize (H2 s1').
  specialize (H3 s2').
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt_explicit _ _ _ ?p1 _ _ _ _ _,
     H2: abstract_oracles_exist_wrt_explicit _ _ _ ?p2 _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p1_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ _ _ _,
     H1: RDNI _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p2_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply exec_with_recovery_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.


Lemma RDNI_explicit_transfer_2:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond l_o s1_imp s2_imp,

    RDNI
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

    (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp l_o s1_imp s_abs)->
    (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp l_o s2_imp s_abs)->
    
    (forall l_o_abs1 l_o_abs2, oracle_refines_same_from_related_explicit R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs l_o l_o_abs1 l_o_abs2 s1_imp s2_imp) ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    Termination_Sensitive_explicit u l_o s1_imp s2_imp
    (compile R p1_abs)
    (compile R p2_abs) (compile R rec_abs)
    (refines_valid R valid_state_abs)
    (refines_related R equivalent_states_abs)
    l_get_reboot_state_imp ->
    
    RDNI_explicit
      u l_o s1_imp s2_imp
      (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  eapply RDNI_Weak_explicit_to_RDNI_explicit; eauto.
  unfold RDNI_Weak_explicit; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  specialize (H2 s1').
  specialize (H3 s2').
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt_explicit _ _ _ ?p1 _ _ _ _ _,
     H2: abstract_oracles_exist_wrt_explicit _ _ _ ?p2 _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: forall _ _, oracle_refines_same_from_related_explicit _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  (** Use self_simulation to generate second abs execution from s2 **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p1_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ _ _ _,
     H1: RDNI _ _ _ _ _ _ _ _,
     H2: equivalent_states_abs _ _ |- _ ] =>
    eapply_fresh H1 in H;    
    specialize Hx with (3:= H2); edestruct Hx;
    eauto; cleanup
  end.
  
  (** Show two executions are the same **)
  match goal with
  | [H: exec_with_recovery L_abs _ _ _ _ p2_abs _ _,
     H0: exec_with_recovery L_abs _ _ _ _ p2_abs _ _ |- _ ] =>
    eapply exec_with_recovery_deterministic_wrt_reboot_state in H;
    eauto; cleanup
  end.
  
  repeat (split; eauto).
Qed.


(** If you don't care about termination, then you don't need Termination_Sensitive **)
Lemma RDNIW_transfer:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    RDNI_Weak
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
    
    RDNI_Weak
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
  unfold RDNI_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  edestruct H; eauto.
  do 2 eexists; intuition eauto.
Qed.

Lemma RDNIW_transfer_test2:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond,

    RDNI_Weak
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
    
    oracle_refines_same_from_related_test2 R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->
    
    RDNI_Weak
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
  unfold RDNI_Weak; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: abstract_oracles_exist_wrt _ _ _ ?p1 _ _,
     H2: abstract_oracles_exist_wrt _ _ _ ?p2 _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: oracle_refines_same_from_related_test2 _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  split_ors.
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  edestruct H; eauto.
  do 2 eexists; intuition eauto.

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  edestruct H; eauto.
  do 2 eexists; intuition eauto.
Qed.

Lemma RDNIW_explicit_transfer:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      valid_state_abs
      cond lo s1 s2,

    RDNI_Weak
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

      (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp lo s1 s_abs)->
      (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp lo s2 s_abs)->
    
      (forall l_o_abs1 l_o_abs2, oracle_refines_same_from_related_explicit R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs lo l_o_abs1 l_o_abs2 s1 s2) ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->
    
    RDNI_Weak_explicit
      u lo s1 s2
      (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (refines_related R equivalent_states_abs)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  unfold RDNI_Weak_explicit; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: forall _, abstract_oracles_exist_wrt_explicit _ _ _ ?p1 _ _ _ _ _,
     H2: forall _, abstract_oracles_exist_wrt_explicit _ _ _ ?p2 _ _ _ _ _|- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: forall _ _, oracle_refines_same_from_related_explicit _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  edestruct H; eauto.
  do 2 eexists; intuition eauto.
Qed.


Lemma RDNIW_explicit_transfer_2:
  forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (R: Refinement L_imp L_abs)
    u T (p1_abs p2_abs: L_abs.(prog) T)
      rec_abs
      l_get_reboot_state_imp
      l_get_reboot_state_abs
      equivalent_states_abs
      (P: _ -> _ -> Prop)
      valid_state_abs
      cond lo s1 s2,

    RDNI_Weak
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

      (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p1_abs rec_abs l_get_reboot_state_imp lo s1 s_abs)->
      (forall s_abs, abstract_oracles_exist_wrt_explicit R R.(refines) u p2_abs rec_abs l_get_reboot_state_imp lo s2 s_abs)->
    
      (forall l_o_abs1 l_o_abs2, oracle_refines_same_from_related_explicit R u p1_abs p2_abs rec_abs l_get_reboot_state_imp equivalent_states_abs lo l_o_abs1 l_o_abs2 s1 s2) ->

    exec_compiled_preserves_validity R
    u p1_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    exec_compiled_preserves_validity R
    u p2_abs rec_abs l_get_reboot_state_imp
    (refines_valid R valid_state_abs) ->

    (forall s1' s2',
    refines_related R equivalent_states_abs s1 s2 -> 
    P s1 s2 -> 
    exec_with_recovery L_imp u lo s1 l_get_reboot_state_imp 
       (compile R p1_abs) (compile R rec_abs) s1' ->
    exec_with_recovery L_imp u lo s2 l_get_reboot_state_imp 
       (compile R p2_abs) (compile R rec_abs) s2' -> 
    P (extract_state_r s1') (extract_state_r s2')) ->
    
    RDNI_Weak_explicit
      u lo s1 s2
      (R.(compile) p1_abs)
      (R.(compile) p2_abs)
      (R.(compile) rec_abs)
      (refines_valid R valid_state_abs)
      (fun s1 s2 => refines_related R equivalent_states_abs s1 s2 /\ P s1 s2)
      cond
      l_get_reboot_state_imp.
Proof.

  intros.
  (** Convert to weak self_simulation **)
  unfold RDNI_Weak_explicit; simpl; intros.

  (** Construct abs oracles **)
  (* unfold refines_valid, refines_related in *; cleanup. *)

  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: forall _, abstract_oracles_exist_wrt_explicit _ _ _ ?p1 _ _ _ _ _,
     H2: forall _, abstract_oracles_exist_wrt_explicit _ _ _ ?p2 _ _ _ _ _|- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup;
    try solve [ unfold refines_valid, refines_related in *; cleanup; eauto]
  end.
  
  match goal with
  | [H: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H0: recovery_oracles_refine _ _ _ _ _ _ _ _,
     H1: forall _ _, oracle_refines_same_from_related_explicit _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] =>
    eapply_fresh H1 in H0; eauto; cleanup
  end.
  
  (** Construct abs executions **)
  unfold refines_related in *; cleanup.
  
  match goal with
  | [H: exec_with_recovery _ _ _ _ _ (compile _ ?p1) _ _,
     H0: exec_with_recovery _ _ _ _ _ (compile _ ?p2) _ _,
     H1: SimulationForProgram _ _ ?p1 _ _ _,
     H2: SimulationForProgram _ _ ?p2 _ _ _ |- _ ] =>
    eapply_fresh H1 in H; eauto; cleanup;
    eapply_fresh H2 in H0; eauto; cleanup
  end.
  simpl in *; cleanup.

  edestruct H; eauto.
  do 2 eexists; intuition eauto.
  eapply H7; eauto.
Qed.