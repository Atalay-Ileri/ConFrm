Require Import List BaseTypes Memx Disk Prog ProgAuto.
Require Import Eqdep.
Require Import Simulation Confidentiality.
Import ListNotations.

Set Implicit Arguments.

Section ProgLTS.

Definition state := (user * oracle * disk * store)%type.

Inductive exec_lts :
    forall T, state -> prog T -> @Result state T -> Prop :=
  | ExecFinished : 
      forall T (p: prog T) u o o' d d' s s' r tr,
        exec u o d s p (Finished o' d' s' r) tr ->
        trace_ok tr ->
        exec_lts (u, o, d, s) p (Finish (u, o', d', s') r)
  | ExecCrashed : 
      forall T (p: prog T) u o o' d d' s s' tr,
        exec u o d s p (Crashed _ o' d' s') tr ->
        trace_ok tr ->
        exec_lts (u, o, d, s) p (Crash (u, o', d', s')).

 Theorem exec_to_exec_lts:
   forall T (p: prog T) u o d s ret tr,
     exec u o d s p ret tr ->
     trace_ok tr ->
     exists ret',
       exec_lts (u, o, d, s) p ret' /\
       (exists o' d' s',
           (exists r, ret = Finished o' d' s' r /\ ret' = Finish (u, o', d', s') r) \/
           (ret = Crashed _ o' d' s' /\ ret' = Crash (u, o', d', s'))).
 Proof.
   intros.
   destruct ret.
   eexists; split.
   econstructor; eauto.
   do 3 eexists; left; eauto.

   eexists; split.
   eapply ExecCrashed; eauto.
   do 3 eexists; right; eauto.
 Qed.

 Theorem exec_lts_to_exec:
   forall T (p: prog T) u o d s ret,
     exec_lts (u, o, d, s) p ret ->
     exists ret' tr,
       exec u o d s p ret' tr /\
       trace_ok tr /\
       (exists o' d' s',
           (exists r, ret' = Finished o' d' s' r /\ ret = Finish (u, o', d', s') r) \/
           (ret' = Crashed _ o' d' s' /\ ret = Crash (u, o', d', s'))).
 Proof.
   intros.
   inv_exec'' H;
     do 2 eexists; split; eauto.
   split; eauto.
   do 3 eexists; left; eauto.
   split; eauto.
   do 3 eexists; right; eauto.
 Qed.

Definition prog_LTS := {| State:= state; Op:= prog; transition := exec_lts |}.


Definition state_equivalent (st1 st2: state) :=
  let '(u1, o1, d1, s1) := st1 in
  let '(u2, o2, d2, s2) := st2 in
  u1 = u2 /\
  o1 = o2 /\
  equivalent_for u1 d1 d2 /\
  equivalent_for_store u1 s1 s2.

Lemma exec_lts_preserves_equivalence:
  forall T (p: prog T) st1 st2 st1',
    exec_lts st1 p st1' ->
    state_equivalent st1 st2 ->
    exists st2', exec_lts st2 p st2' /\
    state_equivalent (extract_state st1') (extract_state st2') /\
    (forall def, extract_ret def st1' = extract_ret def st2').
Proof.
  unfold state_equivalent; intros.
  cleanup.
  inv_exec'' H;
  eapply trace_ok_to_ret_noninterference in H5;
  edestruct H5; eauto; cleanup;
    destruct H0; cleanup.
  
  eexists; split; eauto.
  econstructor; eauto.
  simpl in *; eauto.
  
  eexists; split; eauto.
  eapply ExecCrashed; eauto.
  simpl in *; eauto.
Qed.

Definition state_equivalence_self_simulation : 
  SelfSimulation prog_LTS state_equivalent.
  intros; constructor; intros.
  simpl in *; eapply exec_lts_preserves_equivalence; eauto.
Defined.

Definition relational_noninterference {lts T} (p: Op lts T) (R: State lts -> State lts -> Prop):=
  forall st1 st1' st2,
    (transition _) _ st1 p st1' ->
    R st1 st2 ->
    exists st2',
      (transition _) _ st2 p st2' /\
      R (extract_state st1') (extract_state st2') /\
      (forall def, extract_ret def st1' = extract_ret def st2').

Theorem equivalence_to_noninterference:
  forall lts eq,
    SelfSimulation lts eq ->
    (forall T (p: Op lts T), relational_noninterference p eq).
Proof.
  unfold relational_noninterference; intros.
  inversion H; clear H.
  specialize self_simulation_correct with (1:= H0)(2:=H1).
  cleanup.
  eexists; intuition eauto.
Qed.

End ProgLTS.

