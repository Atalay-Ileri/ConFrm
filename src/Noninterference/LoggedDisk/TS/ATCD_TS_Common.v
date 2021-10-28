Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer Not_Init HSS ATC_ORS ATC_Simulation ATC_AOE.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE ATCD_ORS.
Require Import ATCD_TS_BatchOperations ATCD_TS_Log ATCD_TS_LogCache.
Import FileDiskLayer.
Set Nested Proofs Allowed.


(* TODO: Move to framework *)
Lemma TS_explicit_and_inject:
forall u s1 s2 T (p1 p2: ATCDLang.(prog) T) rec V 
(R1 R2: state ATCDLang -> state ATCDLang -> Prop) l_grs,
R2 s1 s2 ->
Termination_Sensitive_explicit u s1 s2
p1 p2 rec V (fun s1 s2 => R1 s1 s2 /\ R2 s1 s2) l_grs ->
Termination_Sensitive_explicit u s1 s2
p1 p2 rec V R1 l_grs.
Proof.
  unfold Termination_Sensitive_explicit; intros.
  eapply H0; eauto.
Qed.

Lemma TS_explicit_to_TS:
forall u T (p1 p2: ATCDLang.(prog) T) rec V 
(R: state ATCDLang -> state ATCDLang -> Prop) l_grs,
  (forall s1 s2, Termination_Sensitive_explicit u s1 s2
p1 p2 rec V R l_grs) <->
Termination_Sensitive u
p1 p2 rec V R l_grs.
Proof.
  unfold Termination_Sensitive_explicit, Termination_Sensitive; intros.
  intuition; eauto.
Qed.

Lemma TS_eqv_impl:
forall u T (p1 p2: ATCDLang.(prog) T) rec V 
(R1 R2: state ATCDLang -> state ATCDLang -> Prop) l_grs,
Termination_Sensitive u p1 p2 rec V R1 l_grs ->
(forall s1 s2, R2 s1 s2 -> R1 s1 s2) ->
Termination_Sensitive u
p1 p2 rec V R2 l_grs.
Proof.
  unfold Termination_Sensitive; intros.
  intuition; eauto.
Qed.




Opaque LogCache.recover LogCache.init.
Lemma test_core:
forall u T (p: ATCCore.(operation) T) grs o o0 x s sa sa' r,
@HC_token_refines _ _ _ TCDLang ATCDLang TCD_CoreRefinement T u s o grs o0 x ->
Core.exec ATCCore u x sa o (Finished sa' r) ->
ATCD_CoreRefinement.(Simulation.Definitions.refines_core) s sa ->
exists s' r,
exec ATCDLang u o0 s (ATCD_CoreRefinement.(Simulation.Definitions.compile_core) o) (Finished s' r).
Proof.
  intros; destruct o; simpl in *; cleanup.
  {
    invert_exec.
    unfold HC_refines in *; cleanup.
    eexists; repeat econstructor; eauto.
    rewrite H; eauto.
  }
  {
    invert_exec.
    unfold HC_refines in *; cleanup.
    destruct o;  simpl in *; cleanup.
    {
      specialize (H3 tt); cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      repeat invert_exec;
      eexists; repeat econstructor; eauto.
      (* rewrite <- H0; econstructor; eauto. *)
    }
    {
      specialize (H3 tt); cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      specialize (H3 []); cleanup.
      repeat invert_exec; simpl in *.
      {
        split_ors; cleanup; try congruence;
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.
      }
      {
        split_ors; cleanup; try congruence;
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.
      }
      {
        repeat (repeat split_ors; cleanup; try congruence);
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.

      unfold Definitions.refines in *; cleanup.
      apply H3 in H1; cleanup; 
      split_ors; cleanup; try congruence.
    }
    {
      clear H8.
      repeat (repeat split_ors; cleanup; try congruence);
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.

      unfold Definitions.refines in *; cleanup.
      apply H3 in H1; cleanup; 
      split_ors; cleanup; try congruence.
    }
    {
        repeat (repeat split_ors; cleanup; try congruence);
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.
    }
    {
        repeat (repeat split_ors; cleanup; try congruence);
      unfold HC_transform_oracle in *;
      repeat cleanup_pairs;
      do 2 eexists; 
      repeat eapply lift2_exec_step; eauto.
    }
  }
}
Unshelve.
all: eauto.
Qed.


Lemma test:
forall u T (p: ATCLang.(prog) T) grs o oa s sa sa' r,
oracle_refines ATCDCore ATCCore ATCDLang ATCLang
   ATCD_CoreRefinement T u s p (ATCD_reboot_f grs) o oa ->
Language.exec' u oa sa p (Finished sa' r) ->
ATCD_Refinement.(Simulation.Definitions.refines) s sa ->
not_init p ->
exists s' r,
exec ATCDLang u o s (ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s' r).
Proof.
  induction p; simpl; intros.
  {
    clear H2.
    simpl in *; cleanup.
    invert_exec'' H0.
    eapply test_core in H2; eauto.
  }
  {
    invert_exec'' H0.
    split_ors; repeat invert_exec; cleanup; try congruence;
    eauto.
  }
  {
    invert_exec'' H1.
    split_ors; repeat invert_exec; cleanup; try congruence;
    eauto.

    eapply ATCD_exec_lift_crashed in H0; eauto.
    cleanup.
    exfalso; eapply finished_not_crashed_oracle_prefix.
    eauto.
    2: eauto.
    rewrite app_assoc; eauto.


    eapply_fresh ATCD_exec_lift_finished in H5; eauto.
    cleanup.
    eapply exec_finished_deterministic_prefix in H10; eauto; cleanup.
    destruct x5.
    eapply_fresh ATCD_exec_lift_finished in H6; eauto.
    cleanup.
    unify_execs; cleanup.
    do 2 eexists; repeat econstructor; eauto.

    eapply_fresh ATCD_exec_lift_crashed in H6; eauto.
    cleanup.
    unify_execs; cleanup.
  }
Unshelve.
eauto.
Qed.

(*
Lemma test3:
forall u T (p: ATCLang.(prog) T) grs o oa s1 s2 s1' sa1 sa2 sa1' sa2' r r1 r2,
oracle_refines ATCDCore ATCCore ATCDLang ATCLang
   ATCD_CoreRefinement T u s1 p grs o oa ->
Language.exec' u oa sa1 p (Finished sa1' r1) ->
Language.exec' u oa sa2 p (Finished sa2' r2) ->
exec ATCDLang u o s1 (ATCD_Refinement.(Simulation.Definitions.compile) p) (Finished s1' r) ->
ATCD_Refinement.(Simulation.Definitions.refines) s1 sa1 ->
ATCD_Refinement.(Simulation.Definitions.refines) s2 sa2 ->
not_init p ->
oracle_refines ATCDCore ATCCore ATCDLang ATCLang
   ATCD_CoreRefinement T u s2 p grs o oa.
Proof.
  induction p; simpl; intros.
  {
    clear H5.
    simpl in *; cleanup.
    invert_exec'' H0.
    invert_exec'' H1.
    destruct o.
    {
      simpl in *; cleanup; eauto.
    }
    {
      simpl in *; cleanup; eauto.
      specialize (H1 tt).
      destruct o.
      {
        simpl in *; cleanup; eauto.
        eexists; intuition eauto.
        do 2 eexists; intuition eauto.
      }
      {
        simpl in *; cleanup; eauto.
        specialize (H1 []).
        simpl in *; cleanup.
        eexists; intuition eauto.
        do 2 eexists; intuition eauto.
        do 2 eexists; intuition eauto.
        destruct o; simpl in *.
        {
          repeat invert_exec;
          repeat apply HC_map_ext_eq in H; subst.
          split_ors; cleanup; try congruence.
          left; do 2 eexists; intuition eauto.
          unfold LogCache.read in *; 
          cleanup; try lia; repeat invert_exec.
          repeat econstructor; eauto.
        }
      }
    }

    eapply test_core in H2; eauto.
  }
  {
    invert_exec'' H0.
    split_ors; repeat invert_exec; cleanup; try congruence;
    eauto.
  }
  {
    invert_exec'' H1.
    split_ors; repeat invert_exec; cleanup; try congruence;
    eauto.

    eapply ATCD_exec_lift_crashed in H0; eauto.
    cleanup.
    exfalso; eapply finished_not_crashed_oracle_prefix.
    eauto.
    2: eauto.
    rewrite app_assoc; eauto.
*)

Lemma ATCD_TS_recovery:
forall n u txns1 txns2 valid_part hdr1 hdr2,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
(Simulation.Definitions.compile
 ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
 (Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
(refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement
 AD_valid_state))
(fun s1 s2 => 
exists sa1 sa2,
(fst s1 = fst sa1 /\
 fst (snd s1) = fst (snd sa1) /\
 ((exists (hdr_blockset : set value) (log_blocksets : list (set value)),
 Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1
   txns1 hdr_blockset log_blocksets (snd (snd (snd s1))) /\
 (valid_part = Log.Old_Part ->
  Log.hash (Log.current_part hdr1) <>
  rolling_hash hash0
    (firstn (Log.count (Log.current_part hdr1))
       (map fst log_blocksets)))) /\
    snd (snd sa1) =
    total_mem_map fst
      (shift (Nat.add data_start)
         (list_upd_batch_set (snd (snd (snd (snd s1))))
            (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
    (forall a : nat,
     a >= data_start -> snd (snd (snd (snd (snd s1))) a) = [])) /\
 (forall (a : addr) (vs : value * list value),
  snd (snd (snd (snd s1))) a = vs -> snd vs = [])) /\
(fst s2 = fst sa2 /\
 fst (snd s2) = fst (snd sa2) /\
 ((exists (hdr_blockset : set value) (log_blocksets : list (set value)),
 Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2
   txns2 hdr_blockset log_blocksets (snd (snd (snd s2))) /\
 (valid_part = Log.Old_Part ->
  Log.hash (Log.current_part hdr2) <>
  rolling_hash hash0
    (firstn (Log.count (Log.current_part hdr2))
       (map fst log_blocksets)))) /\
    snd (snd sa2) =
    total_mem_map fst
      (shift (Nat.add data_start)
         (list_upd_batch_set (snd (snd (snd (snd s2))))
            (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
    (forall a : nat,
     a >= data_start -> snd (snd (snd (snd (snd s2))) a) = [])) /\
 (forall (a : addr) (vs : value * list value),
  snd (snd (snd (snd s2))) a = vs -> snd vs = [])) /\ 
length txns1 = length txns2 /\
(valid_part = Log.Old_Part ->
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2)) /\
Forall2
  (fun rec1 rec2 : Log.txn_record =>
   Log.start rec1 = Log.start rec2 /\
   Log.addr_count rec1 = Log.addr_count rec2 /\
   Log.data_count rec1 = Log.data_count rec2) (map Log.record txns1)
  (map Log.record txns2))
(ATCD_reboot_list n).
Proof.
unfold Termination_Sensitive, ATCD_reboot_list; induction n.
{
  simpl; intros.
  repeat invert_exec.
  unfold AD_related_states, refines_valid in *.
  cleanup.
  Transparent File.recover.
  unfold File.recover in *; simpl in *.
  invert_exec'' H9; repeat invert_exec.
  invert_exec'' H25; repeat invert_exec.
  eapply lift2_invert_exec in H28; cleanup.
  eapply lift2_invert_exec in H20; cleanup.
  simpl in *.

eapply LogCache_TS_recover in H21; cleanup.
eexists (RFinished _ _); repeat econstructor.
rewrite cons_app; repeat econstructor; eauto.
apply lift2_exec_step; eauto.
shelve.
apply lift2_exec_step; eauto.
intuition eauto.
intuition eauto.
all: eauto.
}
{
  Opaque LogCache.recover.
  intros.
  repeat invert_exec.
  simpl in *; cleanup; try tauto.
  invert_exec'' H12; repeat invert_exec.
  { (* Recover crashed*)
    invert_exec'' H26; repeat invert_exec.
    simpl in *.
    eapply lift2_invert_exec_crashed in H29; cleanup.
    eapply lift2_invert_exec_crashed in H21; cleanup.
    simpl in *.
    eapply_fresh LogCache_TS_recover_crashed in H22; try logic_clean.
    edestruct IHn. 
    3: eauto.

    unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.

    unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
  2: {
    eexists (Recovered _); econstructor.
    simpl in *.
    rewrite cons_app.
    econstructor.
    repeat econstructor.
    repeat apply lift2_exec_step_crashed; eauto.
    shelve.
    simpl; eauto.
  }
  simpl; shelve.
  simpl in *; intuition eauto.
  simpl in *; intuition eauto.
  all: eauto.
}
{ (*Delete crashed*)
  invert_exec'' H25; repeat invert_exec.
  simpl in *.
    edestruct IHn. 
    3: eauto.

    unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.

    unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.

  2: {
    eexists (Recovered _); econstructor.
    simpl in *.
    repeat econstructor.
    simpl; eauto.
  }
  simpl; shelve.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
all: try solve [exact ATCDLang].
all: admit. (* These are Log Cache crashed then reboot implies other stuff things *)
Admitted.


Lemma ATCD_TS_compositional:
forall T (p1 p2: ATCDLang.(prog) T) 
T' (p3 p4: T -> ATCDLang.(prog) T') 
u n (R R': state ATCDLang -> state ATCDLang -> Prop),
(forall n,
Termination_Sensitive u p1 p2
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATCD_Refinement
 AD_valid_state) R
(ATCD_reboot_list n)) ->

(forall n s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive u (p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATCD_Refinement
AD_valid_state)
R'
(ATCD_reboot_list n)) ->

(forall s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' s1' s2') ->
Termination_Sensitive u (Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATCD_Refinement
AD_valid_state)
R
(ATCD_reboot_list n).
Proof.
unfold Termination_Sensitive, ATCD_reboot_list; 
destruct n; intros; simpl in *.
{
repeat invert_exec.
invert_exec'' H12.
edestruct H.
4: eauto.
all: eauto.
instantiate (1 := RFinished _ _).
instantiate (3 := 0).
simpl.
econstructor; eauto.
eauto.
simpl in *; invert_exec.

edestruct H0.
3: eauto.
6: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := RFinished _ _).
instantiate (3 := 0).
simpl.
econstructor; eauto.
simpl in *; invert_exec.
eexists (RFinished _ _); repeat econstructor; eauto.
}
{
simpl in *; invert_exec.
edestruct ATCD_TS_recovery.
3: eauto.

all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

shelve.

invert_exec'' H15.
{
  edestruct H.
  4: eauto.
  all: eauto.
  instantiate (1 := RFinished _ _).
  instantiate (3 := 0).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  edestruct H0.
3: eauto.
6: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := Recovered _).
instantiate (2 := S n).
simpl.
econstructor; eauto.
simpl in *; invert_exec.

eexists (Recovered _); repeat econstructor; eauto.
}
{
  edestruct H.
  4: eauto.
  all: eauto.
  instantiate (1 := Recovered _).
  instantiate (2 := S n).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  eexists (Recovered _); repeat econstructor; eauto.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
Qed.


Lemma ATCD_TS_explicit_compositional:
forall T (p1 p2: ATCDLang.(prog) T) 
T' (p3 p4: T -> ATCDLang.(prog) T') 
u n (R R': state ATCDLang -> state ATCDLang -> Prop) s1 s2,
(forall n,
Termination_Sensitive_explicit u s1 s2 p1 p2
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATCD_Refinement
 AD_valid_state) R
(ATCD_reboot_list n)) ->

(forall n s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive_explicit u s1' s2' (p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATCD_Refinement
AD_valid_state)
R'
(ATCD_reboot_list n)) ->


(forall s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' s1' s2') ->

Termination_Sensitive_explicit u s1 s2 
(Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATCD_Refinement
AD_valid_state)
R
(ATCD_reboot_list n).
Proof.
unfold Termination_Sensitive_explicit, ATCD_reboot_list; 
destruct n; intros; simpl in *.
{
repeat invert_exec.
invert_exec'' H12.
edestruct H.
4: eauto.
all: eauto.
instantiate (1 := RFinished _ _).
instantiate (3 := 0).
simpl.
econstructor; eauto.
eauto.
simpl in *; invert_exec.

edestruct H0.
3: eauto.
6: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := RFinished _ _).
instantiate (3 := 0).
simpl.
econstructor; eauto.
simpl in *; invert_exec.
eexists (RFinished _ _); repeat econstructor; eauto.
}
{
simpl in *; invert_exec.
edestruct ATCD_TS_recovery.
3: eauto.

all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

shelve.

invert_exec'' H15.
{
  edestruct H.
  4: eauto.
  all: eauto.
  instantiate (1 := RFinished _ _).
  instantiate (3 := 0).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  edestruct H0.
3: eauto.
6: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := Recovered _).
instantiate (2 := S n).
simpl.
econstructor; eauto.
simpl in *; invert_exec.

eexists (Recovered _); repeat econstructor; eauto.
}
{
  edestruct H.
  4: eauto.
  all: eauto.
  instantiate (1 := Recovered _).
  instantiate (2 := S n).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  eexists (Recovered _); repeat econstructor; eauto.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
Qed.


Lemma ATCD_TS_ret:
    forall n u T (t1 t2: T) V R,
    Termination_Sensitive u (Ret t1) (Ret t2)
  (Simulation.Definitions.compile
     ATCD_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  V R
  (ATCD_reboot_list n).
  Proof.
    unfold Termination_Sensitive, ATCD_reboot_list; simpl; intros.
    destruct n; simpl in *;
    repeat invert_exec.
    invert_exec'' H9.
    eexists (RFinished _ _); repeat econstructor.

    invert_exec'' H12.
    edestruct ATCD_TS_recovery; eauto.
    all: unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    shelve.
    eexists (Recovered _); repeat econstructor; eauto.
    Unshelve.
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.

    

  Qed.