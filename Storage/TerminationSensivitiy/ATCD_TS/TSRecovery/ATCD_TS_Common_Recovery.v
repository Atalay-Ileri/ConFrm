Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer Not_Init HSS ATC_ORS ATC_Simulation ATC_AOE.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE ATCD_ORS.
Require Import ATCD_TS_BatchOperations_Recovery ATCD_TS_Log_Recovery.
Require Import ATCD_TS_LogCache_Recovery ATC_TS.
Import FileDiskLayer.
Set Nested Proofs Allowed.


(* TODO: Move to framework *)
Lemma TS_explicit_and_inject:
forall u lo s1 s2 T (p1 p2: ATCDLang.(prog) T) rec V 
(R1 R2: state ATCDLang -> state ATCDLang -> Prop) l_grs,
R2 s1 s2 ->
Termination_Sensitive_explicit u lo s1 s2
p1 p2 rec V (fun s1 s2 => R1 s1 s2 /\ R2 s1 s2) l_grs ->
Termination_Sensitive_explicit u lo s1 s2
p1 p2 rec V R1 l_grs.
Proof.
  unfold Termination_Sensitive_explicit; intros.
  eapply H0; eauto.
Qed.

Lemma TS_explicit_to_TS:
forall u T (p1 p2: ATCDLang.(prog) T) rec V 
(R: state ATCDLang -> state ATCDLang -> Prop) l_grs,
  (forall lo s1 s2, Termination_Sensitive_explicit u lo s1 s2
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

Lemma TS_explicit_eqv_impl:
forall u T (p1 p2: ATCDLang.(prog) T) rec V 
(R1 R2: state ATCDLang -> state ATCDLang -> Prop) l_grs lo s1 s2,
Termination_Sensitive_explicit u lo s1 s2 p1 p2 rec V R1 l_grs ->
(forall s1 s2, R2 s1 s2 -> R1 s1 s2) ->
Termination_Sensitive_explicit u lo s1 s2
p1 p2 rec V R2 l_grs.
Proof.
  unfold Termination_Sensitive_explicit; intros.
  intuition; eauto.
Qed.


Lemma ATCD_TS_transfer:
forall u T (p1 p2: ATCLang.(prog) T) V 
(R1: state ATCLang -> state ATCLang -> Prop) 
(R2: state ATCDLang -> state ATCDLang -> Prop) l_grs lo s1 s2,
Termination_Sensitive u p1 p2 (Simulation.Definitions.compile ATC_Refinement
File.recover) V R1 (ATC_reboot_list (length l_grs)) ->

not_init p1 ->
not_init p2 ->

(forall lo s1 s2 x0 x1 x3,
recovery_oracles_refine_to ATCD_Refinement u s1 p1
(Simulation.Definitions.compile ATC_Refinement File.recover)
(ATCD_reboot_list l_grs) lo x1 -> 
recovery_exec ATCLang u x1 x0 (ATC_reboot_list (length l_grs))
  p2 (Simulation.Definitions.compile ATC_Refinement File.recover) x3 ->
Simulation.Definitions.refines ATCD_Refinement s2 x0 ->
exists s2' : Recovery_Result,
  recovery_exec ATCDLang u lo s2 (ATCD_reboot_list l_grs)
    (Simulation.Definitions.compile ATCD_Refinement p2)
    (Simulation.Definitions.compile ATCD_Refinement
       (Simulation.Definitions.compile ATC_Refinement File.recover))
    s2') ->

non_colliding_selector_list u
    (Simulation.Definitions.refines ATCD_Refinement)
    (Simulation.Definitions.refines_reboot ATCD_Refinement) l_grs
    (Simulation.Definitions.compile ATCD_Refinement p1)
    (Simulation.Definitions.compile ATCD_Refinement
       (Simulation.Definitions.compile ATC_Refinement File.recover))
    lo s1 ->

Termination_Sensitive_explicit u lo s1 s2
(Simulation.Definitions.compile
 ATCD_Refinement p1) 
 (Simulation.Definitions.compile
 ATCD_Refinement p2)
 (Simulation.Definitions.compile
 ATCD_Refinement 
 (Simulation.Definitions.compile ATC_Refinement
 File.recover))
 (refines_valid ATCD_Refinement V) 
 (refines_related ATCD_Refinement R1)
 (ATCD_reboot_list l_grs).
Proof.
  unfold Termination_Sensitive_explicit; intros.
  unfold refines_related in *; cleanup.
  edestruct ATCD_AOE. 
  4: eauto. 
  all: eauto.
  
  edestruct ATCD_simulation. 
  2: eauto.
  all: eauto.
  cleanup.
  edestruct H.
  4: eauto.
  all: eauto.
Qed.



Opaque LogCache.recover LogCache.init.

Definition equivalent_for_recovery txns1 txns2 valid_part hdr1 hdr2 :=  
  (fun (s1 s2: state ATCDLang) => 
exists (sa1 sa2: state ATCLang),
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
Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2) /\
Forall2
  (fun rec1 rec2 : Log.txn_record =>
   Log.start rec1 = Log.start rec2 /\
   Log.addr_count rec1 = Log.addr_count rec2 /\
   Log.data_count rec1 = Log.data_count rec2) (map Log.record txns1)
  (map Log.record txns2)).

  Lemma equivalent_for_recovery_after_reboot :
  forall txns1 txns2 hdr1 hdr2 s1 s2 t,
  equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2 s1 s2 ->
  equivalent_for_recovery txns1 txns2 
  Log.Current_Part hdr1 hdr2
     (fst s1,
     ([],
     (empty_mem,
     (fst (snd (snd (snd s1))),
     select_total_mem t (snd (snd (snd (snd s1))))))))
     (fst s2,
     ([],
     (empty_mem,
     (fst (snd (snd (snd s2))),
     select_total_mem t (snd (snd (snd (snd s2)))))))).
Proof.
intros.
unfold equivalent_for_recovery in *; 
simpl in *; logic_clean.
eapply RepImplications.log_rep_explicit_after_reboot in H5.
eapply RepImplications.log_rep_explicit_after_reboot in H11.


  eexists (_, (_, _)), (_, (_, _)).
 simpl; repeat split.
 do 2 eexists; intuition eauto; try congruence.
 eapply select_total_mem_synced.
 do 2 eexists; intuition eauto; try congruence.
 eapply select_total_mem_synced.
 all: eauto.
Qed.


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
(equivalent_for_recovery txns1 txns2 valid_part hdr1 hdr2)
(ATCD_reboot_list n).
Proof.
unfold equivalent_for_recovery, Termination_Sensitive, ATCD_reboot_list; induction n.
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
rewrite H4 in *; intuition eauto.
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
  simpl in *; rewrite H4 in *; intuition eauto.
  simpl in *; intuition eauto.
  simpl in *; eauto.
  intros; eauto.
  eauto.
  }
  {
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