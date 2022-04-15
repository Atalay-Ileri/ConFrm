Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer Not_Init HSS ATC_ORS ATC_Simulation ATC_AOE.
Require Import ATCDLayer FileDisk.TransferProofs ATCD_Simulation ATCD_AOE ATCD_ORS.
Require Import ATCD_TS_Recovery.
Import FileDiskLayer.
Set Nested Proofs Allowed.

Ltac invert_lift2:=
match goal with
|[H: exec _ _ _ _ (lift_L2 _ _) (Finished _ _) |- _] =>
eapply lift2_invert_exec in H; try logic_clean
|[H: exec _ _ _ _ (lift_L2 _ _) (Crashed _) |- _] =>
eapply lift2_invert_exec_crashed in H; try logic_clean
|[H: Language.exec' _ _ _ (lift_L2 _ _) (Finished _ _) |- _] =>
eapply lift2_invert_exec in H; try logic_clean
|[H: Language.exec' _ _ _ (lift_L2 _ _) (Crashed _) |- _] =>
eapply lift2_invert_exec_crashed in H; try logic_clean
end.


Lemma ATCD_TS_compositional:
forall T (p1 p2: ATCDLang.(prog) T) 
T' (p3 p4: T -> ATCDLang.(prog) T') 
u n (R : state ATCDLang -> state ATCDLang -> Prop)
(R': T -> T -> state ATCDLang -> state ATCDLang -> Prop),
(forall n,
Termination_Sensitive u p1 p2
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
 (refines_valid ATCD_Refinement
 (refines_valid ATC_Refinement
AD_valid_state)) 
R
(ATCD_reboot_list n)) ->

(forall n s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive u (p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement
 AD_valid_state))
(R' r1 r2)
(ATCD_reboot_list n)) ->

(forall s1 s2 o s1' r1 s2' r2 ,
exec ATCDLang u o s1 p1 (Finished s1' r1) ->
exec ATCDLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' r1 r2 s1' s2') ->
Termination_Sensitive u (Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
 (refines_valid ATCD_Refinement
 (refines_valid ATC_Refinement
AD_valid_state))
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
instantiate (3 := []).
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
instantiate (3 := []).
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
  instantiate (3 := []).
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
instantiate (2 := t::n).
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
  instantiate (2 := t::n).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  eexists (Recovered _); repeat econstructor; eauto.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
all: try solve [exact []].
all: try solve [exact Log.header0].
all: try solve [exact Log.Current_Part].
all: admit. (* These are Log Cache crashed then reboot implies other stuff things *)
Admitted.


Lemma ATCD_TS_explicit_compositional:
forall T (p1 p2: ATCDLang.(prog) T) 
T' (p3 p4: T -> ATCDLang.(prog) T') 
u n (R : state ATCDLang -> state ATCDLang -> Prop)
(R': T -> T -> state ATCDLang -> state ATCDLang -> Prop) s1 s2 lo,
(forall n o1 o2 lo1,
seln lo 0 [] = o1 ++ o2 ->
Termination_Sensitive_explicit u (o1::lo1) s1 s2 p1 p2
(Simulation.Definitions.compile
 ATCD_Refinement
 (Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
 (refines_valid ATCD_Refinement
 (refines_valid ATC_Refinement
AD_valid_state)) 
R
(ATCD_reboot_list n)) ->

(forall n s1' r1 s2' r2 o1 o2 lo2,
seln lo 0 [] = o1 ++ o2 ->
exec ATCDLang u o1 s1 p1 (Finished s1' r1) ->
exec ATCDLang u o1 s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive_explicit u (o2 :: lo2) s1' s2'
(p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
  (refines_valid ATCD_Refinement
  (refines_valid ATC_Refinement
 AD_valid_state))
(R' r1 r2)
(ATCD_reboot_list n)) ->

(forall s1' r1 s2' r2 o1 o2,
seln lo 0 [] = o1 ++ o2 ->
exec ATCDLang u o1 s1 p1 (Finished s1' r1) ->
exec ATCDLang u o1 s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' r1 r2 s1' s2') ->

Termination_Sensitive_explicit u lo s1 s2
(Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATCD_Refinement
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover))
 (refines_valid ATCD_Refinement
 (refines_valid ATC_Refinement
AD_valid_state))
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
all: simpl; eauto.
instantiate (1 := RFinished _ _).
instantiate (3 := []).
simpl.
econstructor; eauto.

eauto.
simpl in *; invert_exec.

edestruct H0; cleanup.
4: eauto.
7: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := RFinished _ _).
instantiate (3 := []).
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
  all: simpl; eauto.
  instantiate (1 := RFinished _ _).
  instantiate (3 := []).
  simpl.
  econstructor; eauto.
  simpl in *; invert_exec.
  edestruct H0.
4: eauto.
7: eauto.
all: eauto.
all: unfold refines_valid, AD_valid_state; simpl;
     unfold refines_valid, FD_valid_state; simpl; eauto.

instantiate (1 := Recovered _).
instantiate (2 := t::n).
simpl.
econstructor; eauto.
simpl in *; invert_exec.

eexists (Recovered _); repeat econstructor; eauto.
}
{
  edestruct H.
  4: eauto.
  all: simpl; eauto.
  rewrite app_nil_r; eauto.

  instantiate (1 := Recovered _).
  instantiate (2 := t::n).
  simpl.
  econstructor; eauto.
  
  simpl in *; invert_exec.
  eexists (Recovered _); repeat econstructor; eauto.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
all: try solve [exact []].
all: try solve [exact Log.header0].
all: try solve [exact Log.Current_Part].
all: admit. (* These are Log Cache crashed then reboot implies other stuff things *)
Admitted.


Lemma ATCD_TS_ret:
    forall n u T (t1 t2: T) V txns1 txns2 hdr1 hdr2,
    Termination_Sensitive u (Ret t1) (Ret t2)
    (Simulation.Definitions.compile
    ATCD_Refinement
    (Simulation.Definitions.compile
     ATC_Refinement
     File.recover))
  V (equivalent_for_recovery txns1 txns2 Log.Current_Part hdr1 hdr2)
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
    eapply equivalent_for_recovery_after_reboot; eauto.
    eexists (Recovered _); repeat econstructor; eauto.
  Qed.