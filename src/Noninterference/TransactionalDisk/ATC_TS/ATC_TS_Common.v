Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATC_Simulation ATC_AOE.
Require Import Not_Init HSS ATC_ORS.

Import FileDiskLayer.
Set Nested Proofs Allowed.


(* TODO: Move to framework *)
Lemma TS_explicit_and_inject:
forall u s1 s2 T (p1 p2: ATCLang.(prog) T) rec V 
(R1 R2: state ATCLang -> state ATCLang -> Prop) l_grs lo,
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
forall u T (p1 p2: ATCLang.(prog) T) rec V 
(R: state ATCLang -> state ATCLang -> Prop) l_grs,
  (forall lo s1 s2, Termination_Sensitive_explicit u lo s1 s2
p1 p2 rec V R l_grs) <->
Termination_Sensitive u
p1 p2 rec V R l_grs.
Proof.
  unfold Termination_Sensitive_explicit, Termination_Sensitive; intros.
  intuition; eauto.
Qed.

Lemma TS_eqv_impl:
forall u T (p1 p2: ATCLang.(prog) T) rec V 
(R1 R2: state ATCLang -> state ATCLang -> Prop) l_grs,
Termination_Sensitive u p1 p2 rec V R1 l_grs ->
(forall s1 s2, R2 s1 s2 -> R1 s1 s2) ->
Termination_Sensitive u
p1 p2 rec V R2 l_grs.
Proof.
  unfold Termination_Sensitive; intros.
  intuition; eauto.
Qed.

Lemma ATC_TS_recovery:
forall n u R,
Termination_Sensitive u
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover)
(Simulation.Definitions.compile
 ATC_Refinement
 File.recover)
 (Simulation.Definitions.compile
 ATC_Refinement
 File.recover)
(refines_valid ATC_Refinement
 AD_valid_state)
R
(ATC_reboot_list n).
Proof.
unfold Termination_Sensitive, ATC_reboot_list; induction n.
{
  simpl; intros.
  repeat invert_exec.
  unfold refines_related, AD_related_states, refines_valid in *;
  cleanup.
  Transparent File.recover.
  unfold File.recover in *; simpl in *.
  invert_exec'' H9; repeat invert_exec.
  invert_exec'' H8; repeat invert_exec.
  invert_exec'' H12; repeat invert_exec.
  eexists (RFinished _ _).
  repeat econstructor.
}
{
  intros.
  repeat invert_exec.
  simpl in *; cleanup; try tauto.
  invert_exec'' H12; repeat invert_exec.
  { (* Recover crashed*)
    invert_exec'' H8; repeat invert_exec.
    invert_exec'' H11; repeat invert_exec.
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
    rewrite cons_app.
    repeat econstructor.
    simpl; eauto.
  }
  shelve.
}
{ (*Delete crashed*)
  invert_exec'' H7; repeat invert_exec.
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
  shelve.
}
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: simpl; eauto.
Qed.


Lemma ATC_TS_compositional:
forall T (p1 p2: ATCLang.(prog) T) 
T' (p3 p4: T -> ATCLang.(prog) T') 
u n (R R': state ATCLang -> state ATCLang -> Prop),
(forall n,
Termination_Sensitive u p1 p2
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state) R
(ATC_reboot_list n)) ->

(forall n s1 s2 o s1' r1 s2' r2 ,
exec ATCLang u o s1 p1 (Finished s1' r1) ->
exec ATCLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive u (p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATC_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATC_Refinement
AD_valid_state)
R'
(ATC_reboot_list n)) ->
(forall s1 s2 o s1' r1 s2' r2 ,
exec ATCLang u o s1 p1 (Finished s1' r1) ->
exec ATCLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' s1' s2') ->
Termination_Sensitive u (Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATC_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATC_Refinement
AD_valid_state)
R
(ATC_reboot_list n).
Proof.
unfold Termination_Sensitive, ATC_reboot_list; 
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
edestruct ATC_TS_recovery.
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


Lemma ATC_TS_explicit_compositional:
forall T (p1 p2: ATCLang.(prog) T) 
T' (p3 p4: T -> ATCLang.(prog) T') 
u n (R R': state ATCLang -> state ATCLang -> Prop) lo s1 s2,
(forall n lo,
Termination_Sensitive_explicit u lo s1 s2 p1 p2
(Simulation.Definitions.compile
 ATC_Refinement
 (Simulation.Definitions.compile
    FD.refinement
    (| Recover |)))
(refines_valid ATC_Refinement
 AD_valid_state) R
(ATC_reboot_list n)) ->

(forall n lo s1 s2 o s1' r1 s2' r2 ,
exec ATCLang u o s1 p1 (Finished s1' r1) ->
exec ATCLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
Termination_Sensitive_explicit u lo s1' s2' (p3 r1) (p4 r2)
(Simulation.Definitions.compile
ATC_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATC_Refinement
AD_valid_state)
R'
(ATC_reboot_list n)) ->


(forall s1 s2 o s1' r1 s2' r2 ,
exec ATCLang u o s1 p1 (Finished s1' r1) ->
exec ATCLang u o s2 p2 (Finished s2' r2) ->
R s1 s2 ->
R' s1' s2') ->

Termination_Sensitive_explicit u lo s1 s2 
(Bind p1 p3) (Bind p2 p4)
(Simulation.Definitions.compile
ATC_Refinement
(Simulation.Definitions.compile
  FD.refinement
  (| Recover |)))
(refines_valid ATC_Refinement
AD_valid_state)
R
(ATC_reboot_list n).
Proof.
unfold Termination_Sensitive_explicit, ATC_reboot_list; 
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
edestruct ATC_TS_recovery.
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


Lemma ATC_TS_ret:
    forall n u T (t1 t2: T) V R,
    Termination_Sensitive u (Ret t1) (Ret t2)
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  V R
  (ATC_reboot_list n).
  Proof.
    unfold Termination_Sensitive, ATC_reboot_list; simpl; intros.
    destruct n; simpl in *;
    repeat invert_exec.
    invert_exec'' H9.
    eexists (RFinished _ _); repeat econstructor.

    invert_exec'' H12.
    edestruct ATC_TS_recovery; eauto.
    all: unfold AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    shelve.
    eexists (Recovered _); repeat econstructor; eauto.
    Unshelve.
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.

    

  Qed.