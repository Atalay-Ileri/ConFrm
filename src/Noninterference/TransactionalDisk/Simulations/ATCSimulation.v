Require Import Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer. (** TransferProofs. *)
Require Import TransactionalDiskRefinement.
Require Import Coq.Program.Equality.
Require Import Eqdep.

Set Nested Proofs Allowed.

Fixpoint not_init {T} (p: AD.(prog) T) :=
  match p with
  | Op _ o =>
    match o with
    | P1 _ => True
    | P2 o =>
    (forall l, ~eq_dep Type (operation Definitions.abs_op) _ o 
    unit (TransactionalDiskLayer.Init l))
    end
  | Ret _ => True
  | Bind p1 p2 =>
  not_init p1 /\ forall t, not_init (p2 t)
  end.


Lemma HC_exec_same_finished:
  forall u T (p: AD.(prog) T) 
  o o0 s_imp s_abs x x0,
  not_init p ->
  Language.exec' u o s_imp
 (ATC_Refinement.(Simulation.Definitions.compile) p)
 (Finished x x0) ->

 oracle_refines _ _ _ _ ATC_CoreRefinement T u s_imp
 p (fun
 s : HorizontalComposition.state' AuthenticationOperation
       TransactionCacheOperation => (fst s, ([], snd (snd s)))) o o0 ->

 ATC_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->

  (forall u s_imp s_abs T o x x0 x2 x3 x4,
  exec Definitions.imp u x3 s_imp
 (compile T o) (Finished x x0) ->
 token_refines T u s_imp o x4 x3 x2 ->
 refines s_imp s_abs ->
 (forall l, ~eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
exists s_abs',
TransactionalDiskLayer.exec' data_length u x2
  s_abs o (Finished s_abs' x0) /\
refines x s_abs') ->
 exists s_abs' : Recovery_Result,
  recovery_exec AD u [o0] s_abs
    (authenticated_disk_reboot_list 0) p
    File.recover s_abs' /\
    ATC_Refinement.(Simulation.Definitions.refines) x
    (extract_state_r s_abs') /\
  Some x0 = extract_ret_r s_abs'.
Proof.
  induction p; simpl; intros.
  {
    cleanup; simpl in *.
    {
      invert_exec'' H0.
      invert_exec.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold authenticated_disk_reboot_list; simpl.
      eexists (RFinished _ _); split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
    }
    {
      eapply lift2_invert_exec in H0; cleanup.
      apply HC_oracle_transformation_id in h; subst.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold authenticated_disk_reboot_list; simpl.
      eapply_fresh H3 in H4; eauto; cleanup.
      eexists (RFinished _ _); split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
    }
  }
  {
    cleanup; simpl in *.
    split_ors; cleanup; repeat unify_execs; cleanup.
    invert_exec'' H0.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold authenticated_disk_reboot_list; simpl.
    eexists (RFinished _ _); split.
    repeat econstructor; eauto.
    simpl; intuition eauto.
  }
  {
    cleanup; simpl in *.
    invert_exec'' H1.
    split_ors; cleanup; simpl in *;
    repeat unify_execs; cleanup.
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H12.
      apply H12; eauto.
      setoid_rewrite app_nil_r at 2; eauto.
    }
    {
      eapply exec_finished_deterministic_prefix in H6; eauto; cleanup.
      repeat unify_execs; cleanup.

      edestruct IHp; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      edestruct H; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      eexists (RFinished _ _); split; eauto.
      repeat econstructor; eauto.
      simpl; eauto.
    }
  }
Qed.


Lemma HC_exec_same_crashed:
  forall u T (p: AD.(prog) T) 
  o o0 s_imp s_abs x,
  not_init p ->
  Language.exec' u o s_imp
 (ATC_Refinement.(Simulation.Definitions.compile) p)
 (Crashed x) ->

 oracle_refines _ _ _ _ ATC_CoreRefinement T u s_imp
 p
 (fun s : HorizontalComposition.state'
          AuthenticationOperation
          TransactionCacheOperation => (fst s,
          ([], snd (snd s)))) o o0 ->

 ATC_Refinement.(Simulation.Definitions.refines) s_imp s_abs -> 

  (forall u s_imp s_abs T o x x2 x3 x4,
      exec Definitions.imp u x3 s_imp
    (compile T o) (Crashed x) ->
    token_refines T u s_imp o x4 x3 x2 ->
    refines s_imp s_abs ->
    (forall l, ~eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
    exists s_abs',
    TransactionalDiskLayer.exec' data_length u x2
      s_abs o (Crashed s_abs') /\
    refines_reboot x s_abs') ->

    (forall u s_imp s_abs T o x x0 x2 x3 x4,
    exec Definitions.imp u x3 s_imp
   (compile T o) (Finished x x0) ->
   token_refines T u s_imp o x4 x3 x2 ->
   refines s_imp s_abs ->
   (forall l, ~eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
  exists s_abs',
  TransactionalDiskLayer.exec' data_length u x2
    s_abs o (Finished s_abs' x0) /\
  refines x s_abs') ->

  (*
  (forall T o2 u s_imp x x1 x2 x3 x4 x5 x6 x7,
    @HC_oracle_transformation AuthenticationOperation _ TransactionCacheLang ATCLang x5 x4 ->
    minimal_oracle (compile T o2) u s_imp x4 ->
    token_refines T u s_imp o2 x7 x4 x3 ->
    x5 ++ x6 =
     map
       (fun o : Language.token' TransactionCacheOperation =>
        match o with
        | OpToken _ o1 =>
            OpToken
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
              (Token2 AuthenticationOperation TransactionCacheOperation o1)
        | Language.Crash _ =>
            Language.Crash
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        | Language.Cont _ =>
            Language.Cont
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        end) x2 ++ x1 ->
        exec Definitions.imp u x2 s_imp (compile T o2) (Crashed x) ->
    token_refines T u s_imp o2 x7 x2 x3) -> 
    *)

 exists s_abs',
 Language.exec' u o0 s_abs p (Crashed s_abs') /\
  refines_reboot (snd x) (snd s_abs').
Proof.
  induction p; simpl; intros.
  {
    cleanup; simpl in *.
    {
      invert_exec'' H0.
      invert_exec.
      unfold HC_refines in *; simpl in *; cleanup.
      eexists; split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
      unfold refines, refines_reboot,
      Transaction.transaction_rep,
      Transaction.transaction_reboot_rep in *;
      cleanup; eauto.
    }
    {
      eapply lift2_invert_exec_crashed in H0; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      apply HC_oracle_transformation_id in h; cleanup.
      unfold authenticated_disk_reboot_list; simpl.
      eapply H3 in H5; eauto; cleanup.
      eexists; split.
      repeat econstructor; eauto.
      simpl; intuition eauto.
    }
  }
  {
    cleanup; simpl in *.
    split_ors; cleanup; repeat unify_execs; cleanup.
    invert_exec'' H0.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold authenticated_disk_reboot_list; simpl.
    eexists; split.
    repeat econstructor; eauto.
    simpl; intuition eauto.
    unfold refines, refines_reboot,
      Transaction.transaction_rep,
      Transaction.transaction_reboot_rep in *;
      cleanup; eauto.
  }
  {
    cleanup; simpl in *.
    invert_exec'' H1.
    split_ors; cleanup; simpl in *;
    repeat unify_execs; cleanup.
    {
      exfalso; eapply finished_not_crashed_oracle_prefix in H13; eauto.
      setoid_rewrite app_nil_r at 2; eauto.
    }
    {
      eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
      repeat unify_execs; cleanup.

      edestruct HC_exec_same_finished; eauto.
      cleanup; invert_exec; simpl in *; cleanup.
      edestruct H; eauto.
      cleanup; simpl in *; cleanup.
      eexists; split; eauto.
      repeat econstructor; eauto.
    }
    {
      split_ors; cleanup; simpl in *;
      repeat unify_execs; cleanup.
      {
        eapply_fresh exec_deterministic_wrt_oracle_prefix in H12; eauto; cleanup.
        edestruct IHp.
        3: eauto.
        eauto.
        eauto.
        all: eauto.
        cleanup.
        eexists; split; eauto.
        solve [econstructor; eauto].
      }
      {
        exfalso; eapply finished_not_crashed_oracle_prefix in H7; eauto.
        setoid_rewrite app_nil_r at 2; eauto.
      }
    }
  }
  Unshelve.
  eauto.
Qed.

Theorem recover_simulation:
forall u n,
SimulationForProgramGeneral _ _ _ _ ATC_Refinement 
u _
  File.recover File.recover
  (ATC_reboot_list n)
  (authenticated_disk_reboot_list n)
  (fun s1 s2 => snd (snd s1) = snd (snd (snd s2)))
  ATC_Refinement.(Simulation.Definitions.refines).
  Proof.
      unfold File.recover, 
      SimulationForProgram,
      SimulationForProgramGeneral,
      ATC_reboot_list; 
      induction n; simpl in *; intros.
      {
          repeat invert_exec.
          simpl in *; cleanup; try tauto.
          destruct l; simpl in *; try lia.
          split_ors; cleanup; repeat unify_execs; cleanup.
          specialize (H2 (fun s => s)); cleanup.
          invert_exec'' H8; repeat invert_exec.
          invert_exec'' H10; repeat invert_exec.
          invert_exec'' H13; repeat invert_exec.
          
          simpl in *; cleanup.
          inversion H; inversion H2; subst.
          unfold HC_refines in *; simpl in *;
          split_ors; cleanup.
          {
            edestruct recovery_simulation with (n:= 0); simpl.
            3: unfold transaction_cache_reboot_list; 
            simpl; econstructor; eauto.
            instantiate (1:= [_]).
            simpl; split; intuition eauto.
            left; intuition eauto.
             do 2 eexists; intuition eauto.
             eexists; intuition eauto.

             left; do 2 eexists; intuition eauto.
             rewrite H0; eauto.

             unfold refines, refines_reboot, Transaction.transaction_rep,
             Transaction.transaction_reboot_rep in *.
             cleanup; eauto.

             cleanup.
             unfold transactional_disk_reboot_list,
             authenticated_disk_reboot_list in *; simpl in *; invert_exec.
             simpl in *; cleanup; 
             invert_exec'' H11; repeat invert_exec.
             
             eexists (RFinished _ _); split.
             repeat (econstructor; eauto).
             simpl; intuition eauto.
             destruct s_imp; destruct s_abs; simpl.
             destruct s, s1; eauto.
             (*
             unfold refines, Transaction.transaction_rep  in *; 
             simpl in *; cleanup; eauto.
             destruct t; eauto.
             *)
          }
          {
            unfold Transaction.recover in *; repeat invert_exec.
            split_ors; cleanup; repeat invert_exec;
            simpl in *; cleanup.
            (*
            eexists; intuition eauto.
            unfold authenticated_disk_reboot_list; simpl.
            *)
          }
      }
      {
        repeat invert_exec.
          simpl in *; cleanup; try tauto.
          split_ors; cleanup; repeat unify_execs; cleanup.
          invert_exec'' H11; repeat invert_exec.
          {
            invert_exec'' H10; repeat invert_exec.
            invert_exec'' H15; repeat invert_exec.
            simpl in *; cleanup.
            inversion H1; inversion H4; subst.
            unfold HC_refines in *; simpl in *;
            split_ors; cleanup.
            {
              unfold Transaction.recover in *; repeat invert_exec.
              simpl in *; cleanup.
            }
            {
              edestruct IHn; eauto.
              instantiate (1:= (_, (_, (_, _)))); simpl; intuition eauto.

              exists (Recovered (extract_state_r x0)).
              simpl; intuition eauto.
              
              repeat econstructor; eauto.
            }
          }
          {
            invert_exec'' H9; repeat invert_exec.
            simpl in *; cleanup.
            inversion H1; subst.
            unfold HC_refines in *; simpl in *;
            split_ors; cleanup.
            {
              unfold Transaction.recover in *; repeat invert_exec.
              simpl in *; cleanup.
            }
            {
              edestruct IHn; eauto.
              instantiate (1:= (_, (_, (_, _)))); simpl; intuition eauto.

              eexists (Recovered (extract_state_r _)).
              simpl; intuition eauto.
              
              repeat econstructor; eauto.
            }
          }
      }
  Qed.


  Theorem HC_recovery_exec_same:
      forall u T (p: AD.(prog) T) n 
      l_o_imp l_o_abs s_imp s_abs s_imp',
    not_init p ->
      recovery_exec ATCLang u l_o_imp s_imp (ATC_reboot_list n)
      (Simulation.Definitions.compile ATC_Refinement p)
      (Simulation.Definitions.compile ATC_Refinement File.recover) s_imp' ->

      recovery_oracles_refine_to ATC_Refinement u
      s_imp p File.recover (ATC_reboot_list n) l_o_imp l_o_abs ->

      Simulation.Definitions.refines
       ATC_Refinement s_imp
       s_abs ->

       (forall u s_imp s_abs T o x x0 x2 x3 x4,
       exec Definitions.imp u x3 s_imp
      (compile T o) (Finished x x0) ->
      token_refines T u s_imp o x4 x3 x2 ->
      refines s_imp s_abs ->
      (forall l, ~eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
     exists s_abs',
     TransactionalDiskLayer.exec' data_length u x2
       s_abs o (Finished s_abs' x0) /\
     refines x s_abs') ->

     (forall u s_imp s_abs T o x x2 x3 x4,
     exec Definitions.imp u x3 s_imp
   (compile T o) (Crashed x) ->
   token_refines T u s_imp o x4 x3 x2 ->
   refines s_imp s_abs ->
   (forall l, ~eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
   exists s_abs',
   TransactionalDiskLayer.exec' data_length u x2
     s_abs o (Crashed s_abs') /\
   refines_reboot x s_abs') ->

      exists s_abs' : Recovery_Result,
      recovery_exec AD u l_o_abs s_abs
      (authenticated_disk_reboot_list n) p File.recover s_abs' /\
      Simulation.Definitions.refines ATC_Refinement (extract_state_r s_imp')
    (extract_state_r s_abs') /\ extract_ret_r s_imp' = extract_ret_r s_abs'.
    Proof.
      intros; destruct n.
      {
        invert_exec.
        simpl in *; cleanup; try tauto.
        destruct l; simpl in *; try lia.
        split_ors; cleanup; repeat unify_execs; cleanup.
        eapply HC_exec_same_finished; eauto.
      }
      {
        unfold ATC_reboot_list in *; invert_exec.
        simpl in *; cleanup; try tauto.
        split_ors; cleanup; repeat unify_execs; cleanup.
        simpl in *.
        edestruct HC_exec_same_crashed; eauto; cleanup.
        edestruct recover_simulation.
        eauto.
        {
          simpl in *;
          instantiate (1:= (fst x0, (Empty, (snd (snd (snd x0)), snd (snd (snd x0)))))); 
          simpl; intuition eauto.
        }
        all: eauto.
        {
          cleanup.
          simpl in *; cleanup.
          eexists (Recovered _); split.
          unfold authenticated_disk_reboot_list; simpl; 
          econstructor; eauto.
          unfold HC_refines in *; simpl in *; cleanup.
          simpl; split; eauto.
        }
      }
Qed.


Lemma operation_simulation_finished:
      forall (u0 : user) (s_imp0 : Language.state' TransactionCacheOperation)
      s_abs0 (T0 : Type)
      (o : operation Definitions.abs_op T0)
      (x : Language.state' TransactionCacheOperation) 
      (x0 : T0) (x2 : TransactionalDiskLayer.token')
      (x3 : oracle' TransactionCacheOperation)
      (x4 : state Definitions.imp -> state Definitions.imp),
    exec Definitions.imp u0 x3 s_imp0 (compile T0 o) (Finished x x0) ->
    token_refines T0 u0 s_imp0 o x4 x3 x2 ->
    refines s_imp0 s_abs0 ->
    (forall l, ~eq_dep Type (operation Definitions.abs_op) T0 o unit (TransactionalDiskLayer.Init l)) ->
    exists s_abs' : TransactionalDiskLayer.state',
      TransactionalDiskLayer.exec' data_length u0 x2 s_abs0 o
        (Finished s_abs' x0) /\ refines x s_abs'.
    Proof.
      intros; destruct o.
      {
        edestruct read_simulation with (n:= 0); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
          simpl in *; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct write_simulation with (n:= 0); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
          simpl in *; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct commit_simulation with (n:= 0); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct abort_simulation with (n:= 0); eauto.
        2: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        edestruct TransactionToTransactionalDisk.Refinement.recovery_simulation with (n:= 0); eauto.
        3: {
          instantiate (1:= RFinished _ _).
          eapply ExecFinished; eauto.
         }
         instantiate (1:= [ _ ]). 
         simpl; eauto.
         split; eauto.
         left; do 2 eexists; intuition eauto.
         unfold refines, refines_reboot,
         Transaction.transaction_rep,
         Transaction.transaction_reboot_rep in *; 
         cleanup; eauto.
         cleanup; simpl in *.
         repeat invert_exec; simpl in *; cleanup.
        invert_exec'' H12.
         eexists; split; eauto.
      }
      {
        exfalso.
        eapply H2.
        eauto.
      }
    Qed.

Lemma operation_simulation_crashed:
    forall (u0 : user) (s_imp0 : Language.state' TransactionCacheOperation)
  s_abs0 (T0 : Type)
  (o : operation Definitions.abs_op T0)
  (x : Language.state' TransactionCacheOperation)
  (x2 : TransactionalDiskLayer.token')
  (x3 : oracle' TransactionCacheOperation)
  (x4 : state Definitions.imp -> state Definitions.imp),
exec Definitions.imp u0 x3 s_imp0 (compile T0 o) (Crashed x) ->
token_refines T0 u0 s_imp0 o x4 x3 x2 ->
refines s_imp0 s_abs0 ->
(forall l, ~eq_dep Type (operation Definitions.abs_op) _ o unit (TransactionalDiskLayer.Init l)) ->
exists s_abs' : TransactionalDiskLayer.state',
  TransactionalDiskLayer.exec' data_length u0 x2 s_abs0 o
    (Crashed s_abs') /\ refines_reboot x s_abs'.
    Proof.
      intros; destruct o; simpl in *.
      {
        intuition cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        eexists; intuition eauto.
        repeat econstructor.
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.
      }
      {
        intuition cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        eexists; intuition eauto.
        repeat econstructor.

        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.
      }
      {
        intuition cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        split_ors; cleanup.

        eexists; intuition eauto.
        repeat econstructor.
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.

        repeat econstructor.
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.


        eexists; intuition eauto.
        repeat econstructor.
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.

        repeat econstructor.
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.
      }
      {
        intuition cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        eexists; intuition eauto.
        repeat econstructor.
        
        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.
      }
      {
        intuition cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle_prefix in H; eauto; cleanup.

        eexists; intuition eauto.
        repeat econstructor.

        unfold refines, refines_reboot,
        Transaction.transaction_rep,
        Transaction.transaction_reboot_rep in *; cleanup; eauto.
      }
      { exfalso; eapply H2; eauto. }
    Unshelve.
    all: eauto.
    Qed.


Theorem ATC_simulation:
forall u n T (p: AD.(prog) T),
not_init p ->
SimulationForProgram ATC_Refinement u
  p File.recover
  (ATC_reboot_list n)
  (authenticated_disk_reboot_list n).
  Proof.
    unfold SimulationForProgram,
    SimulationForProgramGeneral; 
    intros.
    eapply HC_recovery_exec_same; eauto.
    eapply operation_simulation_finished.
    eapply operation_simulation_crashed.
  Qed.





Lemma ATC_oracle_refines_finished:
forall T (p: AD.(prog) T) u (o : oracle' ATCCore)
s s' r,
(exists s1,
@HC_refines _ _ _ _ ATCLang 
AD
Definitions.TDCoreRefinement s s1) ->
exec ATCLang u o s
(ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->

exists oa,
forall grs,
oracle_refines ATCCore
AuthenticatedDiskLayer.ADOperation
ATCLang AD ATC_CoreRefinement
T u s p grs o oa.

Proof.
induction p; simpl in *; intros.
{
destruct o.
{
  cleanup; invert_exec'' H0;
  repeat invert_exec.
  
  do 2 eexists; intuition eauto.
  simpl.
  eexists; intuition eauto.
  
  do 2 eexists; intuition eauto.
  simpl.
  eexists; intuition eauto.
}
{
  eapply lift2_invert_exec in H0; cleanup.
  edestruct TD_token_refines_finished; eauto; cleanup.
  unfold HC_refines in *; cleanup; eauto.
  do 2 eexists; intuition eauto.
  simpl.
  do 3 eexists; intuition eauto.
  apply HC_oracle_transformation_same.
}
}
{
eexists; right; eauto.
}
{
cleanup.
repeat invert_exec.
edestruct IHp; eauto.
eapply_fresh exec_compiled_preserves_refinement_finished in H1; eauto.
simpl in *; cleanup.
edestruct H; eauto.
eexists.
right.
do 7 eexists; intuition eauto.
}
Qed.

Lemma ATC_oracle_refines_crashed:
forall T (p: AD.(prog) T) u (o : oracle' ATCCore)
s s',
(exists s1,
@HC_refines _ _ _ _ ATCLang 
AD
Definitions.TDCoreRefinement s s1) ->
exec ATCLang u o s
(ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->

not_init p ->

exists oa,
oracle_refines ATCCore
AuthenticatedDiskLayer.ADOperation
ATCLang AD ATC_CoreRefinement
T u s p (fun s0 => (fst s0, ([], snd (snd s0))))  o oa.

Proof.
induction p; simpl in *; intros.
{
  destruct o.
  {
    cleanup; invert_exec'' H0;
    repeat invert_exec.
    
    do 2 eexists; intuition eauto.
    simpl.
    eexists; intuition eauto.
  }
  {
    eapply lift2_invert_exec_crashed in H0; cleanup.
    edestruct TD_token_refines_crashed; eauto; cleanup.
    unfold HC_refines in *; cleanup; eauto.
    do 2 eexists; intuition eauto.
    simpl.
    do 3 eexists; intuition eauto.
    apply HC_oracle_transformation_same.
  }
}
{
  eexists; left; eauto.
}
{
  cleanup.
  repeat invert_exec.
  split_ors; cleanup.
  {
    edestruct IHp; eauto.
  }
  {
    eapply_fresh ATC_oracle_refines_finished in H4; eauto; cleanup.
    eapply_fresh exec_compiled_preserves_refinement_finished in H4; eauto.
    simpl in *; cleanup.
    edestruct H; eauto.
    eexists.
    right.
    do 7 eexists; intuition eauto.
  }

}
Qed.

Lemma ATC_exec_lift_finished:
  forall T (p: AD.(prog) T) u o_imp o_abs s_imp s_abs s_imp' r grs,
  exec ATCLang u o_imp s_imp
  (ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s_imp' r) ->
  ATC_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->
  oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation 
  ATCLang AD ATC_CoreRefinement T u s_imp p grs o_imp o_abs ->
  
  (forall T o s_imp s_imp' s_abs r o_imp t_abs grs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Finished s_imp' r) ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o grs o_imp t_abs ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TDCore
data_length) u t_abs s_abs o (Finished s_abs' r) /\
  TransactionToTransactionalDisk.Definitions.refines s_imp' s_abs') ->
  
  exists s_abs', 
  exec AD u o_abs s_abs p (Finished s_abs' r) /\
  ATC_Refinement.(Simulation.Definitions.refines) s_imp' s_abs'.
  Proof.
    induction p; simpl; intros; eauto.
    {
      cleanup.
      destruct o; simpl in *; repeat invert_exec;
      cleanup.
      {
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      }
      {
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      }
      {
        apply HC_oracle_transformation_id in H3; subst.
        unfold HC_refines in *; simpl in *; cleanup.
        edestruct H2; eauto; cleanup.
        eexists. 
        split.
        repeat econstructor.
        intuition eauto.
        simpl; intuition eauto.
      }
    }
    {
      split_ors; cleanup; unify_execs; cleanup.
      repeat invert_exec.
      eexists. 
      split.
      repeat econstructor.
      intuition eauto.
    }
    {
      invert_exec;
      split_ors; cleanup; try unify_execs; cleanup.
      exfalso; eapply finished_not_crashed_oracle_prefix.
      eauto.
      2: eauto.
      rewrite <- app_assoc; eauto.
      eapply exec_finished_deterministic_prefix in H0; eauto; cleanup.
      eapply exec_deterministic_wrt_oracle in H4; eauto; cleanup.
      edestruct IHp; eauto; cleanup.
      edestruct H; eauto; cleanup.
      eexists; split; eauto.
      econstructor; eauto.
      simpl in *; eauto.
    }
    Unshelve.
    eauto.
  Qed.

Definition ATC_reboot_f := fun s: ATCLang.(state) => (fst s, TC_reboot_f (snd s)).
Definition AD_reboot_f := fun s: AD.(state) => (fst s, TD_reboot_f (snd s)).


Lemma ATC_exec_lift_crashed:
  forall T (p: AD.(prog) T) u o_imp o_abs s_imp s_abs s_imp',
  exec ATCLang u o_imp s_imp
  (ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s_imp') ->
  ATC_Refinement.(Simulation.Definitions.refines) s_imp s_abs ->
  oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation 
  ATCLang AD ATC_CoreRefinement T u s_imp p ATC_reboot_f o_imp o_abs ->
  
  (forall T o s_imp s_imp' s_abs r o_imp t_abs grs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Finished s_imp' r) ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o grs o_imp t_abs ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TDCore
data_length) u t_abs s_abs o (Finished s_abs' r) /\
  TransactionToTransactionalDisk.Definitions.refines s_imp' s_abs') ->
  
  (forall T o s_imp s_imp' s_abs o_imp t_abs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Crashed s_imp') ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o TC_reboot_f o_imp t_abs ->
  (forall l, ~ eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TDCore
data_length) u t_abs s_abs o (Crashed s_abs') /\
  TransactionToTransactionalDisk.Definitions.refines_reboot (TC_reboot_f s_imp') (TD_reboot_f s_abs')) ->

  not_init p ->
  exists s_abs', 
  exec AD u o_abs s_abs p (Crashed s_abs') /\
  TransactionToTransactionalDisk.Definitions.refines_reboot (snd (ATC_reboot_f s_imp')) (snd (AD_reboot_f s_abs')) /\
fst (ATC_reboot_f s_imp')  = fst (AD_reboot_f s_abs').
  Proof.
    induction p; simpl; intros; eauto.
    {
      cleanup_no_match.
      destruct o; simpl in *; repeat invert_exec;
      cleanup.
      {
      destruct s_abs.
      eexists; intuition eauto.
      repeat econstructor; eauto.
      unfold TC_reboot_f, TD_reboot_f; simpl; eauto.
      unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines_reboot in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines, Transaction.transaction_reboot_rep,
      Transaction.transaction_rep in *; simpl in *; simpl; cleanup; eauto.
      unfold HC_refines in *; simpl in *; cleanup; eauto.
      }
      {
        apply HC_oracle_transformation_id in H5; subst.
        unfold HC_refines in *; simpl in *; cleanup.
        edestruct H3; eauto; cleanup.
        eexists. 
        split.
        repeat econstructor.
        intuition eauto.
        simpl; intuition eauto.
      }
    }
    {
      split_ors; cleanup; unify_execs; cleanup.
      repeat invert_exec.
      eexists. 
      split.
      repeat econstructor.
      intuition eauto.
      unfold TC_reboot_f, TD_reboot_f; simpl; eauto.
      unfold HC_refines, TransactionToTransactionalDisk.Definitions.refines_reboot in *; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines, Transaction.transaction_reboot_rep,
      Transaction.transaction_rep in *; simpl in *; simpl; cleanup; eauto.
      unfold HC_refines in *; simpl in *; cleanup; eauto.
    }
    {
      invert_exec;
      repeat split_ors; cleanup; try unify_execs; cleanup.
      edestruct IHp; eauto; cleanup.
      eexists; split.
      econstructor; eauto.
      simpl in *; eauto.

      exfalso; eapply finished_not_crashed_oracle_prefix.
        eauto.
        2: eauto.
        rewrite <- app_assoc; eauto.

        eapply finished_not_crashed_oracle_prefix in H8.
        exfalso; apply H8; eauto.
        rewrite <- app_assoc; eauto.

        eapply exec_finished_deterministic_prefix in H12; eauto; cleanup.
        eapply exec_deterministic_wrt_oracle in H13; eauto; cleanup.
        eapply ATC_exec_lift_finished in H8; eauto; cleanup.
        edestruct H; eauto; cleanup.
      eexists; split; eauto.
      econstructor; eauto.
      simpl in *; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.

Lemma ATC_exec_lift_finished_recovery:
forall u o_imp o_abs s_imp s_abs s_imp' r grs,
exec ATCLang u o_imp s_imp
(ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) (Finished s_imp' r) ->
TransactionToTransactionalDisk.Definitions.refines_reboot (snd s_imp) (snd s_abs) ->
fst s_imp  = fst s_abs ->

oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation 
ATCLang AD ATC_CoreRefinement _ u s_imp (File.recover) grs o_imp o_abs ->

exists s_abs', 
exec AD u o_abs s_abs (File.recover) (Finished s_abs' r) /\
ATC_Refinement.(Simulation.Definitions.refines) s_imp' s_abs'.
Proof.
  simpl; intros; eauto.
  cleanup; simpl in *.
  simpl in *.
  repeat invert_exec; cleanup.
  split_ors; cleanup; repeat invert_exec; cleanup.
  {
    eapply_fresh (Transaction.recover_finished) in H; eauto; cleanup.
    simpl in *; cleanup.

    destruct s_abs.
    eexists; intuition eauto.
    repeat econstructor; eauto.
    simpl in *.
    unfold HC_refines; simpl; intuition eauto.
  }
  {
    unfold Transaction.recover in *; repeat invert_exec; cleanup.
    split_ors; cleanup; repeat invert_exec; cleanup;
    simpl in *; cleanup; try congruence.
  }
Qed.

Lemma ATC_exec_lift_crashed_recovery:
forall u o_imp o_abs s_imp s_abs s_imp' grs,
exec ATCLang u o_imp s_imp
(ATC_Refinement.(Simulation.Definitions.compile) (File.recover)) (Crashed s_imp') ->
TransactionToTransactionalDisk.Definitions.refines_reboot (snd s_imp) (snd s_abs) ->
fst s_imp  = fst s_abs ->

oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation 
ATCLang AD ATC_CoreRefinement _ u s_imp (File.recover) grs o_imp o_abs ->

exists s_abs', 
exec AD u o_abs s_abs (File.recover) (Crashed s_abs') /\
TransactionToTransactionalDisk.Definitions.refines_reboot (snd s_imp') (snd s_abs') /\
fst s_imp'  = fst s_abs'.
Proof.
  simpl; intros; eauto.
  cleanup; simpl in *.
  simpl in *.
  repeat invert_exec; cleanup.
  repeat split_ors; cleanup; repeat invert_exec; cleanup.
  {
    unfold Transaction.recover in *; repeat invert_exec; cleanup.
    simpl in *; cleanup; try congruence.
  }
  {
    unfold Transaction.recover in *; repeat invert_exec; cleanup.
    simpl in *; cleanup; try congruence.
  }

  {
    eapply_fresh (Transaction.recover_crashed) in H2; eauto; cleanup.
    simpl in *; cleanup.
    destruct s_abs.
    eexists; intuition eauto.
    repeat econstructor; eauto.
  }
  {
    destruct s_abs.
    eexists; intuition eauto.
    repeat econstructor; eauto.
  }
Qed.