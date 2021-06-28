Require Import Lia Framework ATCLayer File FileDiskNoninterference.

Set Nested Proofs Allowed.

(*
Lemma HC_oracle_refines_2 :
forall O O1 O2
(L1: Language O1) (L2: Language O2)
(HCL1: Language (HorizontalComposition O O1))
(HCL2: Language (HorizontalComposition O O2))
(RC: CoreRefinement L1 O2)
u T p  s s0 x0 o,
let R := LiftRefinement L2 RC in
let HCR := HC_Refinement HCL1 HCL2 RC in
(forall u s T (op:O2.(operation) T) o t, 
token_refines RC u s op (fun s1 : state L1 => s1) o t ->
minimal_oracle (compile_core RC op) u s o) ->
oracle_refines O1 O2 L1 L2 RC T u s0 p (fun s1 : state L1 => s1) x0 o ->
(forall T (p: L2.(prog) T), HCR.(Simulation.Definitions.compile) (lift_L2 _ p) = 
lift_L2 _ (R.(Simulation.Definitions.compile) p)) ->
oracle_refines (HorizontalComposition O O1) (HorizontalComposition O O2) HCL1
HCL2 (HC_Core_Refinement HCL1 HCL2 RC) T u (s, s0) 
(lift_L2 O p) (fun s1 : HorizontalComposition.state' O O1 => s1)
(map
(fun o0 : Language.token' O1 =>
match o0 with
| OpToken _ o1 => OpToken (HorizontalComposition O O1) (Token2 O O1 o1)
| Language.Crash _ => Language.Crash (HorizontalComposition O O1)
| Language.Cont _ => Language.Cont (HorizontalComposition O O1)
end) x0)
(map
(fun o0 : Language.token' O2 =>
match o0 with
| OpToken _ o1 => OpToken (HorizontalComposition O O2) (Token2 O O2 o1)
| Language.Crash _ => Language.Crash (HorizontalComposition O O2)
| Language.Cont _ => Language.Cont (HorizontalComposition O O2)
end) o).
Proof.
induction p; simpl; intros; cleanup.
{
  eexists; simpl; split; eauto.
  do 5 eexists; intuition eauto.
  setoid_rewrite app_nil_r; eauto.
  apply HC_oracle_transformation_same; eauto.
}
{
  split_ors; cleanup; invert_exec.
  simpl; left; eexists; intuition eauto.
  econstructor; eauto.
  simpl; right; do 2 eexists; intuition eauto.
  econstructor; eauto.
}
{
  split_ors; cleanup.
  {
    repeat rewrite map_app; do 4 eexists; intuition eauto.
    left; eexists; intuition eauto.
    rewrite H2.
    eapply lift2_exec_step_crashed; eauto.
  }
  {
  repeat rewrite map_app; do 4 eexists; intuition eauto.
  destruct x5;
  right; do 3 eexists; intuition eauto.
  rewrite H2; eapply lift2_exec_step; eauto.
  rewrite H2; eapply lift2_exec_step; eauto.
  rewrite H2; eapply lift2_exec_step; eauto.
  rewrite H2; eapply lift2_exec_step_crashed; eauto.
  }
}
Qed.
*)
(*
Lemma HC_abstract_oracles_exist_wrt_2_recover:
forall O O1 O2
(L1: Language O1) (L2: Language O2)
(HCL1: Language (HorizontalComposition O O1))
(HCL2: Language (HorizontalComposition O O2))
(RC: CoreRefinement L1 O2)
(l_grs1: list (L1.(state) -> L1.(state))) 
(l_grs2: list (HCL1.(state) -> HCL1.(state)))
u (rec: HCL2.(prog) unit) 
(rec2: L2.(prog) unit)
refines_reboot,

let R := LiftRefinement L2 RC in
let HCR := HC_Refinement HCL1 HCL2 RC in

abstract_oracles_exist_wrt R refines_reboot u rec2 rec2 l_grs1 ->
Forall2 (fun f1 f2 => forall (s: (O.(Core.state) * L1.(state))), f1 (snd s) = snd (f2 s)) l_grs1 l_grs2 ->
(HCR.(Simulation.Definitions.compile) (lift_L2 _ rec2) = lift_L2 _ (R.(Simulation.Definitions.compile) rec2)) ->

(forall lo s ret grs1 grs2 l_grs1' l_grs2', 
recovery_exec' u lo s l_grs2'
(HCR.(Simulation.Definitions.compile) rec)
(HCR.(Simulation.Definitions.compile) rec) ret ->
l_grs1 = grs1::l_grs1' ->
l_grs2 = grs2::l_grs2' ->
exists lo' ret',
   recovery_exec' u lo' (snd s) l_grs1' 
   (R.(Simulation.Definitions.compile) rec2)
  (R.(Simulation.Definitions.compile) rec2)  ret' /\
  length lo = length lo') -> 

(forall o s s' grs1 l_grs1', 
exec L1 u o s (R.(Simulation.Definitions.compile) rec2) (Crashed s') ->
(exists sa, refines_reboot s sa) ->
l_grs1 = grs1::l_grs1' ->
exists sa', refines_reboot (grs1 s') sa') ->

abstract_oracles_exist_wrt HCR XXXXX u
  rec rec l_grs2.
Proof.
    unfold abstract_oracles_exist_wrt; simpl; 
    induction l_grs1; simpl; intros;
    eapply_fresh forall2_length in H1;
    destruct l_grs2; simpl in *; try lia;
    unfold HC_refines in *; cleanup;
    repeat invert_exec; cleanup.
    {
        rewrite H2 in H14.
        eapply lift2_invert_exec in H14 ; cleanup.
        simpl in *.
        
        edestruct H; eauto.
        simpl; econstructor; eauto.

        simpl in *; cleanup; try intuition;
        cleanup; repeat unify_execs; cleanup.
        exists ([(map
        (fun o0 : Language.token' O2 =>
         match o0 with
         | OpToken _ o1 =>
             OpToken (HorizontalComposition O O2)
               (Token2 O O2 o1)
         | Language.Crash _ =>
             Language.Crash
               (HorizontalComposition O O2)
         | Language.Cont _ =>
             Language.Cont
               (HorizontalComposition O O2)
         end) o)]).
        simpl; split; eauto.
        destruct si.
        left; do 2 eexists; intuition eauto.
        rewrite H2.
        eapply lift2_exec_step; eauto.
        eapply HC_oracle_refines_2; eauto.
    }
    {
      inversion H1; cleanup.
      rewrite H2 in H17.
      eapply_fresh lift2_invert_exec_crashed in H17; cleanup.
      simpl in *.

      edestruct H3; eauto; cleanup.
      edestruct H; eauto.
      econstructor; eauto.
      rewrite H10; eauto.
      simpl in *; cleanup; try tauto.
      split_ors; cleanup; repeat unify_execs; cleanup.

      edestruct H0; eauto.
      rewrite H10; eauto.
      simpl in *; cleanup; try tauto.

      simpl in *; eexists (_::_); simpl.
      split; eauto.
      setoid_rewrite H11; eauto.
      rewrite map_length.
      apply H13.
      
      right.
      eexists; intuition eauto.
      rewrite H2; simpl; eauto.
*)


(*
Lemma HC_abstract_oracles_exist_wrt_2:
forall O O1 O2
(L1: Language O1) (L2: Language O2)
(HCL1: Language (HorizontalComposition O O1))
(HCL2: Language (HorizontalComposition O O2))
(RC: CoreRefinement L1 O2)
(l_grs1: list (L1.(state) -> L1.(state))) 
(l_grs2: list (HCL1.(state) -> HCL1.(state)))
u T (p: L2.(prog) T) 
(rec: HCL2.(prog) unit) 
(rec2: L2.(prog) unit)
refines_reboot,

let R := LiftRefinement L2 RC in
let HCR := HC_Refinement HCL1 HCL2 RC in

abstract_oracles_exist_wrt R R.(refines) u p rec2 l_grs1 ->
(forall grs1 l_grs1', 
l_grs1 = grs1::l_grs1' ->
abstract_oracles_exist_wrt R refines_reboot u rec2 rec2 l_grs1') ->
Forall2 (fun f1 f2 => forall (s: (O.(Core.state) * L1.(state))), f1 (snd s) = snd (f2 s)) l_grs1 l_grs2 ->
(forall T (p: L2.(prog) T), HCR.(Simulation.Definitions.compile) (lift_L2 _ p) = lift_L2 _ (R.(Simulation.Definitions.compile) p)) ->

(forall lo s ret grs1 grs2 l_grs1' l_grs2', 
recovery_exec' u lo s l_grs2'
(HCR.(Simulation.Definitions.compile) rec)
(HCR.(Simulation.Definitions.compile) rec) ret ->
l_grs1 = grs1::l_grs1' ->
l_grs2 = grs2::l_grs2' ->
exists lo' ret',
   recovery_exec' u lo' (snd s) l_grs1' 
   (R.(Simulation.Definitions.compile) rec2)
  (R.(Simulation.Definitions.compile) rec2)  ret' /\
  length lo = length lo') -> 

(forall o s s' grs1 l_grs1', 
exec L1 u o s (R.(Simulation.Definitions.compile) p) (Crashed s') ->
(exists sa, R.(refines) s sa) ->
l_grs1 = grs1::l_grs1' ->
exists sa', refines_reboot (grs1 s') sa') ->

(forall u s T (op:O2.(operation) T) o t, 
token_refines RC u s op (fun s1 : state L1 => s1) o t ->
minimal_oracle (compile_core RC op) u s o) ->

abstract_oracles_exist_wrt HCR HCR.(refines) u
  (lift_L2 _ p) rec l_grs2.
Proof.
    unfold abstract_oracles_exist_wrt; simpl; 
    induction l_grs1; simpl; intros;
    eapply_fresh forall2_length in H1;
    destruct l_grs2; simpl in *; try lia;
    unfold HC_refines in *; cleanup;
    repeat invert_exec; cleanup.
    {
        rewrite H2 in H15.
        eapply lift2_invert_exec in H15 ; cleanup.
        simpl in *.
        
        edestruct H; eauto.
        simpl; econstructor; eauto.

        simpl in *; cleanup; try intuition;
        cleanup; repeat unify_execs; cleanup.
        exists ([(map
        (fun o0 : Language.token' O2 =>
         match o0 with
         | OpToken _ o1 =>
             OpToken (HorizontalComposition O O2)
               (Token2 O O2 o1)
         | Language.Crash _ =>
             Language.Crash
               (HorizontalComposition O O2)
         | Language.Cont _ =>
             Language.Cont
               (HorizontalComposition O O2)
         end) o)]).
        simpl; split; eauto.
        destruct si.
        left; do 2 eexists; intuition eauto.
        rewrite H2.
        eapply lift2_exec_step; eauto.
        eapply HC_oracle_refines_2; eauto.
    }
    {
      inversion H1; cleanup.
      rewrite H2 in H18.
      eapply_fresh lift2_invert_exec_crashed in H18; cleanup.
      simpl in *.

      edestruct H3; eauto; cleanup.
      edestruct H; eauto.
      econstructor; eauto.
      rewrite H11; eauto.
      simpl in *; cleanup; try tauto.
      split_ors; cleanup; repeat unify_execs; cleanup.

      edestruct H0; eauto.
      rewrite H11; eauto.
      simpl in *; cleanup; try tauto.

      simpl in *; eexists (_::_); simpl.
      split; eauto.
      setoid_rewrite H12; eauto.
      rewrite map_length.
      apply H14.
      
      right.
      eexists; intuition eauto.
      rewrite H2; simpl; eauto.

      unfold oracle_refines.
      
      admit.
      

      admit.
    }
Abort.
*)

Require Import TransactionalDiskRefinement.

Lemma AOE_recover:
forall n u,
abstract_oracles_exist_wrt
(LiftRefinement AuthenticatedDisk
  (HC_Core_Refinement ATCLang AuthenticatedDisk
  Definitions.TransactionalDiskCoreRefinement))
(fun s1 s2 => refines_reboot (snd s1) (snd s2))
u
recover
recover (ATC_reboot_list n).
Proof.
    unfold ATC_reboot_list,
    abstract_oracles_exist_wrt;
    induction n; simpl; intros.
    { (* base case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh minimal_oracle_finished_same in H7. *)
      invert_exec'' H7.
      invert_exec'' H6.
      repeat invert_exec; cleanup.
      invert_exec'' H10.
      invert_exec'' H6.
      repeat invert_exec; cleanup.
      eexists [_]; simpl.
      intuition eauto.
      left; intuition eauto.
      do 2 eexists; intuition eauto.
      repeat (rewrite cons_app;
      repeat econstructor; eauto).
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      simpl; eexists; intuition eauto.
      simpl; eexists; intuition eauto.
      left; do 2 eexists; intuition eauto.
      repeat (rewrite cons_app;
      repeat econstructor; eauto).
    }
    { (* Inductive case *)
      repeat invert_exec; cleanup.
      (* eapply_fresh exec_crashed_minimal_oracle in H10; cleanup. *)
      invert_exec'' H10; repeat invert_exec; cleanup.
      {
        invert_exec'' H6; repeat invert_exec; cleanup.
        invert_exec'' H9; repeat invert_exec; cleanup.
        edestruct IHn; only 2: eauto.
        simpl; unfold refines, HC_refines,
        refines_reboot in *; simpl in *;
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_reboot_rep in *; 
        simpl in *; cleanup.
        eexists; eauto.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H0.
      rewrite H0; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      rewrite cons_app.
      repeat econstructor.
      eapply ExecP2Crash with (s:= (fst si, ([], snd (snd si)))).
      repeat econstructor; eauto.
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      simpl.
      do 2 eexists; intuition eauto.
      (*
      rewrite app_nil_r; eauto.
      simpl; intuition eauto.
      do 2 eexists; intuition eauto.
      {
        unfold minimal_oracle; intros.
        intros Hn; simpl in *.
        destruct n0; simpl in *.
        eapply exec_empty_oracle; eauto.
        destruct n0; simpl in *; try lia.
        invert_exec'' Hn.
        apply app_eq_unit in H3;
        split_ors; cleanup; 
        eapply exec_empty_oracle; eauto.
        apply app_eq_unit in H3;
        split_ors; cleanup; 
        try solve [eapply exec_empty_oracle; eauto].
        invert_exec'' H8; repeat invert_exec.
      }
      *)
      right. do 2 eexists.
      unfold Transaction.recover.
      rewrite cons_app;
      econstructor; eauto.
      repeat econstructor; eauto.
      repeat econstructor; eauto.
      intuition eauto.
    }
    {
      (* eapply exec_crashed_minimum_oracle in H5; cleanup. 
      rewrite <- app_assoc. *)
      invert_exec'' H5; repeat invert_exec; cleanup.
      edestruct IHn; only 2: eauto.
      simpl; unfold refines, HC_refines,
      refines_reboot in *; simpl in *;
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_reboot_rep in *; 
      simpl in *; cleanup.
      eexists; eauto.

      eexists (_::_); 
      simpl; intuition eauto.
      eapply recovery_oracles_refine_to_length in H0.
      rewrite H0; eauto.
      eauto.
      
      right; intuition eauto.
      eexists; intuition eauto.
      rewrite cons_app;
      eapply ExecBindCrash.
      repeat econstructor; eauto.
      eexists; intuition eauto.
      do 3 eexists; intuition eauto.
      (*
      do 2 eexists; intuition eauto.
      instantiate (1:= o2).
      rewrite cons_app; eauto.
      simpl; eauto.
      {
        unfold minimal_oracle; intros.
        intros Hn; simpl in *.
        destruct n0; simpl in *; try lia.
        eapply exec_empty_oracle; eauto.
      }
      *)
      right; do 2 eexists; intuition eauto.
      unfold Transaction.recover.
      rewrite cons_app;
      eapply ExecBindCrash; eauto.
      repeat econstructor; eauto.
      destruct si.
      simpl.
      destruct s0.
      repeat econstructor; eauto.
    }
  }
  Unshelve.
  all: exact TransactionCacheLang.
  Qed.


  Lemma compile_lift2_comm:
  forall u T (p: TransactionalDisk.(prog) T) o s ret,
  Language.exec' u o s
  (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TransactionalDiskOperation
            FSParameters.data_length)) ATCLang AuthenticatedDisk
      (HC_Core_Refinement ATCLang AuthenticatedDisk
        TransactionalDiskCoreRefinement) T
      (lift_L2 AuthenticationOperation p)) ret ->

      Language.exec' u o s
      (lift_L2 AuthenticationOperation 
        (TransactionalDiskRefinement.(Simulation.Definitions.compile) p)) ret.
  Proof.
    induction p; simpl; intros; eauto.
    invert_exec'' H0.
    eapply IHp in H7.
    eapply H in H10.
    econstructor; eauto.
    eapply IHp in H6.
    eapply ExecBindCrash; eauto.
  Qed.


  Lemma compile_lift2_comm_rev:
  forall u T (p: TransactionalDisk.(prog) T) o s ret,
  Language.exec' u o s
      (lift_L2 AuthenticationOperation 
        (TransactionalDiskRefinement.(Simulation.Definitions.compile) p)) ret ->
  
  Language.exec' u o s
  (RefinementLift.compile
      (HorizontalComposition AuthenticationOperation
        TransactionCacheOperation)
      (HorizontalComposition AuthenticationOperation
        (TransactionalDiskLayer.TransactionalDiskOperation
            FSParameters.data_length)) ATCLang AuthenticatedDisk
      (HC_Core_Refinement ATCLang AuthenticatedDisk
        TransactionalDiskCoreRefinement) T
      (lift_L2 AuthenticationOperation p)) ret.
  Proof.
    induction p; simpl; intros; eauto.
    invert_exec'' H0.
    eapply IHp in H7.
    eapply H in H10.
    econstructor; eauto.
    eapply IHp in H6.
    eapply ExecBindCrash; eauto.
  Qed.



Lemma ATC_AOE:
forall u T (p: TransactionalDisk.(prog) T) n, 

(forall o s s' r, 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec TransactionCacheLang u o (snd s) 
(TransactionalDiskRefinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
exists oa, oracle_refines _ _
  ATCLang AuthenticatedDisk
  ATC_CoreRefinement T u s
  (lift_L2 AuthenticationOperation p)
  (fun
     s : HorizontalComposition.state'
           AuthenticationOperation
           TransactionCacheOperation
   => s) (map
       (fun o : Language.token' TransactionCacheOperation =>
        match o with
        | OpToken _ o1 =>
            OpToken
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
              (Token2 AuthenticationOperation
                 TransactionCacheOperation o1)
        | Language.Crash _ =>
            Language.Crash
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        | Language.Cont _ =>
            Language.Cont
              (HorizontalComposition AuthenticationOperation
                 TransactionCacheOperation)
        end) o) oa) ->

        (forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
Language.exec' u o s
        (RefinementLift.compile
           (HorizontalComposition AuthenticationOperation
              TransactionCacheOperation)
           (HorizontalComposition AuthenticationOperation
              (TransactionalDiskLayer.TransactionalDiskOperation
                 FSParameters.data_length)) ATCLang AuthenticatedDisk
           (HC_Core_Refinement ATCLang AuthenticatedDisk
              TransactionalDiskCoreRefinement) T
           (lift_L2 AuthenticationOperation p)) (Crashed s') ->
exists oa, oracle_refines _ _
  ATCLang AuthenticatedDisk
  ATC_CoreRefinement T u s
  (lift_L2 AuthenticationOperation p)
  (fun
     s : HorizontalComposition.state'
           AuthenticationOperation
           TransactionCacheOperation
   => (fst s, ([], snd (snd s)))) o oa) ->

(forall o s s', 
(exists s1, refines s s1) ->
exec TransactionCacheLang u o s 
(TransactionalDiskRefinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists s1', refines_reboot s' s1') ->
abstract_oracles_exist_wrt ATC_Refinement
  (ATC_Refinement.(Simulation.Definitions.refines)) u
  (@lift_L2 AuthenticationOperation _ TransactionalDisk _ p) 
  File.recover (ATC_reboot_list n).
Proof.
    intros; destruct n; simpl; eauto.
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      eapply_fresh compile_lift2_comm in H10.
      eapply lift2_invert_exec in Hx; cleanup.
      edestruct H; eauto.

      eexists [_]; simpl; eauto.
      split; intuition eauto.
      left; do 2 eexists; intuition eauto.
    }
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct AOE_recover; eauto.
      {
        unfold HC_refines in *; 
        simpl in *; cleanup.
        eapply compile_lift2_comm in H13.
        eapply lift2_invert_exec_crashed in H13; cleanup.
        edestruct H1; eauto.
        unfold refines_reboot, Transaction.transaction_reboot_rep in *; 
        simpl in *; eauto.
        exists (fst x, (snd x1, snd x1)); eauto.
      }

      eapply_fresh compile_lift2_comm in H13.
      eapply lift2_invert_exec_crashed in Hx; cleanup.
      edestruct H0; eauto.

      eexists (_ :: _).
      simpl.
      intuition eauto.
      eapply recovery_oracles_refine_to_length in H3; eauto.
    }
    Unshelve.
    all: exact ATCLang.
Qed.


Lemma ATC_AOE_2:
forall u T (p: AuthenticatedDisk.(prog) T) n, 

(forall o s s' r, 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s 
(ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
exists oa, oracle_refines _ _
  ATCLang AuthenticatedDisk
  ATC_CoreRefinement T u s p (fun s => s) o oa) ->

(forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s (ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists oa, oracle_refines _ _
  ATCLang AuthenticatedDisk
  ATC_CoreRefinement T u s p
  (fun
     s : HorizontalComposition.state'
           AuthenticationOperation
           TransactionCacheOperation
   => (fst s, ([], snd (snd s)))) o oa) ->

(forall o s s', 
(exists s1, ATC_Refinement.(Simulation.Definitions.refines) s s1) ->
exec ATCLang u o s 
(ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->
exists s1', refines_reboot (snd s') s1') ->

abstract_oracles_exist_wrt ATC_Refinement 
  (ATC_Refinement.(Simulation.Definitions.refines)) u p 
  File.recover (ATC_reboot_list n).
Proof.
    intros; destruct n; simpl; eauto.
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct H; eauto.

      eexists [_]; simpl; eauto.
      split; intuition eauto.
      left; do 2 eexists; intuition eauto.
    }
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list in *; 
      simpl in *; intros.
      repeat invert_exec.
      edestruct AOE_recover; eauto.
      {
        unfold HC_refines in *; 
        simpl in *; cleanup.
        edestruct H1; eauto.
        unfold refines_reboot, Transaction.transaction_reboot_rep in *; 
        simpl in *; eauto.
        exists (fst x, (snd x0, snd x0)); eauto.
      }
      
      edestruct H0; eauto.

      eexists (_ :: _).
      simpl.
      intuition eauto.
      eapply recovery_oracles_refine_to_length in H3; eauto.
      }
Qed.
