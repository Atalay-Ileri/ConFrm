Require Import Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer TransferProofs ATCSimulation ATCAOE.

(* Notation "'TransactionalDiskCore'" := (TransactionalDiskOperation data_length). *)

Import FileDiskLayer.

Theorem recovery_exec_termination_sensitive_bind:
  forall O (L: Language O) 
  T (p1 p2: L.(prog) T) 
  T' (p3 p4: T -> L.(prog) T') rec s1 s2 
  lob l_grs u s1',
  (forall s1' lo lgrs, 
  recovery_exec L u lo s1 lgrs p1 rec s1' ->
   exists s2',
   recovery_exec L u lo s2 lgrs p2 rec s2') ->

  (forall s1' s2' s1r t1 t2 lo lo' lgrs, 
  recovery_exec L u lo s1 [] p1 rec (RFinished s1' t1) ->
  recovery_exec L u lo s2 [] p2 rec (RFinished s2' t2) ->
    
  recovery_exec L u lo' s1' lgrs (p3 t1) rec s1r ->
  exists s2r,
  recovery_exec L u lo' s2' lgrs (p4 t2) rec s2r) ->

  recovery_exec L u lob s1 l_grs (Bind p1 p3) rec s1' ->
   exists s2',
   recovery_exec L u lob s2 l_grs (Bind p2 p4) rec s2'.
Proof.
  intros; repeat invert_exec.
  {
      invert_exec'' H10.

      edestruct H.
      econstructor; eauto.
      invert_exec.

      edestruct H0; eauto;
      try solve [econstructor; eauto].
      invert_exec.

      eexists; repeat econstructor; eauto.
  }
  {
    invert_exec'' H9.
    {
      edestruct H.
      econstructor; eauto.
      invert_exec.

      edestruct H0; eauto;
      try solve [econstructor; eauto].
      invert_exec.

      eexists; repeat econstructor; eauto.
    }
    {
      edestruct H.
      eapply ExecRecovered; eauto.
      invert_exec.
      eexists; eapply ExecRecovered; eauto.
      eapply ExecBindCrash; eauto.
    }
  }
Qed.


Lemma not_init_read:
forall inum off,
not_init (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off))).
{
        simpl.
        Transparent Inode.get_owner.
        unfold Inode.get_owner, Inode.get_inode,
        Inode.InodeAllocator.read; simpl.
        intuition eauto.
        destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) inum);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct u0; simpl; intuition eauto.
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number,
         Inode.get_inode, 
         Inode.InodeAllocator.read ; simpl; intuition eauto.
        destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) inum);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        unfold File.DiskAllocator.read; simpl; intuition eauto.
        destruct (Compare_dec.lt_dec a File.DiskAllocatorParams.num_of_blocks);
        simpl; intuition eauto.
        inversion H.
        destruct (nth_error (value_to_bits t) a);
        simpl; intuition eauto.
        destruct b; simpl; intuition eauto.
        inversion H.
        destruct t; simpl; intuition eauto.
        destruct t; simpl; intuition eauto.
        all: inversion H.
      }
Qed.


Lemma abstract_oracles_exist_wrt_compositional:
forall (C_imp C_abs: Core)
 (L_imp: Language C_imp)
 (L_abs: Language C_abs)
 (CoreRefinement : CoreRefinement L_imp C_abs)
u l_grs T (p1: prog L_abs T) T' (p2: T -> prog L_abs T') rec, 
let R := LiftRefinement L_abs CoreRefinement in
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p1 rec [] ->
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u p1 rec l_grs ->
(forall t, abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u (p2 t) rec l_grs) ->
abstract_oracles_exist_wrt R R.(Simulation.Definitions.refines) u (Bind p1 p2) rec l_grs.
Proof.
    unfold abstract_oracles_exist_wrt; 
    simpl; intros;
    repeat invert_exec.
    {
        invert_exec'' H12.
        edestruct H; eauto.
        econstructor; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

        edestruct H1; eauto.
        econstructor; eauto.

        simpl in *; cleanup; try intuition; simpl in *; try congruence;
        cleanup; repeat unify_execs; cleanup.
        exists [o0++o].
        simpl; split; eauto.
        repeat left.
        do 2 eexists; econstructor; eauto.
        econstructor; eauto.
        intuition eauto.
        right; do 7 eexists; intuition eauto.
    }
    {
        invert_exec'' H11.
        {
            edestruct H; eauto.
            econstructor; eauto.

            eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

            edestruct H1; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists ((o0++o)::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            econstructor; eauto.
            intuition eauto.
            right; do 7 eexists; intuition eauto.
        }
        {
            edestruct H0; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            eexists (_::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            eapply ExecBindCrash; eauto.
        }
    }
Qed.

Lemma AOE_change_refinement:
  forall O O1 O2 
  (L: Language O)
  (L1: Language O1)
  (L2: Language O2)
  (CR1: CoreRefinement L1 O)
  (CR2: CoreRefinement L2 O)
  u T (p: L.(prog) T) rec l_grs1 l_grs2,
  let R1:= LiftRefinement L CR1 in
  let R2 := LiftRefinement L CR2 in
  ( forall sa si2 l_oi2 si2',  
  Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
recovery_exec L2 u l_oi2 si2 l_grs2
  (Simulation.Definitions.compile (LiftRefinement L CR2) p)
  (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->
  exists si1 l_oi1 si1',
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa /\
  recovery_exec L1 u l_oi1 si1 l_grs1
        (Simulation.Definitions.compile (LiftRefinement L CR1) p)
        (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1') ->

  (forall l_oi1 l_oi2 l_oa si1 si2 sa si1' si2',
    Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa ->
  recovery_exec L2 u l_oi2 si2 l_grs2
          (Simulation.Definitions.compile (LiftRefinement L CR2) p) 
          (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->  
  recovery_exec L1 u l_oi1 si1 l_grs1
    (Simulation.Definitions.compile (LiftRefinement L CR1) p)
    (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1' ->
    recovery_oracles_refine_to (LiftRefinement L CR1) u si1 p rec l_grs1 l_oi1 l_oa ->
    exists l_oa : list (oracle L),
    recovery_oracles_refine_to (LiftRefinement L CR2) u si2 p rec l_grs2 l_oi2 l_oa) ->
  
  abstract_oracles_exist_wrt R1
    R1.(Simulation.Definitions.refines) u
    p rec l_grs1 ->
  abstract_oracles_exist_wrt R2
    R2.(Simulation.Definitions.refines) u
    p rec l_grs2.
Proof.
  unfold abstract_oracles_exist_wrt; intros.
  cleanup.
  eapply_fresh H in H3; eauto; cleanup.
  eapply_fresh H1 in H5; eauto; cleanup.
  eapply H0; eauto.
Qed.



  
Lemma ATC_oracle_refines_finished:
forall T (p: AuthenticatedDisk.(prog) T) u (o : oracle' ATCCore)
s s' r,
(exists s1,
@HC_refines _ _ _ _ ATCLang 
AuthenticatedDisk
Definitions.TransactionalDiskCoreRefinement s s1) ->
exec ATCLang u o s
(ATC_Refinement.(Simulation.Definitions.compile) p) (Finished s' r) ->
(forall T (op: (TransactionToTransactionalDisk.Definitions.abs_op).(operation) T) x r s s',
exec Definitions.imp u x s
(compile_core Definitions.TransactionalDiskCoreRefinement op)
(Finished s' r) ->
(exists s1, Definitions.TransactionalDiskCoreRefinement.(Simulation.Definitions.refines_core) s s1) ->
exists grs1 t,
TransactionToTransactionalDisk.Definitions.token_refines T u 
s op grs1 x t) ->

exists oa,
oracle_refines ATCCore
AuthenticatedDiskLayer.AuthenticatedDiskOperation
ATCLang AuthenticatedDisk ATC_CoreRefinement
T u s p (fun s0 => s0) o oa.

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
  edestruct H1; eauto; cleanup.
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
forall T (p: AuthenticatedDisk.(prog) T) u (o : oracle' ATCCore)
s s',
(exists s1,
@HC_refines _ _ _ _ ATCLang 
AuthenticatedDisk
Definitions.TransactionalDiskCoreRefinement s s1) ->
exec ATCLang u o s
(ATC_Refinement.(Simulation.Definitions.compile) p) (Crashed s') ->

(forall T (op: (TransactionToTransactionalDisk.Definitions.abs_op).(operation) T) x r s s',
exec Definitions.imp u x s
(compile_core Definitions.TransactionalDiskCoreRefinement op)
(Finished s' r) ->
(exists s1, Definitions.TransactionalDiskCoreRefinement.(Simulation.Definitions.refines_core) s s1) ->
exists grs1 t,
TransactionToTransactionalDisk.Definitions.token_refines T u 
s op grs1 x t) ->

(forall T (op: (TransactionToTransactionalDisk.Definitions.abs_op).(operation) T) x s s',
exec Definitions.imp u x s
(compile_core Definitions.TransactionalDiskCoreRefinement op)
(Crashed s') ->
(exists s1, Definitions.TransactionalDiskCoreRefinement.(Simulation.Definitions.refines_core) s s1) ->
exists grs1 t,
TransactionToTransactionalDisk.Definitions.token_refines T u 
s op grs1 x t) ->

exists oa,
oracle_refines ATCCore
AuthenticatedDiskLayer.AuthenticatedDiskOperation
ATCLang AuthenticatedDisk ATC_CoreRefinement
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
  edestruct H2; eauto; cleanup.
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

Opaque Inode.get_owner File.read_inner.
Theorem ss_ATC_read:
  forall n inum off u u',
    SelfSimulation u 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FileDisk.refinement.(Simulation.Definitions.compile) (FileDiskOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros. 
    eapply SS_transfer.
    - apply ss_AD_read.
    - eapply ATC_simulation.
      apply not_init_read.
    - eapply ATC_simulation.
      apply not_init_read.
    - 
    Set Nested Proofs Allowed.
      
  

    Opaque File.read.
    Lemma ATC_AOE_read:
    forall n inum off u,
    abstract_oracles_exist_wrt ATC_Refinement
  (Simulation.Definitions.refines ATC_Refinement) u
  (Simulation.Definitions.compile FileDisk.refinement (| Read inum off |))
  (Simulation.Definitions.compile FileDisk.refinement (| Recover |))
  (ATC_reboot_list n).
  Proof.
    intros; simpl; eapply ATC_AOE_2.
    {
          intros.
      eapply ATC_oracle_refines_finished; eauto.

      clear H H0.
      Lemma TD_token_refines :
      forall (T : Type) (op : operation Definitions.abs_op T)
      (x : oracle' TransactionCacheOperation) (r0 : T)
      (s0 s'0 : Language.state' TransactionCacheOperation),
    exec Definitions.imp u x s0
      (compile_core Definitions.TransactionalDiskCoreRefinement op)
      (Finished s'0 r0) ->
    (exists s1 : Core.state Definitions.abs_op,
       refines_core Definitions.TransactionalDiskCoreRefinement s0 s1) ->
    exists
      (grs1 : state Definitions.imp -> state Definitions.imp) 
    (t : TransactionalDiskLayer.token'),
      TransactionToTransactionalDisk.Definitions.token_refines T u s0 op grs1 x t
      
      intros; cleanup; destruct op; simpl in *; repeat invert_exec.
      
      - do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        eapply Transaction.read_finished; eauto.
        
      - eapply_fresh Transaction.write_finished in H; eauto.
        split_ors; cleanup; intuition eauto;
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        + left; intuition eauto.
          unfold Transaction.transaction_rep in *; simpl in *.
          cleanup.
          inversion H1; eauto.
        
      - eapply_fresh Transaction.commit_finished in H; eauto;
        cleanup; intuition eauto;
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

      - eapply_fresh Transaction.abort_finished in H; eauto;
      cleanup; intuition eauto;
      do 2 eexists; try exact (fst s0); try exact (snd s0);
      left; do 2 eexists; intuition eauto.
      destruct s'0; simpl in *; cleanup; eauto.

      - eapply_fresh Transaction.recover_finished in H; eauto;
        cleanup; intuition eauto.
        2: {
          unfold TransactionToTransactionalDisk.Definitions.refines,
          Transaction.transaction_rep, Transaction.transaction_reboot_rep in *; simpl in *;
          cleanup; eauto.
        }
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines, 
        Transaction.transaction_rep in *; simpl in *.
        cleanup; eauto.

      - eapply_fresh Transaction.init_finished in H; eauto;
        cleanup; intuition eauto.
        do 2 eexists; try exact (fst s0); try exact (snd s0);
        left; do 2 eexists; intuition eauto.
        destruct s'0; simpl in *; cleanup; eauto.
    }

    {

    }

      simpl; intros; cleanup.

      unfold HC_refines in *; cleanup.
      simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.
      Transparent File.read.
      simpl in *.
      repeat invert_exec.
      Transparent Inode.get_owner File.read_inner.
      simpl in *. 


    }
    
    3: {

      Lemma Lift_Simulation:
      
    
      simpl; intros; cleanup.
      unfold HC_refines in *; cleanup.
      simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines in *.
      Transparent File.read.
      simpl in *.
      repeat invert_exec.

    }
      {
        simpl.
        
    
    
    simpl.
      unfold File.read, File.auth_then_exec.
      apply abstract_oracles_exist_wrt_compositional.
      {
        pose proof ATC_AOE.
        specialize H with (n:= 0).
        unfold ATC_reboot_list in *; simpl in *.
        apply H; clear H.
      }
      3: intros t; 
      destruct t;
      apply abstract_oracles_exist_wrt_compositional.
      5: {
        intros t; destruct t. destruct u1.
      apply abstract_oracles_exist_wrt_compositional.

    Opaque File.read.
    Set Nested Proofs Allowed.

    Lemma abstract_oracles_exist_wrt_compositional:
forall O (L: Language O) u l_grs T (p1: prog L T) T' (p2: T -> prog L T') rec, 
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(Simulation.Definitions.refines) u p1 rec [] ->
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(Simulation.Definitions.refines) u p1 rec l_grs ->
(forall t, abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(Simulation.Definitions.refines) u (p2 t) rec l_grs) ->
abstract_oracles_exist_wrt LiftRefinement LiftRefinement.(Simulation.Definitions.refines) u (Bind p1 p2) rec l_grs.
Proof.
    unfold abstract_oracles_exist_wrt; 
    simpl; intros;
    repeat invert_exec.
    {
        invert_exec'' H12.
        edestruct H; eauto.
        econstructor; eauto.

        eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

        edestruct H1; eauto.
        econstructor; eauto.

        simpl in *; cleanup; try intuition; simpl in *; try congruence;
        cleanup; repeat unify_execs; cleanup.
        exists [o0++o].
        simpl; split; eauto.
        repeat left.
        do 2 eexists; econstructor; eauto.
        econstructor; eauto.
        intuition eauto.
        do 4 eexists; intuition eauto. 
        right; do 3 eexists; intuition eauto.
    }
    {
        invert_exec'' H11.
        {
            edestruct H; eauto.
            econstructor; eauto.

            eapply_fresh exec_compiled_preserves_refinement_finished in H9; eauto.

            edestruct H1; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            exists ((o0++o)::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            econstructor; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            right; do 3 eexists; intuition eauto.
        }
        {
            edestruct H0; eauto.
            econstructor; eauto.

            simpl in *; cleanup; try intuition; simpl in *; try congruence;
            cleanup; repeat unify_execs; cleanup.
            eexists (_::l).
            simpl; split; eauto.
            right.
            eexists; econstructor; eauto.
            eapply ExecBindCrash; eauto.
            intuition eauto.
            do 4 eexists; intuition eauto. 
            rewrite app_nil_r; eauto.
        }
    }
    Unshelve.
    eauto.
Qed.







    Lemma AOE_read:
    forall n inum off u,
    abstract_oracles_exist_wrt ATC_Refinement
  (ATC_Refinement.(Simulation.Definitions.refines)) u
  (File.read inum off) File.recover (ATC_reboot_list n).
  Proof.
    destruct n.
    {
      unfold abstract_oracles_exist_wrt, ATC_reboot_list; simpl.
      intros.
      repeat invert_exec.
      simpl in *.
    } 
  
  
  
  eapply ATC_AOE_2.
      all: admit.
    - eapply ATC_AOE_2.
      all: admit.
    - admit. (*oracle_refines_same_from_related*)
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - admit. (* SelfSimulation_Exists *)
Abort.