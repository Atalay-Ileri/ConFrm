Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATCSimulation ATCAOE.
Require Import Not_Init ATC_ORS.

Import FileDiskLayer.
Set Nested Proofs Allowed.


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


Lemma ATC_simulation_crash:
forall u inum off (o : oracle' ATCCore) (s : state ATCLang)
  (s' : Language.state' ATCCore),
(exists s1 : state AD,
   Simulation.Definitions.refines ATC_Refinement s s1) ->
exec ATCLang u o s
  (Simulation.Definitions.compile ATC_Refinement
     (Simulation.Definitions.compile FD.refinement
        (| Read inum off |))) (Crashed s') ->

          
  (forall T o s_imp s_imp' s_abs r o_imp t_abs grs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Finished s_imp' r) ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o grs o_imp t_abs ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TDOperation
data_length) u t_abs s_abs o (Finished s_abs' r) /\
  TransactionToTransactionalDisk.Definitions.refines s_imp' s_abs') ->
  
  (forall T o s_imp s_imp' s_abs o_imp t_abs, 
  exec Definitions.imp u o_imp s_imp
  (TransactionToTransactionalDisk.Definitions.compile
      T o) (Crashed s_imp') ->
  TransactionToTransactionalDisk.Definitions.refines s_imp s_abs ->
  TransactionToTransactionalDisk.Definitions.token_refines
  T u s_imp o TransactionToTransactionalDisk.Refinement.TC_reboot_f o_imp t_abs ->
  (forall l, ~ eq_dep Type (operation Definitions.abs_op) T o unit (TransactionalDiskLayer.Init l)) ->
  exists s_abs',
  Core.exec (TransactionalDiskLayer.TDOperation
data_length) u t_abs s_abs o (Crashed s_abs') /\
  TransactionToTransactionalDisk.Definitions.refines_reboot (TransactionToTransactionalDisk.Refinement.TC_reboot_f s_imp') (TransactionToTransactionalDisk.Refinement.TD_reboot_f s_abs')) ->

exists s1' : total_mem * total_mem,
  TransactionToTransactionalDisk.Definitions.refines_reboot
    (snd s') s1'.
    Proof.
      intros; cleanup.
      eapply_fresh ATC_oracle_refines_crashed in H0; eauto.
      cleanup.
      eapply ATC_exec_lift_crashed in H0; eauto.
      cleanup; simpl in *.
      unfold TransactionToTransactionalDisk.Refinement.TC_reboot_f, 
      TransactionToTransactionalDisk.Refinement.TD_reboot_f in *; simpl in *.
      eexists; unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
      Transaction.transaction_reboot_rep  in ; simpl in *; eauto.
      apply not_init_read.
      simpl in *; eauto.
      apply not_init_read.
    Qed.



  Lemma ATC_AOE_read:
  forall n inum off u,
  abstract_oracles_exist_wrt ATC_Refinement
(Simulation.Definitions.refines ATC_Refinement) u
(Simulation.Definitions.compile FD.refinement (| Read inum off |))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n).
Proof.
  intros; eapply ATC_AOE_2.
  {
    intros.
    eapply ATC_oracle_refines_finished; eauto.
  }
  {
    intros.
    eapply ATC_oracle_refines_crashed; eauto.
    apply not_init_read.
  }
  {
    intros;
    eapply ATC_simulation_crash; eauto.
    apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto.
    eapply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed; eauto.
  }
Qed.

Opaque File.read File.recover.
Lemma ROR_transfer_recovery:
forall l_o_imp l_o_abs n u s1_imp x, 
recovery_oracles_refine_to ATC_Refinement u s1_imp 
File.recover File.recover (ATC_reboot_list n) l_o_imp l_o_abs ->
TransactionToTransactionalDisk.Definitions.refines_reboot (snd s1_imp) (snd x) ->
fst s1_imp = fst x ->
exists l_o_abs',
recovery_oracles_refine_to FD.refinement u x 
(| Recover |) (| Recover |) (authenticated_disk_reboot_list n)
l_o_abs l_o_abs'.
Proof.
  induction l_o_imp; simpl; intros; intuition.
  destruct l_o_abs; intuition.
  {
    simpl in *; cleanup.
    eapply ATC_exec_lift_finished_recovery in H; eauto; cleanup.
    eexists [_].
    simpl; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
    destruct x1; eauto.
    eapply FileSpecs.recover_finished in H; eauto.
  }
  {
    cleanup; intuition.
    unfold ATC_reboot_list in *; 
    destruct n; simpl in *; try congruence.
    cleanup.

    edestruct IHl_o_imp; eauto.
    instantiate (1:= (fst x0, (snd (snd x0), snd(snd x0)))).
    all: simpl; eauto.
    
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep   in *; simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
    Transaction.transaction_reboot_rep; eauto.
    cleanup.
    simpl in *.
    eapply_fresh ATC_exec_lift_crashed_recovery in H; eauto; cleanup.

    eexists (_::_); simpl.
    intuition eauto.
    eapply recovery_oracles_refine_to_length in H5; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    right; eexists; intuition eauto.
    eapply FileSpecs.recover_crashed in H6; eauto.
    unfold TransactionToTransactionalDisk.Definitions.refines_reboot,
    Transaction.transaction_reboot_rep  in *; 
    setoid_rewrite <- H8.
    setoid_rewrite H7; eauto.
  }
  Unshelve.
  all: eauto.
Qed.

(* Need to figure out oracles instead of exists *)
Lemma ROR_transfer:
forall l_o_imp l_o_abs n u s1_imp x inum off , 
recovery_oracles_refine_to ATC_Refinement u s1_imp 
(File.read inum off) File.recover (ATC_reboot_list n) l_o_imp l_o_abs ->
TransactionToTransactionalDisk.Definitions.refines (snd s1_imp) (snd x) ->
fst s1_imp = fst x ->
exists l_o_abs',
recovery_oracles_refine_to FD.refinement u x 
(| Read inum off |) (| Recover |) (authenticated_disk_reboot_list n)
l_o_abs l_o_abs'.
Proof.
  induction l_o_imp; simpl; intros; intuition.
  
  destruct l_o_abs; intuition.
  {
    simpl in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto.
    2: simpl; unfold HC_refines; eauto.
    cleanup.
    eexists [_].
    simpl; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eapply FileSpecs.read_finished in H; cleanup; eauto.
    simpl.
    
    apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto.
  }
  {
    cleanup; intuition.
    unfold ATC_reboot_list in *; 
    destruct n; simpl in *; try congruence.
    cleanup.

    eapply ATC_exec_lift_crashed in H; eauto; cleanup.
    eapply ROR_transfer_recovery in H4; eauto.
    cleanup.
    eexists (_::_).
    simpl; intuition eauto.
    eapply recovery_oracles_refine_to_length in H4; eauto.
    right; eexists; intuition eauto.
    eexists; intuition eauto.
    right; eexists; intuition eauto.
    eapply FileSpecs.read_crashed in H; eauto.
    simpl; unfold HC_refines; eauto.
    apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto.
    apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed; eauto.
    apply not_init_read.
  }
  Unshelve.
  all: eauto.
Qed.


Lemma get_owner_related_ret_eq:
forall u u' ex s1 s2 o s1' s2' r1 r2 inum, 
AD_related_states u' ex s1 s2 ->
exec TD u o (snd s1) (Inode.get_owner inum) (Finished s1' r1) ->
exec TD u o (snd s2) (Inode.get_owner inum) (Finished s2' r2) ->
r1 = r2.
Proof.
  unfold AD_related_states, refines_related, FD_related_states; simpl;
  intros; cleanup.
  unfold refines, File.files_rep, File.files_inner_rep in *.
  cleanup.
  rewrite <- H, <- H2 in *.
  eapply Inode.get_owner_finished in H0; eauto.
  eapply Inode.get_owner_finished in H1; eauto.
  cleanup; repeat split_ors; cleanup; try lia; eauto.
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H16; eauto.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto.
    cleanup.
    unfold File.file_map_rep in *; cleanup.
    eapply H18 in H16; eauto.
    eapply H19 in H17; eauto.
    destruct H3; cleanup.
    eapply H21 in H0; eauto; cleanup.
    unfold File.file_rep in *; cleanup; eauto.
  }
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H16; eauto.
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in H17; eauto.
    cleanup.
    destruct H3; cleanup.
    edestruct H1. 
    exfalso; eapply H20; eauto. congruence.
  }
  {
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto.
    eapply_fresh FileInnerSpecs.inode_missing_then_file_missing in H16 ; eauto.
    cleanup.
    destruct H3; cleanup.
    edestruct H1. 
    exfalso; eapply H19; eauto. congruence.
  }
Qed.


Lemma ATC_ORS_read_inner:
forall n u u' inum off,
oracle_refines_same_from_related ATC_Refinement u
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n) 
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd s1)) /\ 
File.files_inner_rep s2a (fst (snd s2)) /\ 
FD_related_states u' None s1a s2a).
Proof.
  intros.
  Opaque Inode.get_block_number.
  unfold File.read_inner; simpl.
  eapply ATC_ORS_compositional;
  try solve [intros; apply ATC_ORS_recover];
  try solve [apply oracle_refines_independent_from_reboot_function].
  intros; apply ATC_ORS_get_block_number; eauto.
  {
    intros.
    unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply lift2_invert_exec in H; eauto; cleanup.
    eapply lift2_invert_exec in H0; eauto; cleanup.
    eapply map_ext_eq in H; subst; 
    [| intros; cleanup; intuition congruence].
    unfold File.files_inner_rep in *; cleanup.
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H11; eauto.
    cleanup.
    destruct r1, r2; try solve [intuition congruence].
    2: apply ATC_ORS_ret.
    simpl.
    eapply ATC_ORS_compositional;
    try solve [intros; apply ATC_ORS_recover];
    try solve [apply oracle_refines_independent_from_reboot_function].

    unfold File.files_inner_rep in *; cleanup.
    eapply_fresh Inode.get_block_number_finished in H11; eauto.
    eapply_fresh Inode.get_block_number_finished in H12; eauto.
    repeat split_ors; cleanup; try congruence.
    repeat split_ors; cleanup; try congruence.
    intros; apply ATC_ORS_disk_block_allocator_read.
    shelve.
    
    {
      intros; destruct r1, r2; apply ATC_ORS_ret.
    }
  {
    simpl in *; intros.
    unfold refines_related in *; cleanup.
    simpl in *.
    eapply_fresh ATC_exec_lift_finished in H16; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATC_exec_lift_finished in H18; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply_fresh lift2_invert_exec in H27; eauto; cleanup.
    eapply_fresh lift2_invert_exec in H28; eauto; cleanup.
    eapply_fresh ATC_oracle_refines_prefix_finished in H19; eauto.
  {
    apply map_ext_eq in Hx; subst.
    2: intros; cleanup; intuition congruence.
    eapply ATC_oracle_refines_impl_eq; eauto.
    2: apply TD_oracle_refines_operation_eq.
    (* eapply have_same_structure_DiskAllocator_read; eauto. *)
    shelve.
    }
    apply TD_oracle_refines_operation_eq.
    (* eapply have_same_structure_DiskAllocator_read; eauto.
    apply not_init_DiskAllocator_read. 
    apply not_init_DiskAllocator_read. *)
    all: shelve.
  }
  {
  intros; unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_finished in H16; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_finished in H18; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  repeat invert_exec; try lia;
  simpl in *; cleanup; 
  repeat split_ors; cleanup; try congruence;
  do 2 eexists; intuition eauto.
  all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  (*
  eapply have_same_structure_get_owner; eauto.
  apply not_init_get_owner.
  apply not_init_get_owner.
  *)
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  (*
  eapply have_same_structure_get_owner; eauto.
  unfold AD_related_states, refines_related in *; cleanup; eauto.
  do 2 eexists; intuition eauto.
  unfold FD_related_states in *.
  apply TSCommon.same_for_user_except_symmetry; eauto.
  apply not_init_get_owner.
  apply not_init_get_owner.
  *)
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_crashed in H16; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_crashed in H18; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
unfold refines_related_reboot; simpl in *.
unfold HC_refines_reboot; simpl.
do 2 eexists; repeat (split; eauto).
all: shelve.
}
shelve.
}
{
intros; unfold refines_related in *; cleanup.
  eapply_fresh ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
  try solve [apply not_init_read].
  cleanup.
  eapply lift2_invert_exec in H9; eauto; cleanup.
  eapply lift2_invert_exec in H11; eauto; cleanup.
  simpl in *.
  eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
  {
    apply map_ext_eq in Hx; subst.
    2: intros; cleanup; intuition congruence.
    eapply ATC_oracle_refines_impl_eq; eauto.
    2: apply TD_oracle_refines_operation_eq.
    (* eapply have_same_structure_get_owner; eauto. *)
    shelve.
    }
    apply TD_oracle_refines_operation_eq.
    (*
    eapply have_same_structure_get_owner; eauto.
    unfold AD_related_states, refines_related in *; cleanup; eauto.
    do 2 eexists; intuition eauto.
    unfold FD_related_states in *.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_get_owner.
    apply not_init_get_owner.
    *)
    all: shelve.
}
{
  intros; unfold refines_related in *; cleanup.
  eapply_fresh ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  repeat invert_exec; try lia;
  simpl in *; cleanup; 
  repeat split_ors; cleanup; try congruence;
  do 2 eexists; intuition eauto.

  eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
  2: apply TD_oracle_refines_operation_eq.
  {
    apply map_ext_eq in Hx; subst.
    2: intros; cleanup; intuition congruence.
    unfold File.files_inner_rep in *; cleanup.
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H15; eauto.
    eapply Inode.get_block_number_finished in H13; eauto.
    eapply Inode.get_block_number_finished in H15; eauto.
    repeat split_ors; cleanup; try lia.
    repeat split_ors; cleanup; try lia;
    try solve [intuition congruence];
    do 2 eexists; intuition eauto;
    eexists; intuition eauto;
    eexists; intuition eauto.
    all: try solve [eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; FileInnerSpecs.solve_bounds].
    shelve.
    }
    all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_crashed in H; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_crashed in H0; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
unfold refines_related_reboot; simpl in *.
unfold HC_refines_reboot; simpl.
do 2 eexists; repeat (split; eauto).
all: shelve.
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: try solve [simpl; eauto].
all: try eapply have_same_structure_DiskAllocator_read; eauto.
all: try eapply have_same_structure_get_block_number; eauto.
all: try solve [eapply not_init_read_inner].
all: repeat (simpl in *; try destruct t; simpl; eauto;
simpl; 
try match goal with 
[|- _ /\ _ ] => 
try split; intros
end).
all: try solve [eapply not_init_get_block_number].
all: try solve [eapply not_init_DiskAllocator_read].
all: try solve [do 2 eexists; intuition eauto].
all: try solve [
  do 2 eexists; intuition eauto;
  unfold FD_related_states in *;
  apply TSCommon.same_for_user_except_symmetry; eauto].
6:{
  intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H16; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; 
     eauto; cleanup.
     unfold FD_related_states, same_for_user_except in *; cleanup.
     eapply_fresh H21 in H18; eauto; cleanup.
     unfold File.file_map_rep in *; cleanup.
     eapply H24 in H16; eauto.
     eapply H25 in H17; eauto.
     unfold File.file_rep in *; cleanup; eauto.
}
6:{
  intros.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H18; 
     eauto; cleanup.
     eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H19; 
     eauto; cleanup.
     unfold FD_related_states, same_for_user_except in *; cleanup.
     eapply_fresh H23 in H20; eauto; cleanup.
     unfold File.file_map_rep in *; cleanup.
     eapply H26 in H18; eauto.
     eapply H27 in H19; eauto.
     unfold File.file_rep in *; cleanup; eauto.
}
Admitted.


Lemma ATC_ORS_read:
forall n u u' inum off,
oracle_refines_same_from_related ATC_Refinement u
(Simulation.Definitions.compile FD.refinement (| Read inum off |))
(Simulation.Definitions.compile FD.refinement (| Read inum off |))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n) (AD_related_states u' None).
Proof.
  intros.
  Transparent File.read.
  Opaque File.read_inner.
  unfold File.read, File.auth_then_exec.
  eapply ATC_ORS_compositional;
  try solve [intros; apply ATC_ORS_recover];
  try solve [apply oracle_refines_independent_from_reboot_function].
  intros; apply ATC_ORS_get_owner.
  {
  intros.
  unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
  try solve [apply not_init_read].
  eapply ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
  try solve [apply not_init_read].
  cleanup.
  eapply lift2_invert_exec in H; eauto; cleanup.
  eapply lift2_invert_exec in H0; eauto; cleanup.
  eapply map_ext_eq in H; subst; 
  [| intros; cleanup; intuition congruence].
  eapply_fresh Inode.get_owner_finished_oracle_eq in H9; eauto.
  cleanup.
  destruct r1, r2; try solve [intuition congruence].
  2: apply ATC_ORS_abort_then_ret.
  simpl.
  eapply ATC_ORS_compositional;
  try solve [intros; apply ATC_ORS_recover];
  try solve [apply oracle_refines_independent_from_reboot_function].
  intros; apply ATC_ORS_auth.
  {
    clear H2 H3.
    eapply get_owner_related_ret_eq in H10; eauto; cleanup.
    intros; simpl in *; cleanup; repeat invert_exec.
    invert_exec'' H; invert_exec'' H2; 
    repeat invert_exec; try congruence.
    2: apply ATC_ORS_abort_then_ret.
    {
      eapply ATC_ORS_compositional;
      try solve [intros; apply ATC_ORS_recover];
      try solve [apply oracle_refines_independent_from_reboot_function].
      intros; eapply ATC_ORS_read_inner.
      {
       intros.
       unfold refines_related in *; cleanup.
       eapply_fresh ATC_exec_lift_finished in H; eauto;
       try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
       try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
       eapply_fresh ATC_exec_lift_finished in H2; eauto;
       try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
       try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
       cleanup.
       eapply lift2_invert_exec in H14; eauto; cleanup.
       eapply lift2_invert_exec in H15; eauto; cleanup.
       eapply map_ext_eq in H14; subst; 
        [| intros; cleanup; intuition congruence].
        assume (A: (r1 = None <-> r2 = None)).
        destruct r1, r2; try solve [intuition congruence].
        2: apply ATC_ORS_abort_then_ret.
        eapply ATC_ORS_commit_then_ret.
      }
      {
intros; unfold refines_related in *; cleanup.
  eapply_fresh ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh ATC_exec_lift_finished in H2; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
  try solve [apply not_init_read].
  cleanup.
  eapply_fresh lift2_invert_exec in H14; eauto; cleanup.
  eapply_fresh lift2_invert_exec in H23; eauto; cleanup.
  simpl in *.
  eapply_fresh ATC_oracle_refines_prefix_finished in H10; eauto.
  {
    apply map_ext_eq in Hx; subst.
    2: intros; cleanup; intuition congruence.
    eapply ATC_oracle_refines_impl_eq; eauto.
    2: apply TD_oracle_refines_operation_eq.
    shelve.
  }
    apply TD_oracle_refines_operation_eq.
    all: shelve.
}
{
  intros; unfold refines_related in *; cleanup.
  eapply_fresh ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh ATC_exec_lift_finished in H2; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh lift2_invert_exec in H14; eauto; cleanup.
  eapply_fresh lift2_invert_exec in H19; eauto; cleanup.
  eapply FileInnerSpecs.read_inner_finished in H23; eauto.
  eapply FileInnerSpecs.read_inner_finished in H25; eauto.
  instantiate (1:= u') in H18.
  instantiate (1:= u').
  repeat invert_exec; try lia;
  simpl in *; cleanup; 
  repeat split_ors; cleanup; try congruence;
  do 2 eexists; intuition eauto.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  4: rewrite <- app_assoc; eauto.
  all: shelve.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_crashed in H; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_crashed in H2; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
unfold refines_related_reboot; simpl in *.
unfold HC_refines_reboot; simpl.
do 2 eexists; repeat (split; eauto).
all: shelve.
}
    }
    
  }
  {
    intros; repeat invert_exec.
    intros; unfold refines_related in *; cleanup.
      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H12; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
      try solve [apply not_init_read].
      cleanup.
      repeat invert_exec;
      simpl in *; cleanup; eauto.
    }
    {
      intros; unfold refines_related in *; cleanup.
      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H12; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      repeat invert_exec; try lia;
      simpl in *; cleanup; 
      repeat split_ors; cleanup; try congruence;
      do 2 eexists; intuition eauto.
      all: apply H17.
    }
    {
      unfold not; intros.
      unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_crashed in H15; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      repeat invert_exec;
      simpl in *; cleanup;
      simpl in *; congruence.
      simpl; eauto.
    }
    {
      unfold not; intros.
      unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_crashed in H15; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      repeat invert_exec;
      simpl in *; cleanup;
      simpl in *; congruence.
      simpl; eauto.
    }
    {
    intros; unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_crashed in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply ATC_exec_lift_crashed in H12; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    unfold refines_related_reboot; simpl in *.
    unfold HC_refines_reboot; simpl.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
    }
  }
{
intros; unfold refines_related in *; cleanup.
  eapply_fresh ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply_fresh ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
  try solve [apply not_init_read].
  cleanup.
  eapply_fresh lift2_invert_exec in H7; eauto; cleanup.
  eapply_fresh lift2_invert_exec in H9; eauto; cleanup.
  simpl in *.
  eapply_fresh ATC_oracle_refines_prefix_finished in H1; eauto.
  {
    apply map_ext_eq in Hx; subst.
    2: intros; cleanup; intuition congruence.
    eapply ATC_oracle_refines_impl_eq; eauto.
    2: apply TD_oracle_refines_operation_eq.
    eapply have_same_structure_get_owner; eauto.
    }
    apply TD_oracle_refines_operation_eq.
    eapply have_same_structure_get_owner; eauto.
    unfold AD_related_states, refines_related in *; cleanup; eauto.
    do 2 eexists; intuition eauto.
    unfold FD_related_states in *.
    apply TSCommon.same_for_user_except_symmetry; eauto.
    apply not_init_get_owner.
    apply not_init_get_owner.
}
{
  intros; unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_finished in H; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  unfold AD_related_states, refines_related in *;
  simpl in *; unfold refines, File.files_rep in *.
  repeat invert_exec; try lia;
  simpl in *; cleanup; 
  repeat split_ors; cleanup; try congruence;
  do 2 eexists; intuition eauto.
  all: shelve.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  eapply have_same_structure_get_owner; eauto.
  apply not_init_get_owner.
  apply not_init_get_owner.
  rewrite <- app_assoc; eauto.
}
{
  unfold not; intros.
  unfold refines_related in *; cleanup.
  simpl in *.
  eapply ATC_oracle_refines_prefix_one_crashed. 
  3: eauto.
  3: eauto.
  all: eauto.
  eapply have_same_structure_get_owner; eauto.
  unfold AD_related_states, refines_related in *; cleanup; eauto.
  do 2 eexists; intuition eauto.
  unfold FD_related_states in *.
  apply TSCommon.same_for_user_except_symmetry; eauto.
  apply not_init_get_owner.
  apply not_init_get_owner.
  rewrite <- app_assoc; eauto.
}
{
intros; unfold refines_related in *; cleanup.
eapply ATC_exec_lift_crashed in H; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_crashed in H0; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
unfold refines_related_reboot; simpl in *.
unfold HC_refines_reboot; simpl.
do 2 eexists; repeat (split; eauto).
all: shelve.
}
Unshelve.
all: try solve [exact (fun _ _ => True)].
all: try solve [simpl; eauto].
all: repeat (simpl in *; try destruct t; simpl; eauto;
simpl; 
try match goal with 
[|- _ /\ _ ] => 
try split; intros
end).
all: repeat (simpl in *; try destruct u3; try destruct u1;
simpl; eauto;
simpl; 
try match goal with 
[|- _ /\ _ ] => 
try split; intros
end).
all: repeat (simpl in *; try destruct t; simpl; eauto;
simpl; 
try match goal with 
[|- _ /\ _ ] => 
try split; intros
end).
all: try solve [eapply not_init_read_inner].
all: try solve [ 
  unfold not; intros; 
  repeat match goal with 
| [H: eq_dep _ _ _ _ _ _ |- _] =>
inversion H
end].
all: try solve [eapply not_init_get_owner].
all: try eapply have_same_structure_read_inner; eauto.
all: try solve [
  do 2 eexists; intuition eauto;
  unfold FD_related_states in *;
  apply TSCommon.same_for_user_except_symmetry; eauto].
{
  eapply SameRetType.read_inner_finished_oracle_eq in H23; eauto.
  cleanup; eauto.
  intuition eauto.
  unfold FD_related_states in *; eauto.
  apply TSCommon.same_for_user_except_symmetry; eauto.
}
{
  unfold File.files_inner_rep in *; cleanup.
  rewrite <- H5, <- H10 in *. 
  clear H5 H10.
  eapply Inode.get_owner_finished in H15; eauto.
  eapply Inode.get_owner_finished in H9; eauto.
  cleanup.
  clear H5 H15.
  do 2 eexists; intuition eauto;
  eexists; intuition eauto;
  eexists; intuition eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq;
  eauto; intros; FileInnerSpecs.solve_bounds.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq;
  eauto; intros; FileInnerSpecs.solve_bounds.
}
Unshelve.
eauto.  
Qed.

Opaque Inode.get_owner File.read_inner.
Theorem ss_ATC_read:
  forall n inum off u u',
    SelfSimulation u 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
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
    - apply ATC_AOE_read.
    - apply ATC_AOE_read.
    - apply ATC_ORS_read.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - unfold exec_compiled_preserves_validity, AD_valid_state, 
    refines_valid, FD_valid_state; 
    intros; simpl; eauto.
    - 

    Lemma ATC_TS_recovery:
    forall n u u',
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
  (refines_related_reboot _ _ _ _ ATC_Refinement
     (AD_related_states u' None))
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
      Opaque File.recover.
      intros.
      repeat invert_exec.
      unfold refines_related_reboot,
      AD_related_states, refines_related,
      FD_related_states in *; logic_clean.
      edestruct AOE_recover.
      eexists; eapply H1.
      {
        instantiate (2:= S n).
        unfold ATC_reboot_list; simpl.
        econstructor.
        apply H12.
        eauto.
      }
      simpl in *; cleanup; try tauto.
      split_ors; cleanup; repeat unify_execs; cleanup.

      eapply_fresh ATC_exec_lift_crashed in H12; eauto.
      cleanup.
      eapply FileSpecs.recover_crashed in H7.
      (*
      invert_exec'' H12; repeat invert_exec.
      invert_exec'' H11; repeat invert_exec.
      invert_exec'' H8; repeat invert_exec.
      *)
      simpl in *.
      edestruct IHn. 
      3: eauto.
      unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      unfold AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
    do 2 eexists; intuition eauto.
    simpl in *.
    unfold HC_refines_reboot in *; cleanup.
    simpl; intuition eauto.

    simpl in *.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    intuition eauto.
    (*doable*) admit.
    pose proof (FileInnerSpecs.addr_list_to_blocks_length []).
    }

      edestruct ATC_AOE_recover.
      2: instantiate (4 := 0);
      unfold ATC_reboot_list; simpl; econstructor; eauto.
      eauto.
      simpl in *; cleanup; intuition; cleanup; 
      repeat unify_execs; cleanup.
      eapply_fresh ATC_exec_lift_finished in H9; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].
      cleanup.
      Transparent File.read.
      unfold File.read, File.auth_then_exec in *.
      repeat invert_exec_no_match.
      invert_exec'' H9.
      simpl in *; split_ors; cleanup_no_match;
      repeat unify_execs_prefix; repeat unify_execs; cleanup_no_match.
      eapply exec_finished_deterministic_prefix in H9; eauto; cleanup_no_match.


      eapply_fresh ATC_exec_lift_crashed in e; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].

      eapply lift2_invert_exec in H15; cleanup_no_match.

      unfold refines_related in *; cleanup_no_match.
      simpl Simulation.Definitions.refines in *.
      unfold refines, File.files_rep, File.files_inner_rep in *;
      logic_clean.
      eapply Inode.get_owner_finished in H11; eauto.
      cleanup_no_match;
      split_ors; cleanup_no_match.
    }


    Lemma ATC_TS_read:
    forall n inum off u u',
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Read inum off |)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Read inum off |)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATC_Refinement
     AD_valid_state)
  (refines_related ATC_Refinement
     (AD_related_states u' None))
  (ATC_reboot_list n).
  Proof.
    unfold Termination_Sensitive, ATC_reboot_list;
    intros; destruct n.
    {
      repeat invert_exec.
      unfold refines_related, AD_related_states, refines_valid in *;
      cleanup.

      edestruct ATC_AOE_read.
      2: instantiate (4 := 0);
      unfold ATC_reboot_list; simpl; econstructor; eauto.
      eauto.
      simpl in *; cleanup; intuition; cleanup; 
      repeat unify_execs; cleanup.
      eapply_fresh ATC_exec_lift_finished in H9; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].
      cleanup.
      Transparent File.read.
      unfold File.read, File.auth_then_exec in *.
      repeat invert_exec_no_match.
      invert_exec'' H9.
      simpl in *; split_ors; cleanup_no_match;
      repeat unify_execs_prefix; repeat unify_execs; cleanup_no_match.
      eapply exec_finished_deterministic_prefix in H9; eauto; cleanup_no_match.


      eapply_fresh ATC_exec_lift_crashed in e; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].

      eapply lift2_invert_exec in H15; cleanup_no_match.

      unfold refines_related in *; cleanup_no_match.
      simpl Simulation.Definitions.refines in *.
      unfold refines, File.files_rep, File.files_inner_rep in *;
      logic_clean.
      eapply Inode.get_owner_finished in H11; eauto.
      cleanup_no_match;
      split_ors; cleanup_no_match.




      
      edestruct Noninterference.FD.TS.TSRead.Termination_Sensitive_read.
      4: eauto.
      all: eauto.
      instantiate (4:= 0);
      unfold authenticated_disk_reboot_list; 
      simpl; econstructor; eauto.
      invert_exec.
      Transparent File.read.
      unfold File.read, File.auth_then_exec in *.
      repeat invert_exec_no_match.
      invert_exec'' H9.
      simpl in *; split_ors; cleanup_no_match;
      repeat unify_execs_prefix; repeat unify_execs; cleanup_no_match.
      unify_execs_prefix.
      eapply_fresh ATC_exec_lift_crashed in e; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].

      eapply lift2_invert_exec in H15; cleanup_no_match.

      unfold refines_related in *; cleanup_no_match.
      simpl Simulation.Definitions.refines in *.
      unfold refines, File.files_rep, File.files_inner_rep in *;
      logic_clean.
      eapply Inode.get_owner_finished in H11; eauto.
      cleanup_no_match;
      split_ors; cleanup_no_match.

      eexists (RFinished _ _).
      econstructor.
      simpl in *;
      split_ors; cleanup_no_match.
      eapply_fresh ATC_exec_lift_crashed in e; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished; eauto].

      econstructor.
      


      admit.
    }
    {
      repeat invert_exec.
    }

    
    
    admit. (* Termination_Sensitive *)
Abort.