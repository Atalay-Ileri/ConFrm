Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATCSimulation ATCAOE.
Require Import Not_Init ATC_ORS ATC_TS.

Import FileDiskLayer.
Set Nested Proofs Allowed.

Lemma same_for_user_except_reflexive :
forall u ex s,
same_for_user_except u ex s s.
Proof.
  unfold same_for_user_except, addrs_match_exactly; intros;
  intuition; cleanup; eauto.
Qed.


Lemma data_block_inbounds:
forall inum off s fm im dm inode,
Inode.inode_rep im s ->
File.DiskAllocator.block_allocator_rep dm s ->
File.file_map_rep fm im dm ->
im inum = Some inode ->
off < length (Inode.block_numbers inode) ->
File.DiskAllocatorParams.bitmap_addr +
S (seln (Inode.block_numbers inode) off 0) <
FSParameters.data_length.
Proof.
  intros.
  cleanup; repeat cleanup_pairs.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H2; eauto.
    cleanup.
    
      unfold Inode.inode_rep, 
      Inode.inode_map_rep,
      Inode.InodeAllocator.block_allocator_rep in *.
      cleanup.

      eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H7.
      cleanup; split_ors; cleanup; try congruence.
      rewrite H5, H10 in H2; simpl in *; congruence.

      unfold Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
      eapply_fresh H6 in H2; eauto.
      cleanup.
      unfold File.file_map_rep, File.file_rep in *; cleanup.
      eapply_fresh H14 in H2; eauto; cleanup.

      unfold File.DiskAllocator.block_allocator_rep in *.
      rewrite H5, H10 in H2; simpl in *; cleanup.

      destruct_fresh (nth_error (Inode.block_numbers (Inode.decode_inode (seln x2 inum value0))) off).
      eapply_fresh H17 in D; cleanup.
      eapply nth_error_nth with (d:= 0) in D; rewrite <- D in *.

      eapply File.DiskAllocator.valid_bits_extract with (n:= (nth off
      (Inode.block_numbers
         (Inode.decode_inode (seln x2 inum value0)))
      0)) in H18.
      cleanup; split_ors; cleanup; try congruence.
      pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
      unfold File.DiskAllocatorParams.bitmap_addr, File.DiskAllocatorParams.num_of_blocks in *. 

      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      apply PeanoNat.Nat.le_succ_l in H13.
      eapply TSCommon.lt_le_lt; eauto.
      rewrite nth_seln_eq; eauto.
      

      rewrite H19.
      eapply Forall_forall in H13.
      2: eapply nth_In; eauto.
      instantiate (1:= 0) in H13.
      pose proof File.DiskAllocatorParams.num_of_blocks_in_bounds.
      eapply PeanoNat.Nat.lt_le_trans; eauto.

      rewrite H19, value_to_bits_length. 
      apply File.DiskAllocatorParams.num_of_blocks_in_bounds.
      
      apply nth_error_None in D; lia.
      destruct (Compare_dec.lt_dec inum (length x2)); eauto.
      rewrite H5, H9 in H2; simpl in *; try congruence; try lia.

      rewrite H8, value_to_bits_length. 
      apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
Qed.


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
  Core.exec (TransactionalDiskLayer.TDCore
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
  Core.exec (TransactionalDiskLayer.TDCore
data_length) u t_abs s_abs o (Crashed s_abs') /\
  TransactionToTransactionalDisk.Definitions.refines_reboot (TransactionToTransactionalDisk.Refinement.TC_reboot_f s_imp') (TransactionToTransactionalDisk.Refinement.TD_reboot_f s_abs')) ->

exists s1',
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
    instantiate (1:= (fst x0, (_, (snd (snd x0), snd (snd x0))))).
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

Lemma txn_length_0_empty:
forall V (l: list (_ * V)),
length (addr_list_to_blocks (map fst l)) +
length (map snd l) = 0 ->
l = [].
Proof.
 intros; destruct l; eauto; simpl in *; lia.
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


Lemma ATC_ORS_read_inner:
forall n u u' inum off im1 im2,
oracle_refines_same_from_related ATC_Refinement u
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n) 
(fun s1 s2  => exists s1a s2a, 
(Inode.inode_rep im1 (fst (snd (snd s1))) /\
     (exists file_block_map : disk value,
        File.DiskAllocator.block_allocator_rep file_block_map
          (fst (snd (snd s1))) /\
        File.file_map_rep s1a im1 file_block_map)) /\
  (Inode.inode_rep im2 (fst (snd (snd s2))) /\
     (exists file_block_map : disk value,
        File.DiskAllocator.block_allocator_rep file_block_map
          (fst (snd (snd s2))) /\
        File.file_map_rep s2a im2 file_block_map)) /\
FD_related_states u' None s1a s2a).
Proof.
  intros.
  Opaque Inode.get_block_number.
  unfold File.read_inner; simpl; cleanup.
  eapply ATC_ORS_compositional;
  try solve [intros; apply ATC_ORS_recover];
  try solve [apply oracle_refines_independent_from_reboot_function].
  {
    intros; eapply  ATC_ORS_equiv_impl.
    apply ATC_ORS_get_block_number; eauto.

    intros; unfold File.files_inner_rep; cleanup;
    do 2 eexists; intuition eauto.
  }
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
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H15; eauto.
    cleanup.
    destruct r1, r2; try solve [intuition congruence].
    2: apply ATC_ORS_ret.
    simpl.
    unfold File.files_inner_rep in *; cleanup.
    eapply_fresh Inode.get_block_number_finished in H15; eauto.
    eapply_fresh Inode.get_block_number_finished in H16; eauto.
    repeat split_ors; cleanup; try congruence.
    repeat split_ors; cleanup; try congruence.
    eapply ATC_ORS_compositional;
    try solve [intros; apply ATC_ORS_recover];
    try solve [apply oracle_refines_independent_from_reboot_function].
    
    intros; eapply ATC_ORS_equiv_impl.
    apply ATC_ORS_disk_block_allocator_read.
    shelve.
    unfold File.files_inner_rep.

    instantiate (2 := (fun s1 s2  => exists s1a s2a, 
    (Inode.inode_rep im1 (fst (snd (snd s1))) /\
     (exists file_block_map : disk value,
        File.DiskAllocator.block_allocator_rep file_block_map
          (fst (snd (snd s1))) /\
        File.file_map_rep s1a im1 file_block_map)) /\
  (Inode.inode_rep im2 (fst (snd (snd s2))) /\
     (exists file_block_map : disk value,
        File.DiskAllocator.block_allocator_rep file_block_map
          (fst (snd (snd s2))) /\
        File.file_map_rep s2a im2 file_block_map)) /\
    FD_related_states u' None s1a s2a 
    )).
    intros; shelve.
    {
      intros; destruct r1, r2; apply ATC_ORS_ret.
    }
  {
    simpl in *; intros.
    unfold refines_related in *; cleanup.
    simpl in *.
    eapply_fresh ATC_exec_lift_finished in H27; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    eapply_fresh ATC_exec_lift_finished in H29; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed];
    try solve [apply not_init_read].
    cleanup.
    eapply_fresh lift2_invert_exec in H43; eauto; cleanup.
    eapply_fresh lift2_invert_exec in H44; eauto; cleanup.
    eapply_fresh ATC_oracle_refines_prefix_finished in H29; eauto.
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
  eapply ATC_exec_lift_finished in H27; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_finished in H29; eauto;
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
eapply ATC_exec_lift_crashed in H27; eauto;
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
cleanup.
eapply ATC_exec_lift_crashed in H29; eauto;
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
  eapply lift2_invert_exec in H13; eauto; cleanup.
  eapply lift2_invert_exec in H15; eauto; cleanup.
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
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H19; eauto.
    eapply Inode.get_block_number_finished in H17; eauto.
    eapply Inode.get_block_number_finished in H19; eauto.
    repeat split_ors; cleanup; try lia.
    repeat split_ors; cleanup; try lia;
    try solve [intuition congruence].
    do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    all: try solve [eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; FileInnerSpecs.solve_bounds].
    eexists; intuition eauto.
    all: try solve [eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; FileInnerSpecs.solve_bounds].
    shelve.
    (*
    clear H26 H28.
    do 2 eexists; intuition eauto.
    eexists; intuition eauto;
    eexists; intuition eauto.
    all: try solve [eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; FileInnerSpecs.solve_bounds].
    eexists; intuition eauto;
    eexists; intuition eauto.
    all: try solve [eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
    intros; FileInnerSpecs.solve_bounds].
    *)
    all: shelve.
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
all: try exact u'.
all: try solve [exact (fun _ _ => True)].
all: try solve [simpl; eauto].
all: try (eapply have_same_structure_DiskAllocator_read; eauto).
all: try (eapply have_same_structure_get_block_number; eauto).
all: try solve [eapply not_init_read_inner].

all: try solve [
unfold File.files_inner_rep in *; cleanup;
repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto].

all: repeat (simpl in *; try destruct t; simpl; eauto;
simpl; 
try match goal with 
[|- _ /\ _ ] => 
try split; intros
end).
all: try solve [eapply not_init_get_block_number].
all: try solve [eapply not_init_DiskAllocator_read].
all: try solve [
  unfold File.files_inner_rep; do 2 eexists; intuition eauto;
  eexists; intuition eauto;
  repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto].
all: try solve [
  unfold File.files_inner_rep; 
  do 2 eexists; intuition eauto;
  try (eexists; intuition eauto);
  try solve [unfold FD_related_states in *;
  apply TSCommon.same_for_user_except_symmetry; eauto];
  repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto].
  9:{
    intros.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; 
    eauto; cleanup.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; 
    eauto; cleanup.
    unfold FD_related_states, same_for_user_except in *; cleanup.
    eapply_fresh H21 in H18; eauto; cleanup.
    unfold File.file_map_rep in *; cleanup.
    eapply H24 in H; eauto.
    eapply H25 in H17; eauto.
    unfold File.file_rep in *; cleanup; eauto.
  }
  11:{
    intros.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H12; 
    eauto; cleanup.
    eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H14; 
    eauto; cleanup.
    unfold FD_related_states, same_for_user_except in *; cleanup.
    eapply_fresh H23 in H20; eauto; cleanup.
    unfold File.file_map_rep in *; cleanup.
    eapply H26 in H12; eauto.
    eapply H27 in H14; eauto.
    unfold File.file_rep in *; cleanup; eauto.
  }
  all:
  try solve [try (eapply Inode.get_block_number_finished in H11; eauto;
  eapply Inode.get_block_number_finished in H12; eauto;
  cleanup; repeat split_ors; cleanup; try congruence);
  unfold Inode.inode_rep, Inode.inode_map_rep,
  Inode.inode_map_valid,
  Inode.inode_valid in *; cleanup;
  match goal with
       | [H: ?x1 ?inum = Some _,
          H0: ?x2 ?inum = Some _,
          H1: forall _ _, 
          ?x1 _ = Some _ -> _ /\ _,
          H2: forall _ _, 
          ?x2 _ = Some _ -> _ /\ _ |- _] =>
          eapply H1 in H; eauto; cleanup;
          eapply H2 in H0; eauto; cleanup
       end;
       
  match goal with
  | [H: Forall _ (Inode.block_numbers _),
    H0: Forall _ (Inode.block_numbers _) |- _] =>
    eapply Forall_forall in H; [| eapply in_seln; eauto];
    eapply Forall_forall in H0; [| eapply in_seln; eauto]
  end;
  unfold File.DiskAllocatorParams.num_of_blocks; intuition eauto].
{
  cleanup; do 2 eexists; intuition eauto.
  repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto.
}
all: try solve [
  unfold File.files_inner_rep; do 2 eexists; intuition eauto;
  try solve [unfold FD_related_states in *;
  apply TSCommon.same_for_user_except_symmetry; eauto] ].
2: {
  clear H26 H28.
  unfold File.files_inner_rep; do 2 eexists; intuition eauto;
  eexists; intuition eauto;
  try solve [unfold FD_related_states in *;
  apply TSCommon.same_for_user_except_symmetry; eauto].
  all: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
  intros; FileInnerSpecs.solve_bounds.
}
{
  unfold File.files_inner_rep; do 2 eexists; intuition eauto.
  apply same_for_user_except_reflexive.
}
Unshelve.
all: eauto.
Qed.


Lemma ATC_ORS_explicit_inode_map:
      forall n u u' inum off, 
      (forall im1 im2,
        oracle_refines_same_from_related ATC_Refinement u
        (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
        (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
        (Simulation.Definitions.compile FD.refinement (| Recover |))
        (ATC_reboot_list n) 
        (fun s1 s2  => exists s1a s2a, 
        (Inode.inode_rep im1 (fst (snd (snd s1))) /\
            (exists file_block_map : disk value,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s1))) /\
                File.file_map_rep s1a im1 file_block_map)) /\
          (Inode.inode_rep im2 (fst (snd (snd s2))) /\
            (exists file_block_map : disk value,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s2))) /\
                File.file_map_rep s2a im2 file_block_map)) /\
        FD_related_states u' None s1a s2a)) ->

oracle_refines_same_from_related ATC_Refinement u
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(Simulation.Definitions.compile FD.refinement (| Recover |))
(ATC_reboot_list n) 
(fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a).

  Proof.
    unfold oracle_refines_same_from_related; intros.
    unfold refines_related, File.files_inner_rep in *.
    cleanup.
    eapply H; eauto.
    do 2 eexists; intuition eauto.
    do 2 eexists; intuition eauto.
  Qed.


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
      intros; eapply ATC_ORS_explicit_inode_map.
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
  rewrite <- H14, <- H12 in *. 
  clear H14 H12.
  eapply Inode.get_owner_finished in H17; eauto.
  eapply Inode.get_owner_finished in H9; eauto.
  cleanup.
  clear H9 H17.
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


Lemma get_owner_oracle_refines_exists:
     forall u (o0 : oracle' ATCCore) (s : state ATCLang)
 (s' : Language.state' ATCCore) (r : option user) inum,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
 (Simulation.Definitions.compile ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum)))
 (Finished s' r) ->
exists oa : list (Language.token' AuthenticatedDiskLayer.ADOperation),
 forall grs : state ATCLang -> state ATCLang,
 oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation ATCLang AD
   ATC_CoreRefinement (option user) u s
   (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum)) grs o0 oa.
Proof.
  intros.
  eapply ATC_oracle_refines_finished; eauto.
Qed.

Lemma get_block_number_oracle_refines_exists:
     forall u (o0 : oracle' ATCCore) (s : state ATCLang)
 (s' : Language.state' ATCCore) r inum off,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
 (Simulation.Definitions.compile ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)))
 (Finished s' r) ->
exists oa : list (Language.token' AuthenticatedDiskLayer.ADOperation),
 forall grs : state ATCLang -> state ATCLang,
 oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation ATCLang AD
   ATC_CoreRefinement _ u s
   (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)) grs o0 oa.
Proof. 
  intros.
  eapply ATC_oracle_refines_finished; eauto.
Qed.

Lemma read_inner_oracle_refines_exists:
forall u (o0 : oracle' ATCCore) (s : state ATCLang)
(s' : Language.state' ATCCore) r off inum,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
(Simulation.Definitions.compile ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
(Finished s' r) ->
exists oa : list (Language.token' AuthenticatedDiskLayer.ADOperation),
forall grs : state ATCLang -> state ATCLang,
oracle_refines ATCCore AuthenticatedDiskLayer.ADOperation ATCLang AD
ATC_CoreRefinement _ u s
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)) grs o0 oa.
Proof. 
  intros.
  eapply ATC_oracle_refines_finished; eauto.
Qed.


Lemma ATC_TS_DiskAllocator_read:
    forall n a1 a2 u u',
    (a1 < File.DiskAllocatorParams.num_of_blocks <-> a2 < File.DiskAllocatorParams.num_of_blocks) ->
    (File.DiskAllocatorParams.bitmap_addr + S a1 <
    data_length <->
    File.DiskAllocatorParams.bitmap_addr + S a2 <
    data_length) ->
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a1)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.DiskAllocator.read a2)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATC_Refinement
     AD_valid_state)
  (fun s1 s2 => refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a) s1 s2 /\
  (forall a, 
     Transaction.get_first (fst (snd s1)) a = None <-> 
     Transaction.get_first (fst (snd s2)) a = None) /\
  (Transaction.get_first (fst (snd s1)) (File.DiskAllocatorParams.bitmap_addr + S a1) = None <-> 
   Transaction.get_first (fst (snd s2)) (File.DiskAllocatorParams.bitmap_addr + S a2) = None) /\
   nth_error
            (value_to_bits
               (upd_batch (snd (snd s1)) (rev (map fst (fst (snd s1))))
               (rev (map snd (fst (snd s1)))) File.DiskAllocatorParams.bitmap_addr)) a1 =
               nth_error
            (value_to_bits
               (upd_batch (snd (snd s2)) (rev (map fst (fst (snd s2))))
               (rev (map snd (fst (snd s2)))) File.DiskAllocatorParams.bitmap_addr)) a2)
  (ATC_reboot_list n).
  Proof.
    unfold File.DiskAllocator.read; intros.
    destruct (Compare_dec.lt_dec a1 File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec a2 File.DiskAllocatorParams.num_of_blocks);
    try lia.
    2: intros; apply ATC_TS_ret.
    simpl.
    eapply ATC_TS_compositional.

    intros; eapply TS_eqv_impl.
    eapply ATC_TS_Transaction_read.
    shelve.
    intros; cleanup; eauto.
    2: intros; shelve.
    intros.
    eapply lift2_invert_exec in H1; cleanup.
    eapply lift2_invert_exec in H2; cleanup.
    unfold refines_related in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *.
    eapply Transaction.read_finished in H8; eauto.
    eapply Transaction.read_finished in H9; eauto.
    cleanup; repeat split_ors; cleanup; try lia.
    unfold Transaction.transaction_rep in *; cleanup.
    setoid_rewrite H6.
    destruct_fresh (nth_error
    (value_to_bits
       (upd_batch (snd (snd s2)) (rev (map fst (fst (snd s2))))
          (rev (map snd (fst (snd s2))))
          File.DiskAllocatorParams.bitmap_addr)) a2); setoid_rewrite D.
    2: intros; apply ATC_TS_ret.
    {
      destruct b.
      2: intros; apply ATC_TS_ret.
      eapply ATC_TS_compositional.
      2: intros; apply ATC_TS_ret.
      intros; simpl; eapply ATC_TS_Transaction_read; eauto.
      intros; shelve.
    }
    {
      edestruct (block_allocator_empty a1);
      edestruct (block_allocator_empty a2);
      cleanup; apply ATC_TS_ret.
    }
    Unshelve.
    all: try solve [ exact (fun _ _ => True)].
    all: simpl; eauto.
    all: intuition.
    unfold File.DiskAllocatorParams.bitmap_addr.
    {
      eapply lift2_invert_exec in H1; cleanup.
      eapply lift2_invert_exec in H2; cleanup.
      unfold refines_related in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *.
      eapply Transaction.read_finished in H5; eauto.
      eapply Transaction.read_finished in H12; eauto.
      cleanup; intuition.
    }
    {
      eapply lift2_invert_exec in H1; cleanup.
      eapply lift2_invert_exec in H2; cleanup.
      unfold refines_related in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *.
      eapply Transaction.read_finished in H5; eauto.
      eapply Transaction.read_finished in H12; eauto.
      cleanup; intuition.
    }
  Qed.

  Lemma ATC_TS_explicit_inode_map:
  forall n u u' inum off, 
  (forall im1 im2,
  Termination_Sensitive u
  (Simulation.Definitions.compile ATC_Refinement 
  (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Simulation.Definitions.compile ATC_Refinement
  (@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
    (Simulation.Definitions.compile ATC_Refinement File.recover)
    (refines_valid ATC_Refinement
     AD_valid_state)
     (refines_related ATC_Refinement 
     (fun s1 s2  => exists s1a s2a, 
    (Inode.inode_rep im1 (fst (snd (snd s1))) /\
        (exists file_block_map : disk value,
            File.DiskAllocator.block_allocator_rep file_block_map
              (fst (snd (snd s1))) /\
            File.file_map_rep s1a im1 file_block_map)) /\
      (Inode.inode_rep im2 (fst (snd (snd s2))) /\
        (exists file_block_map : disk value,
            File.DiskAllocator.block_allocator_rep file_block_map
              (fst (snd (snd s2))) /\
            File.file_map_rep s2a im2 file_block_map)) /\
    FD_related_states u' None s1a s2a /\
    fst (snd s1) = Empty /\
    fst (snd s2) = Empty))
    (ATC_reboot_list n)) ->


    Termination_Sensitive u
(Simulation.Definitions.compile ATC_Refinement 
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
(Simulation.Definitions.compile ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
  (Simulation.Definitions.compile ATC_Refinement File.recover)
(refines_valid ATC_Refinement
     AD_valid_state)
(refines_related ATC_Refinement
(fun s1 s2  => exists s1a s2a, 
File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
FD_related_states u' None s1a s2a /\
fst (snd s1) = Empty /\
  fst (snd s2) = Empty))
  (ATC_reboot_list n) .
Proof.
unfold Termination_Sensitive; intros.
unfold refines_related, File.files_inner_rep in *.
cleanup.
eapply H.
3: eauto.
all: eauto.
do 2 eexists; intuition eauto.
do 2 eexists; intuition eauto.
Qed.

Lemma ATC_TS_read_inner:
    forall n inum off u u',
    Termination_Sensitive u
  (Simulation.Definitions.compile
     ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.read_inner off inum)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (@lift_L2 AuthenticationOperation _ TD _
     (File.read_inner off inum)))
  (Simulation.Definitions.compile
     ATC_Refinement
     (Simulation.Definitions.compile
        FD.refinement
        (| Recover |)))
  (refines_valid ATC_Refinement
     AD_valid_state)
  (refines_related ATC_Refinement
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a /\
  fst (snd s1) = Empty /\ fst (snd s2) = Empty))
  (ATC_reboot_list n).
  Proof.
    Transparent File.read_inner.
    intros; 
    eapply ATC_TS_explicit_inode_map.
    intros; unfold File.read_inner.
    eapply ATC_TS_compositional.
    intros; eapply TS_eqv_impl.
    eapply ATC_TS_get_block_number.
    simpl; intros; shelve.
    2: intros; shelve.

    intros; unfold refines_related in *; cleanup.
      eapply_fresh get_block_number_oracle_refines_exists in H; eauto.
      eapply_fresh get_block_number_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATC_oracle_refines_impl_eq in H12; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H14;
      eapply lift2_invert_exec in H16; cleanup.
      apply map_ext_eq in H12; cleanup.
      2: intros; cleanup; intuition congruence.

      unfold File.files_inner_rep in *; cleanup.
      eapply_fresh Inode.get_block_number_finished_oracle_eq in H20; eauto; subst.
      cleanup; destruct r1, r2; try solve [intuition congruence].
      2: intros; apply ATC_TS_ret.
      
      eapply ATC_TS_compositional.
      2: intros; destruct r1, r2; apply ATC_TS_ret.
      2: intros; shelve.
      simpl; intros; repeat invert_exec; try congruence.
      eapply TS_eqv_impl. 
      eapply ATC_TS_DiskAllocator_read.
      {
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.
        cleanup; repeat split_ors; cleanup; intuition eauto.
        eapply SameRetType.all_block_numbers_in_bound in H29.
        3: eauto.
        all: eauto.
        eapply Forall_forall in H29; eauto.
        apply in_seln; eauto.

        eapply SameRetType.all_block_numbers_in_bound in H10.
        3: eauto.
        all: eauto.
        eapply Forall_forall in H10; eauto.
        apply in_seln; eauto.
      }
      {
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.

        cleanup; repeat split_ors; cleanup; intuition eauto.
      eapply data_block_inbounds; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      eapply data_block_inbounds.
      4: eauto.
      all: eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
      }
      {
        instantiate (2:= refines_related ATC_Refinement
        (fun s1 s2  => 
        exists s1a s2a, 
        (Inode.inode_rep im1 (fst (snd (snd s1))) /\
            (exists file_block_map,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s1))) /\
                File.file_map_rep s1a im1 file_block_map)) /\
          (Inode.inode_rep im2 (fst (snd (snd s2))) /\
            (exists file_block_map,
                File.DiskAllocator.block_allocator_rep file_block_map
                  (fst (snd (snd s2))) /\
                File.file_map_rep s2a im2 file_block_map)) /\
        FD_related_states u' None s1a s2a /\
        fst (snd s1) = Empty /\
        fst (snd s2) = Empty)).
         
         simpl; intros.
         unfold refines_related in *.
         cleanup.
         split.
         unfold File.files_inner_rep.
         do 2 eexists; intuition eauto.
         do 2 eexists; intuition eauto.

         simpl in *; unfold HC_refines in H12, H21; cleanup.
         simpl in *; unfold TransactionToTransactionalDisk.Definitions.refines,
         Transaction.transaction_rep  in *; cleanup; 
         repeat split_ors; cleanup; try congruence.
        eapply txn_length_0_empty in H34;
        eapply txn_length_0_empty in H38; subst.
        setoid_rewrite H34;
        setoid_rewrite H38.
        simpl; intuition eauto.

        rewrite H38, H34 in *; simpl in *.
        eapply Inode.get_block_number_finished in H20; eauto.
        eapply Inode.get_block_number_finished in H18; eauto.
        cleanup; repeat split_ors; cleanup; intuition eauto.
        repeat erewrite TSCommon.used_blocks_are_allocated_2; eauto.
      }
      shelve.
      {
        unfold File.files_inner_rep in *; cleanup. 
        do 2 eexists; intuition eauto.
      }

    Unshelve.
    all: eauto.
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      simpl in *.
      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      do 2 eexists; intuition eauto. 

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H14;
      setoid_rewrite H14.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H18;
      setoid_rewrite H18.
      simpl; eauto.
    }
    {
      simpl.
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_block_number_oracle_refines_exists in H; eauto.
      eapply_fresh get_block_number_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATC_oracle_refines_impl_eq in H12; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H14;
      eapply lift2_invert_exec in H16; cleanup.
      apply map_ext_eq in H12; cleanup.
      2: intros; cleanup; intuition congruence.
      unfold File.files_inner_rep in *; cleanup.
      eapply Inode.get_block_number_finished in H20; eauto.
      eapply Inode.get_block_number_finished in H18; eauto.
      cleanup.
      clear H12 H20.
      do 2 eexists; intuition eauto.
      do 2 eexists; intuition eauto.

      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.
      
      eexists; intuition eauto. 
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; FileInnerSpecs.solve_bounds.

      setoid_rewrite H26; eauto.
      setoid_rewrite H22; eauto.

      unfold File.files_inner_rep in *; cleanup. 
      do 2 eexists; intuition eauto.
    }
    all: try solve [exact (fun _ _ => True)].
    all: simpl; eauto.
    {
      intros.
      match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold FD_related_states,
       same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold File.file_map_rep in *; cleanup.
       match goal with
       | [H: ?x1 ?inum = Some _,
          H0: ?x2 ?inum = Some _,
          H1: forall (_: Inode.Inum) _ _, 
          ?x1 _ = Some _ ->
          _ _ = Some _ -> _,
          H2: forall (_: Inode.Inum) _ _, 
          ?x2 _ = Some _ ->
          _ _ = Some _ -> _ |- _] =>
          eapply H1 in H; eauto; cleanup;
          eapply H2 in H0; eauto; cleanup
       end.
       unfold File.file_rep in *; cleanup; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.
    Opaque File.read_inner.

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
    intros; simpl.
    eapply ATC_TS_compositional.
    {
      intros; eapply TS_eqv_impl.
      eapply ATC_TS_get_owner.
      unfold refines_related, AD_related_states; 
      simpl. unfold refines_related; simpl.
      unfold refines, File.files_rep; simpl. 
      intros; cleanup; intuition eauto.
      do 2 eexists; intuition eauto.
      rewrite H4, H6;
      do 2 eexists; intuition eauto.
      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H12;
      setoid_rewrite H12.
      simpl; eauto.

      unfold HC_refines in *; cleanup.
      simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      eapply txn_length_0_empty in H16;
      setoid_rewrite H16.
      simpl; eauto.
    }
    {
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_owner_oracle_refines_exists in H; eauto.
      eapply_fresh get_owner_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATC_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H6;
      eapply lift2_invert_exec in H8; cleanup.
      apply map_ext_eq in H4; cleanup.
      2: intros; cleanup; intuition congruence.

      eapply_fresh get_owner_related_ret_eq in H10; eauto; subst.
      destruct r2.
      2: intros; apply ATC_TS_abort_then_ret.
      
      eapply ATC_TS_compositional.
      intros; apply ATC_TS_auth.
      2: shelve.
      simpl; intros; repeat invert_exec; try congruence.
      2: intros; apply ATC_TS_abort_then_ret.
      eapply ATC_TS_compositional.
      intros; eapply ATC_TS_read_inner.
      intros.
      {
        instantiate (1:= refines_related ATC_Refinement
        (fun s3 s4 : state AD =>
         exists s1a s2a : disk File,
           File.files_inner_rep s1a (fst (snd (snd s3))) /\
           File.files_inner_rep s2a (fst (snd (snd s4))) /\
           FD_related_states u' None s1a s2a /\
           fst (snd s3) = Empty /\ fst (snd s4) = Empty)) in H13; simpl in *; cleanup.
        unfold refines_related, FD_related_states in *; simpl in *; cleanup.

      eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
      eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.

      eapply lift2_invert_exec in H22;
      eapply lift2_invert_exec in H24; cleanup.
      
      eapply ATC_oracle_refines_prefix_finished in H21.
      2: apply H20.
      all: simpl in *; eauto.
      2: apply TD_oracle_refines_operation_eq.
      apply map_ext_eq in H21; cleanup.
      2: intros; cleanup; intuition congruence.
      eapply SameRetType.read_inner_finished_oracle_eq in H27.
      2: apply H29.
      all: eauto.
      cleanup.
      destruct r1, r2; try solve [intuition congruence].
      intros; apply ATC_TS_commit_then_ret.
      intros; apply ATC_TS_abort_then_ret.
      eapply have_same_structure_read_inner; eauto.
      do 2 eexists; intuition eauto.
      unfold FD_related_states; 
      apply TSCommon.same_for_user_except_symmetry; eauto.
      apply not_init_read_inner.
      apply not_init_read_inner.
      }
      intros; shelve.
    }
    intros; shelve.
    Unshelve.
    all: try exact u'.
    all: eauto.
    all: try solve [exact (fun _ _ => True)].
    all: try solve [simpl; eauto].
    {
      simpl; intros;
      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      repeat invert_exec; destruct s0, s3; simpl in *; eauto;
        do 2 eexists; intuition eauto;
        do 2 eexists; intuition eauto.
    }
    2:{
      intros; unfold refines_related in *; cleanup.
      eapply_fresh get_owner_oracle_refines_exists in H; eauto.
      eapply_fresh get_owner_oracle_refines_exists in H0; eauto.
      cleanup.

      eapply_fresh ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      eapply ATC_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_owner; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.

      eapply lift2_invert_exec in H6;
      eapply lift2_invert_exec in H8; cleanup.
      apply map_ext_eq in H4; cleanup.
      2: intros; cleanup; intuition congruence.
      do 2 eexists; intuition eauto.

      unfold AD_related_states, refines_related in *; 
      cleanup; simpl in *.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.

      eapply Inode.get_owner_finished in H12; eauto.
      2: rewrite H17; eauto.
      eapply Inode.get_owner_finished in H10; eauto.
      2: rewrite H13; eauto.
      cleanup.

      clear H10 H12. (* clear ors*)
      do 2 eexists; intuition eauto;
      eexists; intuition eauto;
      eexists; intuition eauto.
      all:eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto;
      intros; FileInnerSpecs.solve_bounds.
    }
    {
      simpl.
      unfold refines_related, FD_related_states in *; simpl in *; cleanup.

      eapply_fresh read_inner_oracle_refines_exists in H4; eauto.
      eapply_fresh read_inner_oracle_refines_exists in H6; eauto.
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.

      eapply lift2_invert_exec in H29;
      eapply lift2_invert_exec in H31; cleanup.

      eapply FileInnerSpecs.read_inner_finished in H34; eauto.
      eapply FileInnerSpecs.read_inner_finished in H36; eauto.
      cleanup.

      unfold HC_refines in *; cleanup; simpl in *.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; logic_clean.
      
      clear H48 H52.
      repeat split; intros.
      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H37; eauto.

      eapply Forall_forall; intros.
      apply Transaction.dedup_last_in in H52.
      apply in_rev in H52.
      eapply Forall_forall in H38; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s2'0)))))
             (l2:= (rev (map snd (fst (snd s2'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s2'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H47.
      apply PeanoNat.Nat.add_le_mono; eauto.

      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst (fst (snd s1'0)))))
             (l2:= (rev (map snd (fst (snd s1'0))))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst (fst (snd s1'0))))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H88.
      eapply PeanoNat.Nat.le_trans.
      2: apply H51.
      apply PeanoNat.Nat.add_le_mono; eauto.
    }
    Unshelve.
    all: eauto.
  Qed.

Opaque Inode.get_owner File.read_inner.
Theorem ss_ATC_read:
  forall n inum off u u',
    SelfSimulation u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
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
      - apply ATC_TS_read.
Qed.
      