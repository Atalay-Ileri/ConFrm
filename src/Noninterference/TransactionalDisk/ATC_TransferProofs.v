Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCLayer FileDisk.TransferProofs ATC_Simulation ATC_AOE.
Require Import Not_Init HSS ATC_ORS. (* ATC_TS. *)

Import FileDiskLayer.
Set Nested Proofs Allowed.


Opaque Inode.get_owner File.read_inner.
Theorem ss_ATC_read:
  forall n inum off u u',
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Read inum off)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_read.
      - eapply ATC_simulation.
        apply not_init_read.
      - eapply ATC_simulation.
        apply not_init_read.
      - apply ATC_AOE.
      apply not_init_read.
      - apply ATC_AOE.
      apply not_init_read.
      - apply ATC_ORS_transfer.
        apply not_init_read.
        apply not_init_read.
        apply have_same_structure_read.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.


Theorem ss_ATC_write:
  forall n inum off u u' v,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_write.
      - eapply ATC_simulation.
        apply not_init_write.
      - eapply ATC_simulation.
        apply not_init_write.
      - apply ATC_AOE.
        apply not_init_write.
      - apply ATC_AOE.
        apply not_init_write.
      - apply ATC_ORS_transfer.
        apply not_init_write.
        apply not_init_write.
        intros; eapply have_same_structure_write; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.

Theorem ss_ATC_write_input:
  forall n inum off u u' v1 v2,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v1)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Write inum off v2)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' (Some inum)))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_write_input.
      - eapply ATC_simulation.
        apply not_init_write.
      - eapply ATC_simulation.
        apply not_init_write.
      - apply ATC_AOE.
        apply not_init_write.
      - apply ATC_AOE.
        apply not_init_write.
      - apply ATC_ORS_transfer.
        apply not_init_write.
        apply not_init_write.
        intros; eapply have_same_structure_write_input; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.


Theorem ss_ATC_extend:
  forall n inum u u' v,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_extend.
      - eapply ATC_simulation.
        apply not_init_extend.
      - eapply ATC_simulation.
        apply not_init_extend.
      - apply ATC_AOE.
        apply not_init_extend.
      - apply ATC_AOE.
        apply not_init_extend.
      - apply ATC_ORS_transfer.
        apply not_init_extend.
        apply not_init_extend.
        intros; eapply have_same_structure_extend; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.

Theorem ss_ATC_extend_input:
  forall n inum u u' v1 v2,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v1)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Extend inum v2)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' (Some inum)))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_extend_input.
      - eapply ATC_simulation.
        apply not_init_extend.
      - eapply ATC_simulation.
        apply not_init_extend.
      - apply ATC_AOE.
        apply not_init_extend.
      - apply ATC_AOE.
        apply not_init_extend.
      - apply ATC_ORS_transfer.
        apply not_init_extend.
        apply not_init_extend.
        intros; eapply have_same_structure_extend_input; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.


Theorem ss_ATC_change_owner:
  forall n inum u u' v,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (ChangeOwner inum v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (ChangeOwner inum v)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' (Some inum)))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_change_owner.
      - eapply ATC_simulation.
        apply not_init_change_owner.
      - eapply ATC_simulation.
        apply not_init_change_owner.
      - apply ATC_AOE.
        apply not_init_change_owner.
      - apply ATC_AOE.
        apply not_init_change_owner.
      - apply ATC_ORS_transfer.
        apply not_init_change_owner.
        apply not_init_change_owner.
        intros; eapply have_same_structure_change_owner; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.

Theorem ss_ATC_create:
  forall n u u' o,
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Create o)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Create o)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_create.
      - eapply ATC_simulation.
        apply not_init_create.
      - eapply ATC_simulation.
        apply not_init_create.
      - apply ATC_AOE.
        apply not_init_create.
      - apply ATC_AOE.
        apply not_init_create.
      - apply ATC_ORS_transfer.
        apply not_init_create.
        apply not_init_create.
        intros; eapply have_same_structure_create; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.




Theorem ss_ATC_delete:
  forall n inum u u',
    RDNI_Weak u
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Delete inum)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) (Delete inum)))) 
    (ATC_Refinement.(Simulation.Definitions.compile) (FD.refinement.(Simulation.Definitions.compile) (FDOp.(Op) Recover))) 
    (refines_valid ATC_Refinement AD_valid_state)
    (refines_related ATC_Refinement
     (AD_related_states u' None))
    (eq u') (ATC_reboot_list n).
Proof.
    intros.
    eapply RDNIW_transfer.
      - apply ss_AD_delete.
      - eapply ATC_simulation.
        apply not_init_delete.
      - eapply ATC_simulation.
        apply not_init_delete.
      - apply ATC_AOE.
        apply not_init_delete.
      - apply ATC_AOE.
        apply not_init_delete.
      - apply ATC_ORS_transfer.
        apply not_init_delete.
        apply not_init_delete.
        intros; eapply have_same_structure_delete; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
      - unfold exec_compiled_preserves_validity, AD_valid_state, 
      refines_valid, FD_valid_state; 
      intros; simpl; eauto.
Qed.

(*
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
      eapply lt_le_lt; eauto.
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


Theorem exec_with_recovery_termination_sensitive_bind:
  forall O (L: Layer O) 
  T (p1 p2: L.(prog) T) 
  T' (p3 p4: T -> L.(prog) T') rec s1 s2 
  lob l_grs u s1',
  (forall s1' lo lgrs, 
  exec_with_recovery L u lo s1 lgrs p1 rec s1' ->
   exists s2',
   exec_with_recovery L u lo s2 lgrs p2 rec s2') ->

  (forall s1' s2' s1r t1 t2 lo lo' lgrs, 
  exec_with_recovery L u lo s1 [] p1 rec (RFinished s1' t1) ->
  exec_with_recovery L u lo s2 [] p2 rec (RFinished s2' t2) ->
    
  exec_with_recovery L u lo' s1' lgrs (p3 t1) rec s1r ->
  exists s2r,
  exec_with_recovery L u lo' s2' lgrs (p4 t2) rec s2r) ->

  exec_with_recovery L u lob s1 l_grs (Bind p1 p3) rec s1' ->
   exists s2',
   exec_with_recovery L u lob s2 l_grs (Bind p2 p4) rec s2'.
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
 (L_imp: Layer C_imp)
 (L_abs: Layer C_abs)
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
  (L: Layer O)
  (L1: Layer O1)
  (L2: Layer O2)
  (CR1: CoreRefinement L1 O)
  (CR2: CoreRefinement L2 O)
  u T (p: L.(prog) T) rec l_grs1 l_grs2,
  let R1:= LiftRefinement L CR1 in
  let R2 := LiftRefinement L CR2 in
  ( forall sa si2 l_oi2 si2',  
  Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
exec_with_recovery L2 u l_oi2 si2 l_grs2
  (Simulation.Definitions.compile (LiftRefinement L CR2) p)
  (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->
  exists si1 l_oi1 si1',
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa /\
  exec_with_recovery L1 u l_oi1 si1 l_grs1
        (Simulation.Definitions.compile (LiftRefinement L CR1) p)
        (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1') ->

  (forall l_oi1 l_oi2 l_oa si1 si2 sa si1' si2',
    Simulation.Definitions.refines (LiftRefinement L CR2) si2 sa ->
  Simulation.Definitions.refines (LiftRefinement L CR1) si1 sa ->
  exec_with_recovery L2 u l_oi2 si2 l_grs2
          (Simulation.Definitions.compile (LiftRefinement L CR2) p) 
          (Simulation.Definitions.compile (LiftRefinement L CR2) rec) si2' ->  
  exec_with_recovery L1 u l_oi1 si1 l_grs1
    (Simulation.Definitions.compile (LiftRefinement L CR1) p)
    (Simulation.Definitions.compile (LiftRefinement L CR1) rec) si1' ->
    recovery_oracles_refine (LiftRefinement L CR1) u si1 p rec l_grs1 l_oi1 l_oa ->
    exists l_oa : list (oracle L),
    recovery_oracles_refine (LiftRefinement L CR2) u si2 p rec l_grs2 l_oi2 l_oa) ->
  
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

Opaque File.read File.recover.

Lemma txn_length_0_empty:
forall V (l: list (_ * V)),
length (addr_list_to_blocks (map fst l)) +
length (map snd l) = 0 ->
l = [].
Proof.
 intros; destruct l; eauto; simpl in *; lia.
Qed.


Lemma get_owner_oracle_refines_exists:
     forall u (o0 : oracle' ATCCore) (s : state ATCLang)
 (s' : LayerImplementation.state' ATCCore) (r : option user) inum,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
 (Simulation.Definitions.compile ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_owner inum)))
 (Finished s' r) ->
exists oa : list (Layer.token' AuthenticatedDiskLayer.ADOperation),
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
 (s' : LayerImplementation.state' ATCCore) r inum off,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
 (Simulation.Definitions.compile ATC_Refinement
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.get_block_number inum off)))
 (Finished s' r) ->
exists oa : list (Layer.token' AuthenticatedDiskLayer.ADOperation),
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
(s' : LayerImplementation.state' ATCCore) r off inum,
(exists s3 : state AD, Simulation.Definitions.refines ATC_Refinement s s3) ->
exec ATCLang u o0 s
(Simulation.Definitions.compile ATC_Refinement
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)))
(Finished s' r) ->
exists oa : list (Layer.token' AuthenticatedDiskLayer.ADOperation),
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
*)
