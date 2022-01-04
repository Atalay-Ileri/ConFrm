Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATC_ORS ATCDLayer ATC_Simulation HSS ATC_TransferProofs.
Require Import ATCD_Simulation ATCD_AOE.
Require Import Not_Init ATCD_ORS ATCD_TS.

Import FileDiskLayer.
Set Nested Proofs Allowed.


Ltac destruct_and_split:=
match goal with
| [|- context [match ?x with | _ => _ end ] ] =>
  destruct x
end.


Lemma TIE_auth_then_exec:
    forall T (p1 p2: addr -> TD.(prog) (option T)) inum s1 s2 u ex,
    (forall s1 s2,
    refines_related ATC_Refinement (fun s1 s2  => exists s1a s2a, 
    fst (snd s1) = Empty /\
    fst (snd s2) = Empty /\
    File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
    File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
    FD_related_states u ex s1a s2a) s1 s2 ->
    transaction_input_equiv (lift_L2 AuthenticationOperation (p1 inum)) (lift_L2 AuthenticationOperation (p2 inum)) s1 s2) ->
    
    refines_related ATC_Refinement (AD_related_states u ex) s1 s2 ->
    transaction_input_equiv (File.auth_then_exec inum p1) (File.auth_then_exec inum p2) s1 s2.
    Proof.
      unfold  refines_related, File.auth_then_exec in *; simpl; intuition eauto; cleanup.
      {
        Transparent Inode.get_owner.
        unfold Inode.get_owner; simpl; intuition eauto.
  
        unfold Inode.InodeAllocator.read; simpl; intuition eauto.
      destruct (Compare_dec.lt_dec inum
      Inode.InodeAllocatorParams.num_of_blocks);
      destruct (Compare_dec.lt_dec inum
      Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
      
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s0; simpl in *; try lia; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s0; simpl in *; try lia; eauto.
      }
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_lift2; cleanup.
      eapply Transaction.read_finished in H8; eauto.
      eapply Transaction.read_finished in H10; eauto.
      cleanup. clear H10 H11.
      destruct (nth_error (value_to_bits r1) inum);
      destruct (nth_error (value_to_bits r2) inum);
      simpl; intuition eauto.
      destruct b, b0; simpl; intuition eauto.
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s0; simpl in *; try lia; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s0; simpl in *; try lia; eauto.
      }
      destruct b; simpl; intuition eauto.
      all: repeat destruct_and_split; simpl; eauto.
      Opaque Inode.get_owner.
    }
    repeat destruct_and_split; simpl; eauto.
    all: simpl; intuition eauto.
    all: repeat destruct_and_split; simpl; intuition eauto.
    all: repeat destruct_and_split; simpl; intuition eauto.
    
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto; cleanup.
    eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H2; eauto; cleanup.
    
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H1; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H2; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.

    eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H8; eauto.
    2: eapply have_same_structure_get_owner; eauto.
    2: apply TD_oracle_refines_operation_eq.
    cleanup.

    repeat invert_lift2.
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply Inode.get_owner_finished in H14; eauto.
    eapply Inode.get_owner_finished in H16; eauto.
    cleanup; repeat split_ors; cleanup.
    simpl in *.
    repeat invert_exec; try congruence.

    eapply H; eauto.
    do 2 eexists; intuition eauto.
    do 2 eexists; intuition eauto.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
    [| intros; FileInnerSpecs.solve_bounds ]; eauto.
    eexists; intuition eauto.
    eexists; intuition eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
    [| intros; FileInnerSpecs.solve_bounds ]; eauto.

    destruct p1; simpl; intuition eauto.
    destruct o1; eauto.
  Unshelve.
  all: eauto.
    Qed.

    Lemma TIE_read_inner:
    forall off inum u s0 s3,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u None s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.read_inner off inum)) s0 s3.
Proof.
      Transparent File.read_inner.  
      unfold refines_related, File.read_inner; simpl; intuition eauto; cleanup.
      {
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number.
        simpl; intuition eauto.
        unfold Inode.InodeAllocator.read; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
    
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
      }
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_lift2; cleanup.
      eapply Transaction.read_finished in H11; eauto.
      eapply Transaction.read_finished in H13; eauto.
      cleanup. clear H13 H14.
      destruct (nth_error (value_to_bits r1) inum);
      destruct (nth_error (value_to_bits r2) inum);
      simpl; intuition eauto.
      destruct b, b0; simpl; intuition eauto.
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s1; simpl in *; try lia; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s1; simpl in *; try lia; eauto.
      }
      destruct b; simpl; intuition eauto.
      all: repeat destruct_and_split; simpl; eauto.
      Opaque Inode.get_block_number.
    }
    repeat destruct_and_split; simpl; intuition eauto.
    {
      repeat cleanup_pairs.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0; eauto; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto; cleanup.
      
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
  
      eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_lift2.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply Inode.get_block_number_finished in H13; eauto.
      eapply Inode.get_block_number_finished in H15; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.
      {
        clear H H2.
        unfold File.DiskAllocator.read; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec
    (seln (Inode.block_numbers x3) off 0)
    File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec
    (seln (Inode.block_numbers x4) off 0)
    File.DiskAllocatorParams.num_of_blocks); simpl; intuition eauto.
    
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s2; simpl in *; try lia; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s2; simpl in *; try lia; eauto.
    }
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_lift2; cleanup.
      eapply Transaction.read_finished in H11; eauto.
      eapply Transaction.read_finished in H24; eauto.
      cleanup. clear H24 H25.
      destruct (nth_error (value_to_bits r1) (seln (Inode.block_numbers x3) off 0));
      destruct (nth_error (value_to_bits r2) (seln (Inode.block_numbers x4) off 0));
      simpl; intuition eauto.
      destruct b, b0; simpl; intuition eauto.
      {
        eapply data_block_inbounds.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      {
        eapply data_block_inbounds.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s2; simpl in *; try lia; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s2; simpl in *; try lia; eauto.
      }
      destruct b; simpl; intuition eauto.
    }
  }
  repeat destruct_and_split; simpl; eauto.
  Unshelve.
  all: eauto.
Qed.


Lemma TIE_write_inner:
    forall off inum u s0 s3 v,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u None s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v inum)) s0 s3.
Proof.
      Transparent File.write_inner.  
      unfold refines_related, File.write_inner; simpl; intuition eauto; cleanup.
      {
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number.
        simpl; intuition eauto.
        unfold Inode.InodeAllocator.read; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
    
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
    }
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_lift2; cleanup.
    eapply Transaction.read_finished in H11; eauto.
    eapply Transaction.read_finished in H13; eauto.
    cleanup. clear H13 H14.
    destruct (nth_error (value_to_bits r1) inum);
    destruct (nth_error (value_to_bits r2) inum);
    simpl; intuition eauto.
    destruct b, b0; simpl; intuition eauto.
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s1; simpl in *; try lia; eauto.
    }
    destruct b; simpl; intuition eauto.
    all: repeat destruct_and_split; simpl; eauto.
    Opaque Inode.get_block_number.
  }
    repeat destruct_and_split; simpl; intuition eauto.
    {
      repeat cleanup_pairs.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0; eauto; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H1; eauto; cleanup.
      
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
  
      eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H4; eauto.
      2: eapply have_same_structure_get_block_number; eauto.
      2: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_lift2.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply Inode.get_block_number_finished in H13; eauto.
      eapply Inode.get_block_number_finished in H15; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.
      {
        clear H H2.
        unfold File.DiskAllocator.write; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec
    (seln (Inode.block_numbers x3) off 0)
    File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec
    (seln (Inode.block_numbers x4) off 0)
    File.DiskAllocatorParams.num_of_blocks); simpl; intuition eauto.
    
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s2; simpl in *; try lia; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in *; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s2; simpl in *; try lia; eauto.
    }
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_lift2; cleanup.
      eapply Transaction.read_finished in H11; eauto.
      eapply Transaction.read_finished in H24; eauto.
      cleanup. clear H24 H25.
      destruct (nth_error (value_to_bits r1) (seln (Inode.block_numbers x3) off 0));
      destruct (nth_error (value_to_bits r2) (seln (Inode.block_numbers x4) off 0));
      simpl; intuition eauto.
      destruct b, b0; simpl; intuition eauto.
      {
        eapply data_block_inbounds.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      {
        eapply data_block_inbounds.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s2; simpl in *; try lia; eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s, s2; simpl in *; try lia; eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
      }
      destruct b; simpl; intuition eauto.
    }
  }
  unfold File.DiskAllocator.write;
  repeat destruct_and_split; simpl; eauto.
  Unshelve.
  all: eauto.
Qed.


Lemma TIE_create:
    forall u' s1 s2 v,
refines_related ATC_Refinement
  (AD_related_states u' None) s1 s2 ->
transaction_input_equiv
(File.create v) (File.create v) s1 s2.
Proof.
Transparent File.create.  
unfold refines_related, File.create; simpl; intuition eauto; cleanup.
{
  Transparent Inode.alloc.
  unfold Inode.alloc.
  simpl; intuition eauto.
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s0; simpl in *; try lia; eauto.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s0; simpl in *; try lia; eauto.
  }
  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_lift2; cleanup.
  eapply Transaction.read_finished in H7; eauto.
  eapply Transaction.read_finished in H9; eauto.
  cleanup.

  destruct_fresh (Compare_dec.lt_dec
  (get_first_zero_index
      (firstn
        Inode.InodeAllocatorParams.num_of_blocks
        (value_to_bits r1)))
  Inode.InodeAllocatorParams.num_of_blocks);
  destruct_fresh (Compare_dec.lt_dec
  (get_first_zero_index
      (firstn
        Inode.InodeAllocatorParams.num_of_blocks
        (value_to_bits r2)))
  Inode.InodeAllocatorParams.num_of_blocks);
  simpl; eauto. 
  FileSpecs.hide H9.
  FileSpecs.hide H10.
  intuition eauto; try lia.
  cleanup.
  {
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
    unfold Inode.InodeAllocatorParams.bitmap_addr,
    Inode.InodeAllocatorParams.num_of_blocks in *; lia.
  }
  {
    pose proof Inode.InodeAllocatorParams.blocks_fit_in_disk.
    unfold Inode.InodeAllocatorParams.bitmap_addr,
    Inode.InodeAllocatorParams.num_of_blocks in *; lia.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s0; simpl in *; try lia; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s0; simpl in *; try lia; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
  }

  repeat cleanup_pairs.
  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_lift2; cleanup.
  eapply Transaction.write_finished in H2; eauto.
  eapply Transaction.write_finished in H8; eauto.
  cleanup.
  FileSpecs.hide H2.
  FileSpecs.hide H8.

  unfold AD_related_states, refines_related in *; simpl in *; cleanup.
  unfold refines, File.files_rep in *; simpl in *; cleanup.
  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines,
  Transaction.transaction_rep in H4, H5; simpl in *; cleanup.
  repeat split_ors; cleanup; try congruence.
  repeat cleanup_pairs.
  destruct s, s1; simpl in *; try lia; eauto.

  FileSpecs.reveal H2.
  FileSpecs.reveal H8.
  repeat split_ors; cleanup; try lia; simpl in *; eauto.

  intuition eauto; try solve [
  erewrite addr_list_to_blocks_length_eq; eauto].
  repeat destruct_and_split; simpl; intuition eauto.
}
repeat destruct_and_split; simpl; intuition eauto.
Qed.

Lemma TIE_extend_inner:
    forall inum u s0 s3 v,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u None s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v inum)) s0 s3.
Proof.
  Transparent File.extend_inner.  
  Opaque File.DiskAllocator.alloc.
  unfold refines_related, File.extend_inner; simpl; intuition eauto; cleanup.
{
  Transparent File.DiskAllocator.alloc.
  simpl; intuition eauto.
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s1; simpl in *; try lia; eauto.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s1; simpl in *; try lia; eauto.
  }

  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_lift2; cleanup.
  eapply Transaction.read_finished in H11; eauto.
  eapply Transaction.read_finished in H13; eauto.
  cleanup. clear H13 H14.
  destruct (Compare_dec.lt_dec
  (get_first_zero_index
    (firstn
        File.DiskAllocatorParams.num_of_blocks
        (value_to_bits r1)))
  File.DiskAllocatorParams.num_of_blocks);
  destruct (Compare_dec.lt_dec
  (get_first_zero_index
    (firstn
        File.DiskAllocatorParams.num_of_blocks
        (value_to_bits r2)))
  File.DiskAllocatorParams.num_of_blocks);
  simpl; intuition eauto.
  {
    pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
    unfold File.DiskAllocatorParams.bitmap_addr,
    File.DiskAllocatorParams.num_of_blocks in *.
    lia.
  }
  {
    pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
    unfold File.DiskAllocatorParams.bitmap_addr,
    File.DiskAllocatorParams.num_of_blocks in *.
    lia.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s1; simpl in *; try lia; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
  }
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s1; simpl in *; try lia; eauto.
    erewrite addr_list_to_blocks_length_eq; eauto.
  }
  repeat cleanup_pairs; simpl in *.

  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_lift2; cleanup.
  eapply Transaction.write_finished in H1; eauto.
  eapply Transaction.write_finished in H10; eauto.
  unfold AD_related_states, refines_related in *; simpl in *; cleanup.
  unfold refines, File.files_rep in *; simpl in *; cleanup.
  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines,
  Transaction.transaction_rep in *; simpl in *; cleanup.
  FileSpecs.hide H1.
  FileSpecs.hide H10.
  repeat split_ors; cleanup; try congruence.
  repeat cleanup_pairs.
  destruct s, s4; simpl in *; try lia; eauto.
  FileSpecs.reveal H1.
  FileSpecs.reveal H10.
  cleanup.
  {
    repeat (repeat split_ors; cleanup; try congruence); simpl in *; eauto.
    simpl; intuition eauto; 
    try solve [erewrite addr_list_to_blocks_length_eq; eauto].
    repeat destruct_and_split; simpl; intuition eauto.
  }
}
repeat destruct_and_split; simpl; intuition eauto.
{
   (***********)
   unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    unfold File.DiskAllocator.alloc in *; simpl in *.
    repeat invert_exec_no_match;
    eapply Transaction.read_finished in H12; eauto;
    eapply Transaction.read_finished in H15; eauto;
    cleanup; try lia; repeat cleanup_pairs;
    repeat (simpl in *; repeat invert_exec_no_match; cleanup).
    {
      simpl in *.
      clear H16 H17.
      eapply Transaction.write_finished in H2; eauto;
      eapply Transaction.write_finished in H10; eauto;
      cleanup; try lia; repeat cleanup_pairs;
      repeat split_ors; cleanup; try congruence.
      eapply Transaction.write_finished in H3; eauto;
      eapply Transaction.write_finished in H12; eauto;
      cleanup; try lia; repeat cleanup_pairs;
      repeat split_ors; cleanup; try congruence.
      
      unfold TransactionToTransactionalDisk.Definitions.refines,
      Transaction.transaction_rep in H8, H9; simpl in *; cleanup.
      repeat split_ors; cleanup; try congruence.
      repeat cleanup_pairs.
      destruct s, s2; simpl in *; try lia; eauto.
      {
        Transparent Inode.extend.
        Opaque Inode.get_inode.
        unfold Inode.extend; simpl; intuition.
        {
          Transparent Inode.get_inode.
          simpl; intuition.
          unfold Inode.InodeAllocator.read; simpl; intuition eauto.
          destruct (Compare_dec.lt_dec inum
          Inode.InodeAllocatorParams.num_of_blocks);
          destruct (Compare_dec.lt_dec inum
          Inode.InodeAllocatorParams.num_of_blocks); 
          simpl; intuition eauto.
          cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S
            (get_first_zero_index
                (firstn File.DiskAllocatorParams.num_of_blocks
                  (value_to_bits x6))))); eauto.
          shelve.
          cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S
            (get_first_zero_index
                (firstn File.DiskAllocatorParams.num_of_blocks
                  (value_to_bits x11))))); eauto.
          shelve.
        
          {
            unfold HC_refines in *; simpl in *; cleanup.
            unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
            repeat invert_lift2; cleanup.
            eapply Transaction.read_finished in H16; eauto.
            eapply Transaction.read_finished in H19; eauto.
            cleanup. clear H19 H20.
            destruct (nth_error (value_to_bits r1) inum);
            destruct (nth_error (value_to_bits r2) inum);
            simpl; intuition eauto.
            destruct b, b0; simpl; intuition eauto.
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              destruct (addr_eq_dec
              (Inode.InodeAllocatorParams.bitmap_addr + S inum)
              (File.DiskAllocatorParams.bitmap_addr +
              S
                (get_first_zero_index
                    (firstn
                      File.DiskAllocatorParams.num_of_blocks
                      (value_to_bits x6))))); eauto.
              shelve.
            }
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              destruct (addr_eq_dec
              (Inode.InodeAllocatorParams.bitmap_addr + S inum)
              (File.DiskAllocatorParams.bitmap_addr +
              S
                (get_first_zero_index
                    (firstn
                      File.DiskAllocatorParams.num_of_blocks
                      (value_to_bits x11))))); eauto.
              shelve.
            }
            destruct b; simpl; intuition eauto.
            
          }
          repeat destruct_and_split; simpl; eauto.
        }
        {
          repeat destruct_and_split; simpl; eauto.
          unfold Inode.get_inode in *; simpl in *;
          repeat (repeat invert_exec; simpl in *; cleanup).
          unfold Inode.InodeAllocator.read in *; simpl in *;
          repeat (repeat invert_exec; simpl in *; cleanup).
          eapply Transaction.read_finished in H21; eauto.
          eapply Transaction.read_finished in H18; eauto.
          cleanup. clear H18 H22.
          eapply Transaction.read_finished in H8; eauto.
          eapply Transaction.read_finished in H19; eauto.
          cleanup. clear H19 H22.
          repeat cleanup_pairs.
          unfold Inode.set_inode; simpl; intuition eauto.
          unfold Inode.InodeAllocator.write; simpl; intuition eauto.
          destruct (Compare_dec.lt_dec inum
          Inode.InodeAllocatorParams.num_of_blocks); try lia.
          simpl; intuition eauto.
          {
            cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S
            (get_first_zero_index
                (firstn File.DiskAllocatorParams.num_of_blocks
                  (value_to_bits x6))))); eauto.
          shelve.
          }
          {
          cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S
            (get_first_zero_index
                (firstn File.DiskAllocatorParams.num_of_blocks
                  (value_to_bits x11))))); eauto.
          shelve.
          }
          unfold HC_refines in *; simpl in *; cleanup.
            unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
            repeat invert_lift2; cleanup.
            eapply Transaction.read_finished in H16; eauto.
            eapply Transaction.read_finished in H19; eauto.
            cleanup. clear H19 H21.
            destruct (nth_error (value_to_bits r1) inum);
            destruct (nth_error (value_to_bits r2) inum);
            simpl; intuition eauto.
            destruct b, b0; simpl; intuition eauto.
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              erewrite addr_list_to_blocks_length_eq; eauto.
            }
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              erewrite addr_list_to_blocks_length_eq; eauto.
            }
            destruct b; simpl; intuition eauto.
            {
              unfold Inode.set_inode; simpl; intuition eauto.
              unfold Inode.InodeAllocator.write; simpl; intuition eauto.
              destruct (Compare_dec.lt_dec inum
              Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
            }
          }
        }
      }
    }
    {
      unfold Inode.extend; simpl; intuition eauto.
    }
    Unshelve.
    all:
      unfold Inode.InodeAllocatorParams.bitmap_addr,
      File.DiskAllocatorParams.bitmap_addr,
      Inode.InodeAllocatorParams.num_of_blocks in *;
      pose proof inodes_before_data; try lia.
Qed.