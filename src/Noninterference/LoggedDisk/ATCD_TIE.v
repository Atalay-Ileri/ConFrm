Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATC_ORS ATCDLayer ATC_Simulation HSS ATC_TransferProofs.
Require Import ATCD_Simulation ATCD_AOE.
Require Import Not_Init ATCD_ORS. (* ATCD_TS. *)

Import FileDiskLayer.
Set Nested Proofs Allowed.


Ltac destruct_and_split:=
match goal with
| [|- context [match ?x with | _ => _ end ] ] =>
  destruct x
end.

Ltac solve_get_first:=
  unfold AD_related_states, refines_related in *; simpl in *; cleanup;
  unfold refines, File.files_rep in *; simpl in *; cleanup;
  unfold HC_refines in *; simpl in *; cleanup;
  unfold TransactionToTransactionalDisk.Definitions.refines,
  Transaction.transaction_rep in *; simpl in *; cleanup;
  repeat split_ors; cleanup; try congruence;
  repeat cleanup_pairs;
  match goal with
  | [|- Transaction.get_first ?s _ = _ ] =>
    destruct s; simpl in *; try lia; eauto
  end.



Fixpoint transaction_input_equiv 
{T1 T2} 
(p1: AD.(prog) T1) (p2: AD.(prog) T2) 
(s1 s2: ATCLang.(state)) :=
match p1, p2 with
| Op _ o1, Op _ o2 =>
  match o1, o2 with
  | P2 (TransactionalDiskLayer.Read a1), 
    P2 (TransactionalDiskLayer.Read a2) =>
    (a1 < data_length <-> a2 < data_length) /\
    (Transaction.get_first (fst (snd s1)) a1 = None <->
    Transaction.get_first (fst (snd s2)) a2 = None)

  | P2 (TransactionalDiskLayer.Write a1 v1), 
    P2 (TransactionalDiskLayer.Write a2 v2) =>
    (a1 < data_length <-> a2 < data_length) /\
  ((length (addr_list_to_blocks (map fst (fst (snd s1)) ++ [a1])) +
  length (map snd (fst (snd s1)) ++ [v1])) <= log_length <->
  (length (addr_list_to_blocks (map fst (fst (snd s2)) ++ [a2])) +
            length (map snd (fst (snd s2)) ++ [v2])) <= log_length)
  | _, _ => True
  end

|Bind p1 p3, Bind p2 p4 =>
transaction_input_equiv p1 p2 s1 s2 /\
(forall s1' s2' r1 r2 u o,
exec ATCLang u o s1 (ATC_Refinement.(Simulation.Definitions.compile) p1) (Finished s1' r1) ->
exec ATCLang u o s2 (ATC_Refinement.(Simulation.Definitions.compile) p2) (Finished s2' r2) ->
transaction_input_equiv (p3 r1) (p4 r2) s1' s2' 
)

| _, _ => True
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
      solve_get_first.
      solve_get_first.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_exec; cleanup.
      eapply Transaction.read_finished in H8; eauto.
      eapply Transaction.read_finished in H10; eauto.
      cleanup. clear H10 H11.
      destruct (test_bit inum (value_to_bits r1));
      destruct (test_bit inum (value_to_bits r2));
      simpl; intuition eauto.
      solve_get_first.
      solve_get_first.
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

    repeat invert_exec; cleanup.
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
    repeat cleanup_pairs.
    eapply Inode.get_owner_finished in H11; eauto.
    eapply Inode.get_owner_finished in H14; eauto.
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
    solve_get_first.
    solve_get_first.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_exec; cleanup.
      eapply Transaction.read_finished in H11; eauto.
      eapply Transaction.read_finished in H13; eauto.
      cleanup. clear H13 H14.
      destruct (test_bit inum (value_to_bits r1));
      destruct (test_bit inum (value_to_bits r2));
      simpl; intuition eauto.
      solve_get_first.
      solve_get_first.
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
      2: eapply have_same_structure_get_block_number; simpl; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
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
    solve_get_first.
    solve_get_first.
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_exec; cleanup.
      eapply Transaction.read_finished in H11; eauto.
      eapply Transaction.read_finished in H24; eauto.
      cleanup. clear H24 H25.
      destruct (test_bit (seln (Inode.block_numbers x3) off 0) (value_to_bits r1) );
      destruct (test_bit (seln (Inode.block_numbers x4) off 0) (value_to_bits r2) );
      simpl; intuition eauto.
      {
        eapply BlockAllocatorExistence.data_block_inbounds_2.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      {
        eapply BlockAllocatorExistence.data_block_inbounds_2.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      }
      solve_get_first.
      solve_get_first.
    }
    unfold File.files_inner_rep, 
    FD_related_states, same_for_user_except,
    File.file_map_rep    in *; logic_clean.
    do 2 eexists; intuition eauto.

    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
  }
  repeat destruct_and_split; simpl; eauto.
  Unshelve.
  all: eauto.
Qed.


Lemma TIE_write_inner:
    forall off inum u s0 s3 v1 v2,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u None s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.write_inner off v2 inum)) s0 s3.
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
    solve_get_first.
    solve_get_first.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_exec; cleanup.
    eapply Transaction.read_finished in H11; eauto.
    eapply Transaction.read_finished in H13; eauto.
    cleanup. clear H13 H14.
    destruct (test_bit inum (value_to_bits r1));
    destruct (test_bit inum (value_to_bits r2));
    simpl; intuition eauto.
    solve_get_first.
    solve_get_first.
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
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
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
        solve_get_first.
        solve_get_first.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
        repeat invert_exec; cleanup.
        eapply Transaction.read_finished in H11; eauto.
        eapply Transaction.read_finished in H24; eauto.
        cleanup. clear H24 H25.
        destruct (test_bit (seln (Inode.block_numbers x3) off 0) (value_to_bits r1));
        destruct (test_bit (seln (Inode.block_numbers x4) off 0) (value_to_bits r2));
        simpl; intuition eauto.
        {
          eapply BlockAllocatorExistence.data_block_inbounds_2.
          4: eauto.
          all: eauto.
          eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
          [| intros; FileInnerSpecs.solve_bounds ]; eauto.
        }
        {
          eapply BlockAllocatorExistence.data_block_inbounds_2.
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
    }
    unfold File.files_inner_rep, 
    FD_related_states, same_for_user_except,
    File.file_map_rep    in *; logic_clean.
    do 2 eexists; intuition eauto.

    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
  }
  unfold File.DiskAllocator.write;
  repeat destruct_and_split; simpl; eauto.
  Unshelve.
  all: eauto.
Qed.


Lemma TIE_create:
    forall ex u' s1 s2 v,
refines_related ATC_Refinement
  (AD_related_states u' ex) s1 s2 ->
transaction_input_equiv
(File.create v) (File.create v) s1 s2.
Proof.
Transparent File.create.  
unfold refines_related, File.create; simpl; intuition eauto; cleanup.
{
  Transparent Inode.alloc.
  unfold Inode.alloc.
  simpl; intuition eauto.
  solve_get_first.
  solve_get_first.
  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_exec; cleanup.
  eapply Transaction.read_finished in H7; eauto.
  eapply Transaction.read_finished in H9; eauto.
  cleanup.

  destruct_fresh (Compare_dec.lt_dec
  (get_first_zero_index (value_to_bits r1))
  Inode.InodeAllocatorParams.num_of_blocks);
  destruct_fresh (Compare_dec.lt_dec
  (get_first_zero_index (value_to_bits r2))
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
  repeat invert_exec; cleanup.
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
    forall inum ex u s0 s3 v1 v2,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u ex s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v1 inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.extend_inner v2 inum)) s0 s3.
Proof.
  Transparent File.extend_inner.  
  Opaque File.DiskAllocator.alloc.
  unfold refines_related, File.extend_inner; simpl; intuition eauto; cleanup.
{
  Transparent File.DiskAllocator.alloc.
  simpl; intuition eauto.
  solve_get_first.
  solve_get_first.

  unfold HC_refines in *; simpl in *; cleanup.
  unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
  repeat invert_exec; cleanup.
  eapply Transaction.read_finished in H11; eauto.
  eapply Transaction.read_finished in H13; eauto.
  cleanup. clear H13 H14.
  destruct (Compare_dec.lt_dec
  (get_first_zero_index (value_to_bits r1))
  File.DiskAllocatorParams.num_of_blocks);
  destruct (Compare_dec.lt_dec
  (get_first_zero_index (value_to_bits r2))
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
  repeat invert_exec; cleanup.
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
          S (get_first_zero_index (value_to_bits x6)))); eauto.
          shelve.
          cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S (get_first_zero_index (value_to_bits x11)))); eauto.
          shelve.
        
          {
            unfold HC_refines in *; simpl in *; cleanup.
            unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
            repeat invert_exec; cleanup.
            eapply Transaction.read_finished in H16; eauto.
            eapply Transaction.read_finished in H19; eauto.
            cleanup. clear H19 H20.
            destruct (test_bit inum (value_to_bits r1));
            destruct (test_bit inum (value_to_bits r2));
            simpl; intuition eauto.
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              destruct (addr_eq_dec
              (Inode.InodeAllocatorParams.bitmap_addr + S inum)
              (File.DiskAllocatorParams.bitmap_addr +
              S (get_first_zero_index (value_to_bits x6)))); eauto.
              shelve.
            }
            {
              unfold AD_related_states, refines_related in *; simpl in *; cleanup.
              unfold refines, File.files_rep in *; simpl in *; cleanup.
              destruct (addr_eq_dec
              (Inode.InodeAllocatorParams.bitmap_addr + S inum)
              (File.DiskAllocatorParams.bitmap_addr +
              S (get_first_zero_index (value_to_bits x11)))); eauto.
              shelve.
            }
            
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
          S (get_first_zero_index  (value_to_bits x6)))); eauto.
          shelve.
          }
          {
          cleanup; eauto; try congruence.
          destruct (addr_eq_dec Inode.InodeAllocatorParams.bitmap_addr
          (File.DiskAllocatorParams.bitmap_addr +
          S (get_first_zero_index (value_to_bits x11)))); eauto.
          shelve.
          }
          unfold HC_refines in *; simpl in *; cleanup.
            unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
            repeat invert_exec; cleanup.
            eapply Transaction.read_finished in H16; eauto.
            eapply Transaction.read_finished in H19; eauto.
            cleanup. clear H19 H21.
            destruct (test_bit inum (value_to_bits r1));
            destruct (test_bit inum (value_to_bits r2));
            simpl; intuition eauto.
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

Lemma TIE_change_owner_inner:
forall inum ex u s0 s3 v,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u ex s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.change_owner_inner v inum)) s0 s3.
Proof.
Transparent File.change_owner_inner.  
Opaque Inode.get_inode.
unfold refines_related, File.change_owner_inner; simpl; intuition eauto; cleanup.
{
  Transparent Inode.change_owner.
  unfold Inode.change_owner.
  simpl; intuition eauto.
  {
    Transparent Inode.get_inode.
    simpl; unfold Inode.InodeAllocator.read; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
    solve_get_first.
    solve_get_first.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_exec; cleanup.
    eapply Transaction.read_finished in H11; eauto.
    eapply Transaction.read_finished in H13; eauto.
    cleanup. clear H13 H14.
    destruct (test_bit inum (value_to_bits r1));
    destruct (test_bit inum (value_to_bits r2));
    simpl; intuition eauto.
    solve_get_first.
    solve_get_first.
    all: repeat destruct_and_split; simpl; eauto.
    Opaque Inode.get_inode.
  }

    repeat destruct_and_split; simpl; intuition eauto.
    {
      repeat cleanup_pairs.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H6; eauto; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H7; eauto; cleanup.
      
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H6; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H7; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
  
      eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H2; eauto.
      2: eapply have_same_structure_get_inode; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply Inode.get_inode_finished in H13; eauto.
      eapply Inode.get_inode_finished in H15; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.

      unfold HC_refines in *; simpl in *; cleanup.
      clear H19 H20.
      unfold Inode.set_inode; simpl; intuition eauto; try congruence;
      cleanup.

      unfold Inode.InodeAllocator.write; simpl; intuition eauto.
      destruct (Compare_dec.lt_dec inum
      Inode.InodeAllocatorParams.num_of_blocks); try lia.
      simpl; intuition eauto.
      solve_get_first.
      solve_get_first.

    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_exec; cleanup.
    eapply Transaction.read_finished in H20; eauto.
    eapply Transaction.read_finished in H24; eauto.
    cleanup. clear H24 H27.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines,
    Transaction.transaction_rep in *; simpl in *; cleanup.
    repeat split_ors; cleanup; try congruence.
    repeat cleanup_pairs.
    destruct s, s3; simpl in *; try lia; eauto.
    destruct (test_bit inum (value_to_bits r1));
    destruct (test_bit inum (value_to_bits r2));
    simpl; intuition eauto.
    simpl; intuition eauto.

    unfold File.files_inner_rep, 
    FD_related_states, same_for_user_except,
    File.file_map_rep    in *; logic_clean.
    do 2 eexists; intuition eauto.

    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
    eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
  }
  
  unfold Inode.set_inode, Inode.InodeAllocator.write; simpl; intuition eauto.
  destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
}
Unshelve.
all: eauto.
Qed.

Lemma TIE_free_all_blocks:
    forall l1 l2 s0 s3,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
(exists file_block_map : disk value,
File.DiskAllocator.block_allocator_rep
  file_block_map (fst (snd (snd s4)))) /\ 
(exists file_block_map : disk value,
  File.DiskAllocator.block_allocator_rep
    file_block_map (fst (snd (snd s5))))) s0 s3 ->
(Transaction.get_first (fst (snd s0))
File.DiskAllocatorParams.bitmap_addr = None <->
Transaction.get_first (fst (snd s3))
File.DiskAllocatorParams.bitmap_addr = None) ->
(length (fst (snd s0)) = length (fst (snd s3))) ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l1))
(@lift_L2 AuthenticationOperation _ TD _ (File.free_all_blocks l2)) s0 s3.
Proof.
  induction l1; destruct l2; simpl; intuition eauto.
  {
    unfold File.DiskAllocator.free; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec a
    File.DiskAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec n
    File.DiskAllocatorParams.num_of_blocks);
    simpl; intuition eauto.

    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_exec; cleanup.
    eapply Transaction.read_finished in H11; eauto.
    eapply Transaction.read_finished in H13; eauto.
    cleanup. clear H13 H14.
    destruct (test_bit a (value_to_bits r1));
    destruct (test_bit n (value_to_bits r2));
    simpl; intuition eauto.
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      repeat rewrite app_length, map_length in *; simpl in *.
      erewrite addr_list_to_blocks_length_eq; try lia.
      rewrite <- H1; eauto.
      repeat rewrite app_length, map_length; eauto.
    }
    {
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep in *; simpl in *; cleanup.
      unfold HC_refines in *; simpl in *; cleanup.
      repeat rewrite app_length, map_length in *; simpl in *.
      erewrite addr_list_to_blocks_length_eq; try lia.
      rewrite H1; eauto.
      repeat rewrite app_length, map_length; eauto.
    }
    Opaque Inode.get_all_block_numbers Inode.get_inode.
  }
  repeat destruct_and_split; simpl; eauto.
  {
    unfold AD_related_states, refines_related in *; simpl in *; cleanup.
    unfold refines, File.files_rep in *; simpl in *; cleanup.
    repeat cleanup_pairs.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H0; eauto; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H4; eauto; cleanup.
      
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H4; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
  
      eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H9; eauto.
      2: eapply have_same_structure_DiskAllocator_free; eauto.
      4: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply File.DiskAllocator.free_finished in H15; eauto.
      eapply File.DiskAllocator.free_finished in H17; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.
      eapply IHl1; eauto.
      do 2 eexists; intuition eauto.
      {
        clear H8 H9 H12.
        unfold File.DiskAllocator.free in *;
        simpl in *; repeat invert_exec.
        destruct (Compare_dec.lt_dec a
        File.DiskAllocatorParams.num_of_blocks);
        destruct (Compare_dec.lt_dec n
        File.DiskAllocatorParams.num_of_blocks); try lia;
        repeat (simpl in *; repeat invert_exec; cleanup).

        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
        repeat invert_exec; cleanup.
        eapply Transaction.read_finished in H10; eauto.
        eapply Transaction.read_finished in H16; eauto.
        cleanup.
        clear H0 H9.
        eapply Transaction.write_finished in H18; eauto.
        eapply Transaction.write_finished in H22; eauto.
        cleanup.
        repeat split_ors; cleanup.
        simpl; intuition eauto; cleanup; eauto.
      }

      {
        clear H8 H9 H12.
        unfold File.DiskAllocator.free in *;
        simpl in *; repeat invert_exec.
        destruct (Compare_dec.lt_dec a
        File.DiskAllocatorParams.num_of_blocks);
        destruct (Compare_dec.lt_dec n
        File.DiskAllocatorParams.num_of_blocks); try lia;
        repeat (simpl in *; repeat invert_exec; cleanup).

        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
        repeat invert_exec; cleanup.
        eapply Transaction.read_finished in H10; eauto.
        eapply Transaction.read_finished in H16; eauto.
        cleanup.
        clear H0 H9.
        eapply Transaction.write_finished in H18; eauto.
        eapply Transaction.write_finished in H22; eauto.
        cleanup.
        repeat split_ors; cleanup.
        simpl; intuition eauto; cleanup; eauto.
      }
      {
        clear H8 H9 H12.
        unfold File.DiskAllocator.free in *;
        simpl in *; repeat invert_exec.
        destruct (Compare_dec.lt_dec a
        File.DiskAllocatorParams.num_of_blocks);
        destruct (Compare_dec.lt_dec n
        File.DiskAllocatorParams.num_of_blocks); try lia;
        repeat (simpl in *; repeat invert_exec; cleanup).
      }
      {
        clear H8 H9 H12.
        unfold File.DiskAllocator.free in *;
        simpl in *; repeat invert_exec.
        destruct (Compare_dec.lt_dec a
        File.DiskAllocatorParams.num_of_blocks);
        destruct (Compare_dec.lt_dec n
        File.DiskAllocatorParams.num_of_blocks); try lia;
        repeat (simpl in *; repeat invert_exec; cleanup).

        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
        repeat invert_exec; cleanup.
        eapply Transaction.read_finished in H10; eauto.
        eapply Transaction.read_finished in H17; eauto.
        cleanup.
        repeat split_ors; cleanup; try lia.
        simpl in *; eauto.
        lia.
      }
      
  }
  destruct l1; simpl; intuition eauto.
  Unshelve.
  all: eauto.
Qed.

Lemma free_all_blocks_transaction_content:
forall l s u o s' r,
exec ATCLang u o s
(RefinementLift.compile
   (HorizontalComposition
      AuthenticationOperation
      TransactionCacheOperation)
   (HorizontalComposition
      AuthenticationOperation
      (TransactionalDiskLayer.TDCore
         data_length))
   ATCLang AD
   (HC_Core_Refinement
      ATCLang AD
      Definitions.TDCoreRefinement)
   (option unit)
   (@lift_L2
      AuthenticationOperation _
      TD _ 
      (File.free_all_blocks l)))
(Finished s' r) ->
(forall a, In a (map fst (fst (snd s'))) -> 
In a (map fst (fst (snd s))) \/ a = File.DiskAllocatorParams.bitmap_addr).
Proof.
induction l; simpl; intros;
  repeat invert_exec; eauto.
eapply IHl in H1; eauto.
unfold File.DiskAllocator.free in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.read in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.write in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
repeat cleanup_pairs; intuition eauto.

unfold File.DiskAllocator.free in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.read in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.write in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
repeat cleanup_pairs; intuition eauto.
Qed.

Lemma get_first_some_in:
forall (l : list (addr * value)) (a : addr)v,
Transaction.get_first l a = Some v -> In a (map fst l).
Proof.
induction l; simpl; intuition eauto; try congruence.
simpl in *; cleanup; eauto.
Qed.


Lemma free_all_blocks_transaction_length:
forall l s u o s',
exec ATCLang u o s
(RefinementLift.compile
   (HorizontalComposition
      AuthenticationOperation
      TransactionCacheOperation)
   (HorizontalComposition
      AuthenticationOperation
      (TransactionalDiskLayer.TDCore
         data_length))
   ATCLang AD
   (HC_Core_Refinement
      ATCLang AD
      Definitions.TDCoreRefinement)
   (option unit)
   (@lift_L2
      AuthenticationOperation _
      TD _ 
      (File.free_all_blocks l)))
(Finished s' (Some tt)) ->
length (fst (snd s')) = length (fst (snd s)) + length l.
Proof.
induction l; simpl; intros;
  repeat invert_exec; cleanup; simpl; eauto; try lia.

eapply IHl in H0; eauto.
unfold File.DiskAllocator.free in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.read in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.write in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
repeat cleanup_pairs; intuition eauto.

unfold File.DiskAllocator.free in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.read in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
unfold Transaction.write in *; 
repeat (simpl in *; repeat invert_exec; cleanup; eauto);
repeat cleanup_pairs; intuition eauto.
Qed.


Lemma TIE_delete_inner:
forall inum u s0 s3,
refines_related ATC_Refinement
(fun s4 s5 : state AD =>
 exists s1a s2a : disk File,
 fst (snd s4) = Empty /\
 fst (snd s5) = Empty /\
   File.files_inner_rep s1a (fst (snd (snd s4))) /\
   File.files_inner_rep s2a (fst (snd (snd s5))) /\
   FD_related_states u None s1a s2a) s0 s3 ->
transaction_input_equiv
(@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum))
(@lift_L2 AuthenticationOperation _ TD _ (File.delete_inner inum)) s0 s3.
Proof.
  Transparent File.delete_inner.  
  unfold refines_related, File.delete_inner; simpl; intuition eauto; cleanup.
  {
    Transparent Inode.get_all_block_numbers Inode.get_inode.
    unfold Inode.get_all_block_numbers.
    simpl; intuition eauto.
    unfold Inode.InodeAllocator.read; simpl; intuition eauto.
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks);
    destruct (Compare_dec.lt_dec inum
    Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
    solve_get_first.
    solve_get_first.
    unfold HC_refines in *; simpl in *; cleanup.
    unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
    repeat invert_exec; cleanup.
    eapply Transaction.read_finished in H11; eauto.
    eapply Transaction.read_finished in H13; eauto.
    cleanup. clear H13 H14.
    destruct (test_bit inum (value_to_bits r1));
    destruct (test_bit inum (value_to_bits r2));
    simpl; intuition eauto.
    solve_get_first.
    solve_get_first.
    all: repeat destruct_and_split; simpl; eauto.
    Opaque Inode.get_all_block_numbers Inode.get_inode.
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
      2: eapply have_same_structure_get_all_block_numbers; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply Inode.get_all_block_numbers_finished in H13; eauto.
      eapply Inode.get_all_block_numbers_finished in H15; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.
      eapply TIE_free_all_blocks.
      unfold refines_related; simpl; do 2 eexists; intuition eauto.
      simpl; eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
        simpl; eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; 
        [| intros; FileInnerSpecs.solve_bounds ]; eauto.
      clear H H2; intuition; solve_get_first.
      {
        clear H H2.
        unfold AD_related_states, refines_related in *; simpl in *; cleanup;
        unfold refines, File.files_rep in *; simpl in *; cleanup;
        unfold HC_refines in *; simpl in *; cleanup;
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in *; simpl in *; cleanup;
        repeat split_ors; cleanup; try congruence;
        repeat cleanup_pairs.
        destruct s, s2; simpl in *; try lia; eauto.
      }
      unfold File.files_inner_rep, 
      FD_related_states, same_for_user_except,
      File.file_map_rep    in *; logic_clean.
      do 2 eexists; intuition eauto.

      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
    }
    repeat destruct_and_split; simpl; eauto.
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
      2: eapply have_same_structure_get_all_block_numbers; eauto.
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply Inode.get_all_block_numbers_finished in H15; eauto.
      eapply Inode.get_all_block_numbers_finished in H17; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.


      repeat cleanup_pairs.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H8; eauto; cleanup.
      eapply_fresh ATC_Simulation.ATC_oracle_refines_finished in H9; eauto; cleanup.
      
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H8; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply_fresh ATC_Simulation.ATC_exec_lift_finished in H9; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
  
      eapply_fresh ATC_ORS.ATC_oracle_refines_impl_eq in H17; eauto.
      (* 2: eapply have_same_structure_free_all_blocks; eauto. *)
      3: apply TD_oracle_refines_operation_eq.
      cleanup.
      repeat invert_exec.
      unfold AD_related_states, refines_related in *; simpl in *; cleanup.
      unfold refines, File.files_rep, File.files_inner_rep in *; simpl in *; cleanup.
      repeat cleanup_pairs.
      eapply FileInnerSpecs.free_all_blocks_finished in H30; eauto.
      eapply FileInnerSpecs.free_all_blocks_finished in H32; eauto.
      2: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
      intros; FileInnerSpecs.solve_bounds]; eauto.
      2: eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
      intros; FileInnerSpecs.solve_bounds]; eauto.
      cleanup; repeat split_ors; cleanup.
      simpl in *; repeat cleanup_pairs.

      Transparent Inode.free.
      unfold Inode.free, Inode.InodeAllocator.free.
      destruct (Compare_dec.lt_dec inum
      Inode.InodeAllocatorParams.num_of_blocks);
      simpl; intuition eauto.
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup;
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in H35; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s2; simpl in *; try lia.

        destruct_fresh (Transaction.get_first (fst s6) Inode.InodeAllocatorParams.bitmap_addr); eauto.
        eapply get_first_some_in in D.
        eapply free_all_blocks_transaction_content with (a:= Inode.InodeAllocatorParams.bitmap_addr) in H9; simpl; eauto; simpl in *; intuition.
        unfold Inode.InodeAllocatorParams.bitmap_addr,
        File.DiskAllocatorParams.bitmap_addr in *;
        pose proof inodes_before_data; lia.
      }
      {
        unfold AD_related_states, refines_related in *; simpl in *; cleanup;
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in H40; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s2; simpl in *; try lia.

        destruct_fresh (Transaction.get_first (fst s6) Inode.InodeAllocatorParams.bitmap_addr); eauto.
        eapply get_first_some_in in D.
        eapply free_all_blocks_transaction_content with (a:= Inode.InodeAllocatorParams.bitmap_addr) in H8; simpl; eauto; simpl in *; intuition.
        unfold Inode.InodeAllocatorParams.bitmap_addr,
        File.DiskAllocatorParams.bitmap_addr in *;
        pose proof inodes_before_data; lia.
      }
      unfold HC_refines in *; simpl in *; cleanup.
      unfold TransactionToTransactionalDisk.Definitions.refines in *; simpl in *; cleanup.
      repeat invert_exec; cleanup.
      eapply Transaction.read_finished in H29; eauto.
      eapply Transaction.read_finished in H45; eauto.
      cleanup. clear H45 H46.
      assume (A: (length (Inode.block_numbers x3) = length (Inode.block_numbers x4))).
      destruct (test_bit inum (value_to_bits r1));
      destruct (test_bit inum (value_to_bits r2));
      simpl; intuition eauto.
      {
        eapply free_all_blocks_transaction_length in H8.
        eapply free_all_blocks_transaction_length in H9.
        repeat rewrite app_length, map_length in *;
        simpl in *.
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in H40, H41; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s0, s2; simpl in *; try lia.
        setoid_rewrite A in H45.
        erewrite addr_list_to_blocks_length_eq; eauto.
        repeat rewrite app_length, map_length; simpl; try lia.
        rewrite H8, H9 in *.
        setoid_rewrite A.
        eauto.
      }
      {
        eapply free_all_blocks_transaction_length in H8.
        eapply free_all_blocks_transaction_length in H9.
        repeat rewrite app_length, map_length in *;
        simpl in *.
        unfold AD_related_states, refines_related in *; simpl in *; cleanup.
        unfold refines, File.files_rep in *; simpl in *; cleanup.
        unfold HC_refines in *; simpl in *; cleanup.
        unfold TransactionToTransactionalDisk.Definitions.refines,
        Transaction.transaction_rep in H40, H41; simpl in *; cleanup.
        repeat split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        destruct s0, s2; simpl in *; try lia.
        setoid_rewrite A.
        erewrite addr_list_to_blocks_length_eq; eauto.
        repeat rewrite app_length, map_length; simpl; try lia.
        rewrite H8, H9 in *.
        setoid_rewrite A.
        eauto.
      }
      {
        eapply have_same_structure_free_all_blocks; simpl; eauto.

        {
          edestruct FileInnerSpecs.inode_exists_then_file_exists; eauto.
          edestruct FileInnerSpecs.inode_exists_then_file_exists.
          2: apply H27.
          eauto.

          unfold File.file_map_rep in *; cleanup.
          eapply_fresh H31 in H29; eauto.
          eapply_fresh H33 in H30; eauto.
          unfold File.file_rep in *; cleanup.
          unfold FD_related_states, same_for_user_except in *; cleanup.
          eapply H42 in H29; eauto; cleanup; eauto.
        }
        eapply SameRetType.all_block_numbers_in_bound; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; FileInnerSpecs.solve_bounds.

        eapply SameRetType.all_block_numbers_in_bound.
        4: eauto.
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; FileInnerSpecs.solve_bounds.

        {
          eapply Forall_forall; intros.
          eapply in_seln_exists in H29; cleanup.
          simpl; rewrite <- H30.
          eapply BlockAllocatorExistence.used_blocks_are_allocated_2; eauto.
          eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
          intros; FileInnerSpecs.solve_bounds.
        }

        {
          eapply Forall_forall; intros.
          eapply in_seln_exists in H29; cleanup.
          simpl; rewrite <- H30.
          eapply BlockAllocatorExistence.used_blocks_are_allocated_2; eauto.
          eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
          intros; FileInnerSpecs.solve_bounds.
        }

        {
          unfold Inode.inode_rep, Inode.inode_map_rep,
          Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
          eapply H39 in H27; cleanup; eauto.
        }
        {
          unfold Inode.inode_rep, Inode.inode_map_rep,
          Inode.inode_map_valid, Inode.inode_valid in *; cleanup.
          eapply H36 in H28; cleanup; eauto.
        }

        simpl; split; eexists; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
        intros; FileInnerSpecs.solve_bounds]; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; [|
        intros; FileInnerSpecs.solve_bounds]; eauto.
      }
      unfold File.files_inner_rep, 
      FD_related_states, same_for_user_except,
      File.file_map_rep    in *; logic_clean.
      do 2 eexists; intuition eauto.

      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_trans; eauto.
      eapply BlockAllocatorExistence.addrs_match_exactly_sym; eauto.
    }
    unfold Inode.free, Inode.InodeAllocator.free.
    destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks); simpl; intuition eauto.
    Opaque Inode.free.
    Unshelve.
    all: eauto.
    {
          edestruct FileInnerSpecs.inode_exists_then_file_exists; eauto.
          edestruct FileInnerSpecs.inode_exists_then_file_exists.
          2: apply H27.
          eauto.

          unfold File.file_map_rep in *; cleanup.
          eapply_fresh H47 in H45; eauto.
          eapply_fresh H49 in H46; eauto.
          unfold File.file_rep in *; cleanup.
          unfold FD_related_states, same_for_user_except in *; cleanup.
          eapply H58 in H45; eauto; cleanup; eauto.
        }
Qed.
