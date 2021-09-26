Require Import Eqdep Lia Framework FSParameters FileDiskLayer. (* LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer. *)
Require Import FileDiskNoninterference FileDiskRefinement.
Require Import ATCDLayer ATCDSimulation ATCDAOE FileDisk.TransferProofs.
Require Import ATC_ORS_Common.
Import FileDiskLayer.

  Lemma ATCD_ORS_inode_allocator_read:
  forall n inum u u',
  oracle_refines_same_from_related ATCD_Refinement u
    (@lift_L2 AuthenticationOperation _  _ (Inode.InodeAllocator.read inum))
    (@lift_L2 AuthenticationOperation _ TD _ (Inode.InodeAllocator.read inum))
    (Simulation.Definitions.compile FD.refinement (| Recover |))
    (ATCD_reboot_list n) 
    (fun s1 s2  => exists s1a s2a, 
    File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
    File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
    FD_related_states u' None s1a s2a).
  Proof.
    Transparent Inode.InodeAllocator.read.
    unfold Inode.InodeAllocator.read; intros.
    destruct (Compare_dec.lt_dec inum Inode.InodeAllocatorParams.num_of_blocks).
    simpl; eapply ATC_ORS_compositional.
    3: intros; apply ATC_ORS_recover.
    intros; apply ATC_ORS_TD_read.
    2:{
      simpl; intros; cleanup.
      eapply lift2_invert_exec in H; cleanup.
      eapply lift2_invert_exec in H0; cleanup.

      apply HC_map_ext_eq in H6; subst.
      apply HC_map_ext_eq in H9; subst.
      repeat split_ors; cleanup; eauto;
      repeat unify_execs; cleanup; eauto.
      eapply map_ext_eq_prefix in H3; eauto; cleanup.
      eapply Transaction.read_finished_oracle_eq in H2; eauto; subst; eauto.
      intros; cleanup; intuition congruence.
    }
    2: apply oracle_refines_independent_from_reboot_function.
    3: {
      intros; unfold refines_related in *; cleanup.
      unfold not; intros.
      eapply ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished].
      cleanup.
      eapply ATC_exec_lift_crashed in H7; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      cleanup.
      specialize (H13 tt).
      specialize (H16 tt).
      repeat invert_exec; cleanup;
      repeat split_ors; cleanup; try congruence.
      eapply HC_oracle_transformation_app_composed in H12; cleanup.
      eapply HC_oracle_transformation_unique in H15; eauto; subst.
      eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
      rewrite <-app_assoc; eauto.

      eapply HC_oracle_transformation_app_composed in H12; cleanup.
      eapply HC_oracle_transformation_unique in H15; eauto; subst.
      eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
      rewrite <-app_assoc; eauto.
      simpl; intros; intuition eauto.
      inversion H9.
    }
    3: {
      intros; unfold refines_related in *; cleanup.
      unfold not; intros.
      eapply ATC_exec_lift_finished in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished].
      cleanup.
      eapply ATC_exec_lift_crashed in H7; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      cleanup.
      specialize (H13 tt).
      specialize (H16 tt).
      repeat invert_exec; cleanup;
      repeat split_ors; cleanup; try congruence.
      eapply HC_oracle_transformation_app_composed in H15; cleanup.
      eapply HC_oracle_transformation_unique in H7; eauto; subst.
      eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
      rewrite <-app_assoc; eauto.
      eapply HC_oracle_transformation_app_composed in H15; cleanup.
      eapply HC_oracle_transformation_unique in H7; eauto; subst.
      eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
      rewrite <-app_assoc; eauto.
      simpl; intros; intuition eauto.
      inversion H9.
    }
    4: apply ATC_ORS_ret.
   
  {
    intros.
    intros; unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    repeat invert_exec; try lia.
    {
      simpl in *.
      unfold AD_related_states, refines_related, FD_related_states in *; cleanup.
      clear H8 H9.
      simpl in *.
      specialize (H10 tt).
      specialize (H14 tt).
      unfold refines, File.files_rep in *; cleanup.
      repeat cleanup_pairs.
      erewrite InodeTS.inode_allocations_are_same with (s2:= t); eauto.
      destruct_fresh (nth_error (value_to_bits (t Inode.InodeAllocatorParams.bitmap_addr))
      inum); try solve [apply ATC_ORS_ret].
      destruct b; try solve [apply ATC_ORS_ret].
      simpl.
      eapply ATC_ORS_compositional.
      intros; simpl. eapply ATC_ORS_TD_read.
      intros; apply ATC_ORS_ret.
      intros; apply ATC_ORS_recover.
      {
        intros.
        intros; unfold refines_related in *; cleanup.
        eapply ATC_exec_lift_finished in H; eauto;
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
        cleanup.
        eapply ATC_exec_lift_finished in H0; eauto;
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
        cleanup.
        repeat invert_exec; try lia;
        simpl in *; cleanup;
      specialize (H19 tt);
      specialize (H22 tt);
        repeat split_ors; cleanup; try congruence.
        {
          eapply HC_oracle_transformation_id_rev in H21; eauto.
          eapply HC_oracle_transformation_id_rev in H8; eauto.
          cleanup.
          eapply map_ext_eq_prefix in H9; eauto; cleanup.
          eapply Transaction.read_finished_oracle_eq in H0; eauto; subst; eauto.
          intros; cleanup; intuition congruence.
        }
        {
          eapply HC_oracle_transformation_id_rev in H21; eauto.
          eapply HC_oracle_transformation_id_rev in H8; eauto.
          cleanup.
          eapply map_ext_eq_prefix in H9; eauto; cleanup.
          eapply Transaction.read_finished_oracle_eq in H0; eauto; subst; eauto.
          intros; cleanup; intuition congruence.
        }
      }
      apply oracle_refines_independent_from_reboot_function.
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
        repeat invert_exec; try lia;
        simpl in *; cleanup;
      specialize (H18 tt);
      specialize (H21 tt);
        repeat split_ors; cleanup; try congruence;
        do 2 eexists; intuition eauto.
        all: shelve.
      }
      {
        unfold not; intros.
        simpl in *.
        eapply lift2_invert_exec in H; cleanup.
        eapply lift2_invert_exec_crashed in H9; cleanup.
        rewrite <- app_nil_r in H.
        eapply map_ext_eq_prefix in H; cleanup.
        eapply Transaction.read_finished_not_crashed; eauto.
        intros; cleanup; intuition congruence.
      }
      {
        unfold not; intros.
        simpl in *.
        eapply lift2_invert_exec in H; cleanup.
        eapply lift2_invert_exec_crashed in H9; cleanup.
        rewrite <- app_nil_r in H.  
        eapply map_ext_eq_prefix in H; cleanup.
        eapply Transaction.read_finished_not_crashed; eauto.
        intros; cleanup; intuition congruence.
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
    }
    {
      unfold AD_related_states, refines_related, FD_related_states in *; cleanup.
      clear H8 H9.
      simpl in *.
      unfold refines, File.files_rep in *; cleanup.
      specialize (H8 tt);
      specialize (H11 tt);
      repeat cleanup_pairs.
      destruct_fresh (nth_error (value_to_bits value0)
      inum); try solve [apply ATC_ORS_ret].
      destruct b; try solve [apply ATC_ORS_ret].
      simpl.
      eapply ATC_ORS_compositional.
      intros; simpl. eapply ATC_ORS_TD_read.
      intros; apply ATC_ORS_ret.
      intros; apply ATC_ORS_recover.
      {
        intros.
        intros; unfold refines_related in *; cleanup.
        eapply ATC_exec_lift_finished in H; eauto;
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
        cleanup.
        eapply ATC_exec_lift_finished in H0; eauto;
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
        try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
        cleanup.
        repeat invert_exec; try lia;
        simpl in *; cleanup;
        
      specialize (H19 tt);
      specialize (H22 tt); 
        repeat split_ors; cleanup; try congruence.
        {
          eapply HC_oracle_transformation_id_rev in H21; eauto.
          eapply HC_oracle_transformation_id_rev in H9; eauto.
          cleanup.
          eapply map_ext_eq_prefix in H12; eauto; cleanup.
          eapply Transaction.read_finished_oracle_eq in H0; eauto; subst; eauto.
          intros; cleanup; intuition congruence.
        }
      }
      apply oracle_refines_independent_from_reboot_function.
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
        repeat invert_exec; try lia;
        simpl in *; cleanup;
        
      specialize (H18 tt);
      specialize (H21 tt); 
        repeat split_ors; cleanup; try congruence;
        do 2 eexists; intuition eauto.
        all: shelve.
      }
      {
        unfold not; intros.
        simpl in *.
        eapply lift2_invert_exec in H; cleanup.
        eapply lift2_invert_exec_crashed in H12; cleanup.
        rewrite <- app_nil_r in H.
        eapply map_ext_eq_prefix in H; cleanup.
        eapply Transaction.read_finished_not_crashed; eauto.
        intros; cleanup; intuition congruence.
      }
      {
        unfold not; intros.
        simpl in *.
        eapply lift2_invert_exec in H; cleanup.
        eapply lift2_invert_exec_crashed in H12; cleanup.
        rewrite <- app_nil_r in H.
        eapply map_ext_eq_prefix in H; cleanup.
        eapply Transaction.read_finished_not_crashed; eauto.
        intros; cleanup; intuition congruence.
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
    }
  }
  2: {
      intros; unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_crashed in H; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_crashed in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      simpl in *.
      unfold refines_related, refines_related_reboot in *;
      simpl in *;  cleanup.
      unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
      do 2 eexists; repeat (split; eauto).
      all: shelve.
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
      simpl in *.
      unfold refines_related, refines_related_reboot in *;
      simpl in *;  cleanup.
      unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
      do 2 eexists; repeat (split; eauto).
      all: shelve.
  }
  Unshelve.
  all: eauto.
  all: try solve [exact (fun _ _ => True)].
  all: simpl in *; eauto.
  all: try solve [instantiate  (1:= fun _ _ => True); simpl; eauto].
  all: intuition eauto.
  all: repeat match goal with 
  | [H: eq_dep _ _ _ _ _ _ |- _] =>
  inversion H
  end.
  all: destruct (nth_error (value_to_bits t) inum); 
  simpl; intuition eauto.
  all: destruct b; simpl; intuition eauto.
  all: repeat match goal with 
  | [H: eq_dep _ _ _ _ _ _ |- _] =>
  inversion H
  end.
Qed.

Set Nested Proofs Allowed.



Lemma ATC_ORS_disk_block_allocator_read:
forall n bn1 bn2 u u',
(bn1 < File.DiskAllocatorParams.num_of_blocks <-> bn2 < File.DiskAllocatorParams.num_of_blocks) ->
oracle_refines_same_from_related ATC_Refinement u
  (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read bn1))
  (@lift_L2 AuthenticationOperation _ TD _ (File.DiskAllocator.read bn2))
  (Simulation.Definitions.compile FD.refinement (| Recover |))
  (ATC_reboot_list n) 
  (fun s1 s2  => exists s1a s2a, 
  File.files_inner_rep s1a (fst (snd (snd s1))) /\ 
  File.files_inner_rep s2a (fst (snd (snd s2))) /\ 
  FD_related_states u' None s1a s2a /\
  (nth_error
(value_to_bits
   (fst (snd (snd s1))
      File.DiskAllocatorParams.bitmap_addr)) bn1 = nth_error
      (value_to_bits
         (fst (snd (snd s2))
            File.DiskAllocatorParams.bitmap_addr)) bn2)).
Proof.
  Transparent File.DiskAllocator.read.
  unfold File.DiskAllocator.read; intros.
  destruct (Compare_dec.lt_dec bn1 File.DiskAllocatorParams.num_of_blocks);
  destruct (Compare_dec.lt_dec bn2 File.DiskAllocatorParams.num_of_blocks); try lia.
  2: eapply ATC_ORS_ret.
  simpl; eapply ATC_ORS_compositional.
  3: intros; apply ATC_ORS_recover.
  intros; apply ATC_ORS_TD_read.
  2:{
    simpl; intros; cleanup.
    eapply lift2_invert_exec in H0; cleanup.
    eapply lift2_invert_exec in H1; cleanup.

    apply HC_map_ext_eq in H7; subst.
    apply HC_map_ext_eq in H10; subst.
    repeat split_ors; cleanup; eauto;
    repeat unify_execs; cleanup; eauto.
    eapply map_ext_eq_prefix in H4; eauto; cleanup.
    eapply Transaction.read_finished_oracle_eq in H3; eauto; subst; eauto.
    intros; cleanup; intuition congruence.
  }
  2: apply oracle_refines_independent_from_reboot_function.
  3: {
    intros; unfold refines_related in *; cleanup.
    unfold not; intros.
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished].
    cleanup.
    eapply ATC_exec_lift_crashed in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    cleanup.

    specialize (H15 tt);
    specialize (H18 tt);
    repeat invert_exec; cleanup;
    repeat split_ors; cleanup; try congruence.
    eapply HC_oracle_transformation_app_composed in H14; cleanup.
    eapply HC_oracle_transformation_unique in H17; eauto; subst.
    eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
    rewrite <-app_assoc; eauto.

    eapply HC_oracle_transformation_app_composed in H14; cleanup.
    eapply HC_oracle_transformation_unique in H17; eauto; subst.
    eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
    rewrite <-app_assoc; eauto.
    simpl; intros; intuition eauto.
    inversion H11.
  }
  3: {
    intros; unfold refines_related in *; cleanup.
    unfold not; intros.
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished].
    cleanup.
    eapply ATC_exec_lift_crashed in H9; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    cleanup.

    specialize (H15 tt);
    specialize (H18 tt);
    repeat invert_exec; cleanup;
    repeat split_ors; cleanup; try congruence.
    eapply HC_oracle_transformation_app_composed in H17; cleanup.
    eapply HC_oracle_transformation_unique in H9; eauto; subst.
    eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
    rewrite <-app_assoc; eauto.
    eapply HC_oracle_transformation_app_composed in H17; cleanup.
    eapply HC_oracle_transformation_unique in H9; eauto; subst.
    eapply Transaction.read_finished_not_crashed; [eauto | | eauto].
    rewrite <-app_assoc; eauto.
    simpl; intros; intuition eauto.
    inversion H11.
  }
  {
  intros; unfold refines_related in *; cleanup.
  eapply ATC_exec_lift_finished in H0; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  eapply ATC_exec_lift_finished in H1; eauto;
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
  try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
  cleanup.
  repeat invert_exec; try lia.
  {
    simpl in *.
    unfold AD_related_states, refines_related, FD_related_states in *; cleanup.
    
    specialize (H12 tt);
    specialize (H16 tt);
    
    clear H9 H10.
    simpl in *.
    unfold refines, File.files_rep in *; cleanup.
    repeat cleanup_pairs.
    
    destruct_fresh (nth_error (value_to_bits (t File.DiskAllocatorParams.bitmap_addr))
    bn2); try solve [apply ATC_ORS_ret].
    destruct b; try solve [apply ATC_ORS_ret].
    simpl.
    eapply ATC_ORS_compositional.
    intros; simpl. 
    eapply ATC_ORS_TD_read.
    intros; apply ATC_ORS_ret.
    intros; apply ATC_ORS_recover.
    {
      intros.
      intros; unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      repeat invert_exec; try lia;
      simpl in *; cleanup;
      specialize (H21 tt);
      specialize (H24 tt);
      repeat split_ors; cleanup; try congruence.
      {
        eapply HC_oracle_transformation_id_rev in H23; eauto.
        eapply HC_oracle_transformation_id_rev in H9; eauto.
        cleanup.
        eapply map_ext_eq_prefix in H10; eauto; cleanup.
        eapply Transaction.read_finished_oracle_eq in H1; eauto; subst; eauto.
        intros; cleanup; intuition congruence.
      }
      {
        eapply HC_oracle_transformation_id_rev in H23; eauto.
        eapply HC_oracle_transformation_id_rev in H9; eauto.
        cleanup.
        eapply map_ext_eq_prefix in H10; eauto; cleanup.
        eapply Transaction.read_finished_oracle_eq in H1; eauto; subst; eauto.
        intros; cleanup; intuition congruence.
      }
      {
        unfold File.DiskAllocatorParams.num_of_blocks,
        File.DiskAllocatorParams.bitmap_addr in *.
        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        lia.
      }
      {
        unfold File.DiskAllocatorParams.num_of_blocks,
        File.DiskAllocatorParams.bitmap_addr in *.
        pose proof File.DiskAllocatorParams.blocks_fit_in_disk.
        lia.
      }
    }
    apply oracle_refines_independent_from_reboot_function.
    {
      intros; unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_finished in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_finished in H1; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      repeat invert_exec; try lia;
      simpl in *; cleanup;
      specialize (H20 tt);
      specialize (H23 tt); 
      repeat split_ors; cleanup; try congruence;
      do 2 eexists; intuition eauto.
      all: shelve.
    }
    {
      unfold not; intros.
      simpl in *.
      eapply lift2_invert_exec in H0; cleanup.
      eapply lift2_invert_exec_crashed in H10; cleanup.
      rewrite <- app_nil_r in H0.
      eapply map_ext_eq_prefix in H0; cleanup.
      eapply Transaction.read_finished_not_crashed; eauto.
      intros; cleanup; intuition congruence.
    }
    {
      unfold not; intros.
      simpl in *.
      eapply lift2_invert_exec in H0; cleanup.
      eapply lift2_invert_exec_crashed in H10; cleanup.
      rewrite <- app_nil_r in H0.  
      eapply map_ext_eq_prefix in H0; cleanup.
      eapply Transaction.read_finished_not_crashed; eauto.
      intros; cleanup; intuition congruence.
    }
    {
      intros; unfold refines_related in *; cleanup.
      eapply ATC_exec_lift_crashed in H0; eauto;
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
      try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
      cleanup.
      eapply ATC_exec_lift_crashed in H1; eauto;
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
    unfold AD_related_states, refines_related, FD_related_states in *; cleanup.
    clear H8 H9.
    simpl in *.
    unfold refines, File.files_rep in *; cleanup.
    repeat cleanup_pairs.

    destruct (block_allocator_empty bn1);
    destruct (block_allocator_empty bn2);
    cleanup;
    apply ATC_ORS_ret.
  }
}
(*
    apply oracle_refines_independent_from_reboot_function.
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
      repeat invert_exec; try lia;
      simpl in *; cleanup; 
      repeat split_ors; cleanup; try congruence;
      do 2 eexists; intuition eauto.
      all: shelve.
    }
    {
      unfold not; intros.
      simpl in *.
      eapply lift2_invert_exec in H; cleanup.
      eapply lift2_invert_exec_crashed in H12; cleanup.
      rewrite <- app_nil_r in H.
      eapply map_ext_eq_prefix in H; cleanup.
      eapply Transaction.read_finished_not_crashed; eauto.
      intros; cleanup; intuition congruence.
    }
    {
      unfold not; intros.
      simpl in *.
      eapply lift2_invert_exec in H; cleanup.
      eapply lift2_invert_exec_crashed in H12; cleanup.
      rewrite <- app_nil_r in H.
      eapply map_ext_eq_prefix in H; cleanup.
      eapply Transaction.read_finished_not_crashed; eauto.
      intros; cleanup; intuition congruence.
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
  }
}
*)
2: {
    intros; unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_crashed in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply ATC_exec_lift_crashed in H1; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    unfold refines_related, refines_related_reboot in *;
    simpl in *;  cleanup.
    unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
}
{
    intros; unfold refines_related in *; cleanup.
    eapply ATC_exec_lift_finished in H0; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    eapply ATC_exec_lift_finished in H1; eauto;
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_finished];
    try solve [apply TransactionToTransactionalDisk.Refinement.TC_to_TD_core_simulation_crashed].
    cleanup.
    simpl in *.
    unfold refines_related, refines_related_reboot in *;
    simpl in *;  cleanup.
    unfold HC_refines_reboot, HC_refines in *; simpl in *; cleanup.
    do 2 eexists; repeat (split; eauto).
    all: shelve.
}
Unshelve.
all: eauto.
all: try solve [exact (fun _ _ => True)].
all: simpl in *; eauto.
all: try solve [instantiate  (1:= fun _ _ => True); simpl; eauto].
all: intuition eauto.
all: repeat match goal with 
| [H: eq_dep _ _ _ _ _ _ |- _] =>
inversion H
end.
all: destruct (nth_error (value_to_bits t) bn1); 
simpl; intuition eauto. 
all: destruct (nth_error (value_to_bits t) bn2); 
simpl; intuition eauto. 
all: try destruct b; try destruct b0; simpl; intuition eauto.
all: repeat match goal with 
| [H: eq_dep _ _ _ _ _ _ |- _] =>
inversion H
end.
Qed.