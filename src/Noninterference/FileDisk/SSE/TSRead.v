Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType TSCommon InodeTS.

  (******** TS PROOFS ********)

  Lemma TS_read_inner:
  forall o fm1 fm2 s1 s2 inum off ret1 u u' ex,
  same_for_user_except u' ex fm1 fm2 ->
  files_inner_rep fm1 (fst (snd s1)) ->
  files_inner_rep fm2 (fst (snd s2)) ->
  exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s1 (read_inner off inum) ret1 ->
  exists ret2, 
  exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s2 (read_inner off inum) ret2 /\
  (extract_ret ret1 = None <-> extract_ret ret2 = None).
  Proof.
    Transparent read_inner.  
    unfold read_inner; intros.
    invert_step.
{
  eapply_fresh TS_get_block_number in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  unfold files_inner_rep  in *; cleanup.
  eapply_fresh Inode.get_block_number_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  eapply Inode.get_block_number_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh Inode.get_block_number_finished in H4; eauto.
  cleanup; split_ors; cleanup.
  

  eapply_fresh TS_DiskAllocator_read in H3. 
  2: eauto.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence].
  eapply DiskAllocator.read_finished_oracle_eq in H3; eauto; cleanup.
  destruct o; try intuition congruence.

  eexists; split.
  econstructor.
  simpl; eapply H4.
  econstructor; eauto.
  simpl; econstructor; eauto.
  simpl; intuition congruence.

  unfold files_inner_rep;
  eexists; intuition eauto.
  eexists; intuition eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; solve_bounds.

  unfold files_inner_rep;
  eexists; intuition eauto.
  eexists; intuition eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; solve_bounds.
  4: {
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

  {
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
  }
  2: {
    intuition.
    eapply data_block_inbounds_2; eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.

    eapply data_block_inbounds_2.
    4: eauto. 
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
}
{
  repeat erewrite used_blocks_are_allocated_2; eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
}
}
{
  eapply_fresh TS_get_block_number in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  unfold files_inner_rep  in *; cleanup.
  eapply_fresh Inode.get_block_number_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  eapply Inode.get_block_number_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh Inode.get_block_number_finished in H4; eauto.
  cleanup; split_ors; cleanup.
  

  eapply_fresh TS_DiskAllocator_read in H3. 
  2: eauto.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence].
  eapply DiskAllocator.read_finished_oracle_eq in H3; eauto; cleanup.
  destruct o; try intuition congruence.

  eexists; split.
  econstructor.
  simpl; eapply H4.
  econstructor; eauto.
  simpl; econstructor; eauto.
  simpl; intuition congruence.

  unfold files_inner_rep;
  eexists; intuition eauto.
  eexists; intuition eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; solve_bounds.

  unfold files_inner_rep;
  eexists; intuition eauto.
  eexists; intuition eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
  intros; solve_bounds.
  4: {
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

  {
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
  }
  2: {
    intuition.
    eapply data_block_inbounds_2; eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.

    eapply data_block_inbounds_2.
    4: eauto. 
    all: eauto.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
}
{
  repeat erewrite used_blocks_are_allocated_2; eauto.
  eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
    eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; solve_bounds.
}
}
{
  eapply_fresh TS_get_block_number in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  unfold files_inner_rep  in *; cleanup.
  eapply_fresh Inode.get_block_number_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  eapply Inode.get_block_number_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh Inode.get_block_number_finished in H3; eauto.
  cleanup; split_ors; cleanup.
  
  eexists; split.
  econstructor.
  simpl; eauto.
  econstructor; eauto.
  simpl; intuition congruence.
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
}
{
  repeat invert_step_crash.
  {
    eapply_fresh TS_get_block_number in H2; eauto.
    cleanup.
    destruct x; simpl in *; try solve [intuition congruence]. 
  
    exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash; eauto.
    simpl; intuition eauto.
  }
  {
    eapply_fresh TS_get_block_number in H3; eauto.
    logic_clean.
    destruct x3; simpl in *; try solve [intuition congruence]. 
    
    unfold files_inner_rep in *; logic_clean.
    eapply_fresh Inode.get_block_number_finished_oracle_eq in H3; eauto.
    logic_clean.
    eapply Inode.get_block_number_finished in H3; eauto.
    eapply_fresh Inode.get_block_number_finished in H2; eauto.
    cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
    {
      repeat invert_step_crash.
      {

      eapply_fresh TS_DiskAllocator_read in H4.
      2: eauto.
      cleanup.
      destruct x8; simpl in *; try solve [intuition congruence].
      exists (Crashed s3); split.
      econstructor; simpl; eauto.
      simpl; eauto.
      econstructor; eauto.
      simpl; intuition eauto.

      unfold files_inner_rep;
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; solve_bounds.

      unfold files_inner_rep;
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; solve_bounds.
      {
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
      }
      2: {
        intuition.
        eapply data_block_inbounds_2; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.

        eapply data_block_inbounds_2.
        4: eauto. 
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.
      }
      {
        repeat erewrite used_blocks_are_allocated_2; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
          intros; solve_bounds.
          eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
          intros; solve_bounds.
      }
      }
    {
      eapply_fresh TS_DiskAllocator_read in H12.
      2: eauto.
      logic_clean.
      destruct x2; simpl in *; try solve [intuition congruence].
      eapply DiskAllocator.read_finished_oracle_eq in H12; eauto; logic_clean.
      cleanup; destruct o; try solve [intuition congruence];
      repeat invert_exec.

      
      exists (Crashed s3); split.
      econstructor; simpl; eauto.
      simpl; eauto.
      econstructor; eauto.
      simpl;
      repeat econstructor; eauto.
      simpl; intuition eauto.

      exists (Crashed s3); split.
      econstructor; simpl; eauto.
      simpl; eauto.
      econstructor; eauto.
      simpl;
      repeat econstructor; eauto.
      simpl; intuition eauto.

      
      unfold files_inner_rep;
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; solve_bounds.

      unfold files_inner_rep;
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
      intros; solve_bounds.
      {
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
      }
      2: {
        intuition.
        eapply data_block_inbounds_2; eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.

        eapply data_block_inbounds_2.
        4: eauto. 
        all: eauto.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.
    }
    {
      repeat erewrite used_blocks_are_allocated_2; eauto.
      eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.
        eapply File.DiskAllocator.block_allocator_rep_inbounds_eq; eauto.
        intros; solve_bounds.
    }
  }
}
{
  repeat invert_exec.
  eexists (Crashed _); split.
      econstructor; simpl; eauto.
      simpl; eauto.
      econstructor; eauto.
      simpl; intuition eauto.
}
{
  clear H4.
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
     end;
     unfold File.file_rep in *; cleanup; eauto.
  }
}
}
Unshelve.
all: eauto.
Qed.
Opaque read_inner.

Theorem Termination_Sensitive_read:
  forall u u' m inum off,
    Termination_Sensitive
      u (read inum off) (read inum off) recover
      AD_valid_state (AD_related_states u' None)
      (authenticated_disk_reboot_list m).
Proof. 
  unfold Termination_Sensitive, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  read;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**write finished **)
   invert_exec.
   eapply TS_auth_then_exec in H11; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eexists; econstructor_recovery.
     eauto.
   }
   {
     intros.
     eapply_fresh TS_read_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.read_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
      eapply same_for_user_except_symmetry; eauto.
     }
     {
      eexists.
      intuition eauto; cleanup; eauto.
     }
   }
  }
  {
    invert_exec.
    eapply_fresh TS_auth_then_exec in H14; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eapply_fresh FileSpecs.read_crashed in H14; eauto.
    eapply_fresh FileSpecs.read_crashed in H1; eauto.
    repeat split_ors; cleanup.
    {
      match goal with
        [H: refines ?s1 ?x,
        H0: refines ?s2 ?x0, 
        H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply Termination_Sensitive_recover in A;
          try instantiate (1:= (fst s, (snd (snd s), snd (snd s)))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: eexists; econstructor_recovery; [|eauto]; eauto.
     {
       instantiate (1:= None).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
     }
   }
   }
  {
     intros.
     eapply_fresh TS_read_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.read_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
      eapply same_for_user_except_symmetry; eauto.
     }
     {
      eexists.
      intuition eauto; cleanup; eauto.
     }
  }
}
Unshelve.
all: eauto.
Qed.