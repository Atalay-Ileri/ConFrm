Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SSECommon.

Definition AD_valid_state := refines_valid FileDiskRefinement FD_valid_state.
Definition AD_related_states u exc := refines_related FileDiskRefinement (FD_related_states u exc).


  (******** SSE PROOFS *********)

Theorem SelfSimulation_Exists_write:
  forall u m inum off v1 v2 ex,
    SelfSimulation_Exists
      u (write inum off v1) (write inum off v2) recover
      AD_valid_state (AD_related_states u ex)
      (authenticated_disk_reboot_list m).
Proof.
  Opaque write_inner.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  write, auth_then_exec;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**write finished **)
    invert_exec.
    repeat invert_step.
    4: {
      Transparent Inode.get_owner.
      unfold  Inode.get_owner in *; simpl in *.
      eapply bind_reorder in H10.
      repeat invert_step.
      unfold Inode.InodeAllocator.read in *.
      repeat invert_step.
      {
        exists (RFinished (fst s2, (snd (snd s2), snd (snd s2))) None).
        econstructor.
        repeat exec_step.
        repeat cleanup_pairs.
        erewrite <- inode_allocations_are_same.
        4: eauto.
        all: eauto.
        simpl; rewrite D0.
        repeat exec_step.
    }
    {
      eapply nth_error_None in D0.
      rewrite value_to_bits_length in D0.
      unfold Inode.InodeAllocatorParams.num_of_blocks in *.
      pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds;
      lia.
    }
    {
        exists (RFinished (fst s2, (snd (snd s2), snd (snd s2))) None).
        econstructor.
        repeat exec_step.
    }
  }
  3: {
    Transparent Inode.get_owner.
      unfold  Inode.get_owner in *; simpl in *.
      eapply bind_reorder in H10.
      repeat invert_step.
      unfold Inode.InodeAllocator.read in *.
      repeat invert_step.
      {
        exists (RFinished (fst s2, (snd (snd s2), snd (snd s2))) None).
        econstructor.
        repeat exec_step.
        repeat cleanup_pairs.
        erewrite <- inode_allocations_are_same.
        4: eauto.
        all: eauto.
        simpl; rewrite D0.
        repeat exec_step.
        simpl.
        rewrite cons_app; econstructor.
        do 2 econstructor.
        eapply AuthenticationLayer.ExecAuthFail; 
        simpl; eauto.
        erewrite <- inode_owners_are_same.
        4: eauto.
        all: eauto.
        simpl; eauto.
        repeat exec_step.
    }
  }
  2: {(** write_inner None **)
    admit.  
  (*
    unfold  Inode.get_owner in *; simpl in *.
    eapply bind_reorder in H10.
    repeat invert_step;
    unfold Inode.InodeAllocator.read in *;
    repeat invert_step.
    {
      Transparent write_inner.
      unfold write_inner in *.
      repeat invert_step.
      {
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number in *.
        repeat invert_step.
        unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
        repeat invert_step; 
        
        unfold DiskAllocator.write in *; cleanup; try congruence;
        repeat invert_step; try congruence; try lia.
        { symmetry in H16; solve_illegal_state. }
        {
            unfold DiskAllocatorParams.bitmap_addr,
            DiskAllocatorParams.num_of_blocks in *.
            apply nth_error_None in D3.
            rewrite value_to_bits_length in D3.
            pose proof DiskAllocatorParams.num_of_blocks_in_bounds; lia.
        }
        { symmetry in H20; solve_illegal_state. }
      }
      {
        unfold Inode.get_block_number in *; invert_step;
        unfold Inode.InodeAllocator.read in *; cleanup; try congruence;
        repeat invert_step; try congruence; try lia.
        {
          exists (RFinished (fst s2, (snd (snd s2), snd (snd s2))) None).
            econstructor.
            repeat exec_step.
            repeat cleanup_pairs.
            erewrite <- inode_allocations_are_same.
            4: eauto.
            all: eauto.
            simpl; rewrite D0.
            repeat exec_step.
            simpl; repeat econstructor.
            erewrite <- inode_owners_are_same.
            4: eauto.
            all: eauto.
            simpl; eauto.
            repeat exec_step.
            repeat cleanup_pairs.
            erewrite <- inode_allocations_are_same.
            4: eauto.
            all: eauto.
            simpl; rewrite D0.
            repeat exec_step.
            simpl.
            rewrite nth_error_None_r; eauto.
            repeat exec_step.
            symmetry in H16; 
            eapply block_numbers_oob. 
            3: rewrite H16 in *; eauto.
            all: eauto.
        }
      }
    }
    *)
  }
  {(** write_inner Some **)
    admit.
  }
}

{(** write crashed **)
  invert_exec.
  repeat eapply bind_reorder_r in H14.
  invert_step_crash.
  {
    unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
    invert_step_crash.
    invert_step_crash.
    { solve_termination. }
    {
      invert_step_crash.
      cleanup; repeat invert_step_crash;
      solve_termination.
    }
    {
      invert_step_crash; solve_termination.
    }
  }
  {
    unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
    {
      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].


      (* write_inner_crashed *)
      Transparent write_inner Inode.get_block_number Inode.InodeAllocator.read.
      unfold write_inner, Inode.get_block_number, 
      Inode.InodeAllocator.read in *; simpl in *.
      unfold Inode.InodeAllocator.read in *; simpl in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      unfold DiskAllocator.write in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      
      (* write_inner_finished*)
      simpl in *.
      unfold Inode.InodeAllocator.read in *.
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      unfold DiskAllocator.write in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { XXXXX
        match goal with
        [H: refines ?s1 ?x,
        H0: refines ?s2 ?x0, 
        H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))) in A;
          unfold SSECommon.AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
        end.
        repeat match goal with
        |  [A: fst ?x = fst ?y,
        A0: snd ?x = snd ?y |- _] =>
        assert(x = y); [repeat cleanup_pairs; eauto|];
          subst; clear A A0
        end.
        match goal with
        [A : SSECommon.AD_related_states _ _ _ _ -> 
        exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
          edestruct A; clear A
        end;
          [ unfold SSECommon.AD_related_states, refines_related, FD_related_states;
            do 2 eexists; intuition eauto;
            simpl in *; unfold refines in *;
            repeat cleanup_pairs;
            unfold files_rep in *; 
            cleanup; simpl in *; 
            subst; eauto
          |].
        try match goal with
          [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
            exists (Recovered (extract_state_r s2'));
            econstructor_recovery; [|
              instantiate (1 := s2); eauto ]
        end.
          repeat eapply bind_reorder_l;
     
            repeat eapply bind_reorder_l;
            repeat exec_step.
            substitute_facts.
            repeat cleanup_pairs.
            subst.
            repeat exec_step.
            substitute_facts.
            simpl.

            repeat eapply bind_reorder_l;
  rewrite cons_app; econstructor;
  [try solve [repeat econstructor; eauto] 
  | try solve [repeat econstructor; eauto] ].
  repeat econstructor; eauto.
  eapply inode_owners_are_same.
  substitute_facts.


            repeat exec_step.
          repeat eapply bind_reorder_l;
          try solve[
            eauto;
          repeat (rewrite cons_app;
          eapply ExecBindCrash);
          repeat cleanup_pairs;
          repeat econstructor; eauto].
      
      
      
      
      
      
      
      
      
      
      
      
      
      solve_termination. }

      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      unfold DiskAllocator.write in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }

      { solve_termination_after_commit. }

        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].

        { solve_termination_after_commit. }
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination. }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort. }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination.
          simpl.
          repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat eapply bind_reorder_l.
          rewrite cons_app;
          econstructor; eauto.
          do 2 econstructor.
          eapply AuthenticationLayer.ExecAuthFail.
          erewrite <- inode_owners_are_same; eauto;
          congruence.
          try solve[
          repeat (rewrite cons_app;
          eapply ExecBindCrash);
          repeat cleanup_pairs;
          repeat econstructor; eauto]. }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.
          simpl.
          repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat eapply bind_reorder_l.
          rewrite cons_app;
          econstructor; eauto.
          do 2 econstructor.
          eapply AuthenticationLayer.ExecAuthFail.
          erewrite <- inode_owners_are_same; eauto;
          congruence.
          repeat eapply bind_reorder_l;
          repeat exec_step;
          try solve[
          repeat (rewrite cons_app;
          eapply ExecBindCrash);
          repeat cleanup_pairs;
          repeat econstructor; eauto]. }
    }
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    cleanup; try solve [solve_illegal_state].
    invert_step; try solve [solve_illegal_state].
    invert_step; try solve [solve_illegal_state].
    invert_step; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination_after_abort. }
    invert_step; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination_after_abort. }
  }
}
Admitted.
