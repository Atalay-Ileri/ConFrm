Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language TSCommon.

  (******** TS PROOFS ********)

Theorem Termination_Sensitive_read:
  forall u u' m inum off,
    Termination_Sensitive
      u (read inum off) (read inum off) recover
      AD_valid_state (AD_related_states u' None)
      (authenticated_disk_reboot_list m).
Proof. Admitted. (* Redo this proof
  Opaque read_inner.
  unfold Termination_Sensitive, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  read, auth_then_exec;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**read finished **)
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
        exists (RFinished (fst s2, (Empty, (snd (snd (snd s2)), snd (snd (snd s2))))) None).
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
        exists (RFinished (fst s2, (Empty, (snd (snd (snd s2)), snd (snd (snd s2))))) None).
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
        exists (RFinished (fst s2, (Empty, (snd (snd (snd s2)), snd (snd (snd s2))))) None).
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
  2: {(** read_inner None **)
    unfold  Inode.get_owner in *; simpl in *.
    eapply bind_reorder in H10.
    repeat invert_step;
    unfold Inode.InodeAllocator.read in *;
    repeat invert_step.
    {
      Transparent read_inner.
      unfold read_inner in *.
      repeat invert_step.
      {
        Transparent Inode.get_block_number.
        unfold Inode.get_block_number in *.
        repeat invert_step.
        unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
        repeat invert_step; 
        
        unfold DiskAllocator.read in *; cleanup; try congruence;
        repeat invert_step; try congruence; try lia.
        { symmetry in H20; solve_illegal_state. }
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
          exists (RFinished (fst s2, (Empty, (snd (snd (snd s2)), snd (snd (snd s2))))) None).
            econstructor.
            repeat exec_step.
            repeat cleanup_pairs.
            erewrite <- inode_allocations_are_same.
            4: eauto.
            all: eauto.
            simpl; rewrite D0.
            repeat exec_step.
            simpl; repeat econstructor.
            erewrite inode_owners_are_same'.
            7: instantiate (1:= (s, (t1, (t, t0))) ); simpl; eauto.
            4: eauto.
            all: eauto.
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
        }
      }
    }
  }
  {(** read_inner Some **)
  unfold  Inode.get_owner in *; simpl in *.
  eapply bind_reorder in H10.
  repeat invert_step;
  unfold Inode.InodeAllocator.read in *;
  repeat invert_step.
  {
    Transparent read_inner.
    unfold read_inner in *.
    repeat invert_step.

    Transparent Inode.get_block_number.
    unfold Inode.get_block_number in *.
    repeat invert_step.
    unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
    repeat invert_step; 
    
    unfold DiskAllocator.read in *; cleanup; try congruence;
    repeat invert_step; try congruence; try lia.

        exists (RFinished (fst s2, (Empty, (fst (snd (snd s2)), fst (snd (snd s2))))) (Some (fst (snd (snd s2)) (DiskAllocatorParams.bitmap_addr + S (nth off
        (Inode.block_numbers
           (Inode.decode_inode
              (fst (snd (snd s2))
                 (Inode.InodeAllocatorParams.bitmap_addr +
                  S inum)))) 0))))).
          econstructor.
          repeat exec_step.
          repeat cleanup_pairs.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          simpl; rewrite D1.
          repeat exec_step.
          simpl; repeat econstructor.
          erewrite inode_owners_are_same'.
          7: instantiate (1:= (s, (t1, (t, t0))) ); simpl; eauto.
          4: eauto.
          all: eauto.
          repeat exec_step.
          repeat cleanup_pairs.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          simpl; rewrite D1.
          repeat exec_step.
          destruct_fresh (nth_error
          (Inode.block_numbers
             (Inode.decode_inode
                (fst (snd (snd s2))
                   (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) off).
          setoid_rewrite D3.
          repeat exec_step.
          {
            
          simpl.

          repeat eapply bind_reorder_l.
          
          rewrite cons_app.
          setoid_rewrite cons_app at 3. 
          rewrite app_assoc.
          setoid_rewrite cons_app at 5. 
          rewrite app_assoc.
           econstructor; 
          [try solve [repeat econstructor; eauto] 
          | try solve [repeat econstructor; eauto] ].
          eapply nth_error_nth in D3.
          instantiate (1:= 0) in D3.
          rewrite <- D3 in *.
          destruct (Compare_dec.lt_dec (nth off
          (Inode.block_numbers
             (Inode.decode_inode
                (fst (snd (snd s2)) 
                   (Inode.InodeAllocatorParams.bitmap_addr +
                    S inum)))) 0) DiskAllocatorParams.num_of_blocks).
          simpl in *; repeat exec_step.
          simpl; setoid_rewrite used_blocks_are_allocated; eauto.
          repeat eapply bind_reorder_l.
          rewrite cons_app.
           econstructor; 
          [try solve [repeat econstructor; eauto] 
          | try solve [repeat econstructor; eauto] ].
          repeat econstructor.
          eapply data_block_inbounds; eauto.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          exfalso; apply n;
          eapply block_nums_inbound; eauto.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          repeat exec_step.
          }
          {
            apply nth_error_None in D3.
            symmetry in H17; 
            eapply block_numbers_in_length in H4; eauto.
            try lia.
          }
  }
  }
}

{(** read crashed **)
  invert_exec.
  repeat eapply bind_reorder_r in H14.
  invert_step_crash.
  { solve_termination. }
    {
      invert_step_crash.
      cleanup; repeat invert_step_crash; solve_termination.
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
      unfold DiskAllocator.read in *.
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
      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }

      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { solve_termination. }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      unfold DiskAllocator.read in *.
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
        { solve_termination.
        repeat invert_exec; simpl in *; eauto.
        clear H5.
        repeat invert_exec_no_match; simpl in *; eauto.
        eapply ExecBindCrash; repeat econstructor; eauto.
        destruct s2; simpl in *;
        repeat econstructor. }
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
Unshelve.
all: exact AD.
Qed. 
*)