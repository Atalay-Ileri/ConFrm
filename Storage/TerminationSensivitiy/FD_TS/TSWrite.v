Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language TSCommon.

  (******** TS PROOFS ********)

Theorem Termination_Sensitive_write:
  forall u u' m inum off v1 ex,
    Termination_Sensitive
      u (write inum off v1) (write inum off v1) recover
      AD_valid_state (AD_related_states u' ex)
      (authenticated_disk_reboot_list m).
Proof. Admitted. (*
  Opaque write_inner.
  unfold Termination_Sensitive, AD_valid_state,
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
  2: { (* Write inner none *)
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
            erewrite nth_error_nth' with (d:= 0).
            destruct_fresh (Compare_dec.lt_dec (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  (fst (snd s2)
                     (Inode.InodeAllocatorParams.bitmap_addr +
                      S inum)))) 0) DiskAllocatorParams.num_of_blocks).
            setoid_rewrite D4.
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
          simpl in *; repeat exec_step.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          exfalso; apply n;
          eapply block_nums_inbound; eauto.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
        }
        { symmetry in H16; solve_illegal_state. }
        {
            unfold DiskAllocatorParams.bitmap_addr,
            DiskAllocatorParams.num_of_blocks in *.
            apply nth_error_None in D3.
            rewrite value_to_bits_length in D3.
            pose proof DiskAllocatorParams.num_of_blocks_in_bounds; lia.
        }
        { symmetry in H16; solve_illegal_state. }
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
        }
      }
    }
  }
  {(** write_inner Some **)
  unfold  Inode.get_owner in *; simpl in *.
    eapply bind_reorder in H10.
    repeat invert_step;
    unfold Inode.InodeAllocator.read in *;
    repeat invert_step.

    Transparent write_inner.
    unfold write_inner in *.
    repeat invert_step.

    Transparent Inode.get_block_number.
    unfold Inode.get_block_number in *.
    repeat invert_step.
    unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
    repeat invert_step; 
    
    unfold DiskAllocator.write in *; cleanup; try congruence;
    repeat invert_step; try congruence; try lia.

    exists (RFinished (fst s2, (upd
    (fst (snd s2))
    (DiskAllocatorParams.bitmap_addr +
     S
       (nth off
          (Inode.block_numbers
            (Inode.decode_inode
            (fst
            (snd s2)
            (Inode.InodeAllocatorParams.bitmap_addr +
            S inum))))
          0)) v1, upd
          (fst (snd s2))
          (DiskAllocatorParams.bitmap_addr +
           S
             (nth off
                (Inode.block_numbers
                  (Inode.decode_inode
                  (fst
                  (snd s2)
                  (Inode.InodeAllocatorParams.bitmap_addr +
                  S inum))))
                0)) v1)) (Some tt)).
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
          7: instantiate (1:= (s, (t, t0)) ); simpl; eauto.
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
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) off).
          setoid_rewrite D3.
          repeat exec_step.
          {
          simpl.
          repeat eapply bind_reorder_l.
          
          rewrite cons_app.
          setoid_rewrite cons_app at 3. 
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
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr +
                    S inum)))) 0) DiskAllocatorParams.num_of_blocks).
          simpl in *; repeat exec_step.
          simpl; setoid_rewrite used_blocks_are_allocated; eauto.
          repeat eapply bind_reorder_l.
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
      { match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end;
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end;
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end;
        [ unfold AD_related_states, refines_related, FD_related_states;
          do 2 eexists; intuition eauto;
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *; 
          cleanup; simpl in *; 
          subst; eauto
        |].
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v1, snd (snd s2)))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
  [| | | eauto | |];
  try match goal with
      | [|- refines _ _ ] =>
      eauto
      end; eauto;
  try solve [repeat cleanup_pairs; simpl; eauto].


  repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }

      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { 
      match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v1, upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v1))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end.
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end.
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end.
      destruct_fresh (x inum).
      {
        destruct_fresh (x0 inum).
        {
          unfold AD_related_states, refines_related, FD_related_states.
          exists (Mem.upd x inum (update_file f off v1)), (Mem.upd x0 inum (update_file f0 off v1)).
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *; 
          cleanup; simpl in *; 
          intuition eauto.
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              instantiate (1:= Mem.upd x4 a v1).
              eapply blocks_allocator_rep_upd; eauto.
            }
            {
              
                eapply file_map_rep_upd; eauto.
                destruct_fresh (x2 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
                split_ors; cleanup;
                rewrite H15, H17 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
                split_ors; cleanup;
                rewrite H15, H17 in D6; simpl in *; try congruence.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D; 
                rewrite H2 in D; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
              erewrite <- used_blocks_are_allocated with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))).
              simpl; eauto. 
              all: simpl; eauto.
              unfold refines, files_rep, files_inner_rep; simpl; 
              intuition eauto.

              eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              pose proof (block_nums_inbound inum off (fst s2, (snd (snd s2), snd (snd s2)))) as Hp.
               simpl in *; eapply Hp.
               unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
            }
            {
                eapply file_map_rep_upd; eauto.
                eapply nth_error_nth'; eauto.
                
                eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                simpl; eauto.
                simpl; eauto.

                destruct_fresh (x1 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H10 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply_fresh Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H21 in D6; simpl in *; try congruence.
                erewrite inode_allocations_are_same with (t2:= snd (snd s2)) in D.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D. 
                setoid_rewrite H2 in D; congruence.
                instantiate (1:= x);
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                instantiate (1:= x0);
                instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                simpl; eauto.
                simpl; eauto.
                eauto.
                eauto.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            instantiate (1:= ex).
           
            unfold same_for_user_except, addrs_match_exactly in *; cleanup.
            simpl; split; intros.
            destruct (addr_dec a0 inum); subst.
            repeat rewrite Mem.upd_eq; eauto.
            intuition congruence.
            repeat rewrite Mem.upd_ne; eauto.
            simpl; split; intros.
            destruct (addr_dec inum0 inum); subst;
            try solve [intuition].
            rewrite Mem.upd_eq in H5, H6; eauto.
            cleanup.
            eapply H2 in D4; eauto; subst; eauto.
            rewrite Mem.upd_ne in H5, H6; eauto.
            destruct (addr_dec inum0 inum); subst.
            rewrite Mem.upd_eq in H4, H5; eauto.
            cleanup.
            unfold update_file in *; simpl; 
            repeat rewrite updn_length; eauto.
            rewrite Mem.upd_ne in H4, H5; eauto.
          }
        }
        {
          unfold same_for_user_except in *; cleanup.
          edestruct H1; exfalso. 
          eapply H10; eauto; congruence.
        }
      }
      {
        unfold refines, files_rep, files_inner_rep, file_map_rep in *; cleanup.
        destruct_fresh (x5 inum).
        edestruct H21; exfalso.
        eapply H27; eauto; congruence.
        unfold Inode.inode_rep, Inode.InodeAllocator.block_allocator_rep in *; cleanup.
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H31; eauto.
        cleanup; split_ors; cleanup;
        repeat cleanup_pairs; cleanup.
        rewrite nth_seln_eq in *.
        eapply nth_error_nth in D.
        rewrite H17 in D; congruence.
        unfold Inode.inode_map_rep in *; cleanup.
        rewrite H5, H31 in D5; simpl in *; congruence.
        lia.
        rewrite value_to_bits_length. 
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; 
        unfold Inode.InodeAllocatorParams.num_of_blocks in *. lia.
      }
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v1, upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v1))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
          [| | | eauto | |];
          try match goal with
              | [|- refines _ _ ] =>
              eauto
              end; eauto;
          try solve [repeat cleanup_pairs; simpl; eauto].


        repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.
        simpl.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      unfold DiskAllocator.write in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { 
      match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2, upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end.
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end.
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end.
      destruct_fresh (x inum).
      {
        destruct_fresh (x0 inum).
        {
          unfold AD_related_states, refines_related, FD_related_states.
          exists (Mem.upd x inum (update_file f off v1)), (Mem.upd x0 inum (update_file f0 off v1)).
          instantiate (2:=(fst s2, (upd (fst (snd s2)) (DiskAllocatorParams.bitmap_addr + 
          S (nth off
          (Inode.block_numbers
             (Inode.decode_inode
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr + S inum))))
          0)) v1, upd (fst (snd s2)) (DiskAllocatorParams.bitmap_addr + 
          S (nth off
          (Inode.block_numbers
             (Inode.decode_inode
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr + S inum))))
          0)) v1))).
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *;
          simpl; intuition eauto;
          cleanup; simpl in *;
          intuition eauto.
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
            }
            {
              eapply file_map_rep_upd; eauto.
              destruct_fresh (x2 inum).
              unfold Inode.inode_rep, Inode.inode_map_rep,
              Inode.InodeAllocator.block_allocator_rep in *; cleanup.
              eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H18; eauto; cleanup.
              split_ors; cleanup;
              rewrite H16, H18 in D6; simpl in *; congruence.
              eauto.
              rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
              unfold Inode.inode_rep, Inode.inode_map_rep,
              Inode.InodeAllocator.block_allocator_rep in *; cleanup.
              eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H18; eauto; cleanup.
              split_ors; cleanup;
              rewrite H16, H18 in D6; simpl in *; try congruence.
              eapply nth_error_nth in D; eauto.
              rewrite <- nth_seln_eq in D; 
              rewrite H3 in D; congruence.
              eauto.
              rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
              unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.            }
          }
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; intuition eauto.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
              erewrite <- used_blocks_are_allocated with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))).
              simpl; eauto. 
              all: simpl; eauto.
              unfold refines, files_rep, files_inner_rep; simpl; 
              intuition eauto.

              eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              pose proof (block_nums_inbound inum off (fst s2, (snd (snd s2), snd (snd s2)))) as Hp.
               simpl in *; eapply Hp.
               unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
            }
            {
                eapply file_map_rep_upd; eauto.
                eapply nth_error_nth'; eauto.
                
                eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                simpl; eauto.
                simpl; eauto.

                destruct_fresh (x1 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H11 ; eauto; cleanup.
                split_ors; cleanup;
                rewrite H5, H11 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply_fresh Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H11; eauto; cleanup.
                split_ors; cleanup;
                rewrite H5, H23 in D6; simpl in *; try congruence.
                erewrite inode_allocations_are_same with (t2:= snd (snd s2)) in D.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D. 
                setoid_rewrite H3 in D; congruence.
                instantiate (1:= x);
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                instantiate (1:= x0);
                instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                simpl; eauto.
                simpl; eauto.
                eauto.
                eauto.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            instantiate (1:= ex).
            unfold same_for_user_except, addrs_match_exactly in *; cleanup.
            simpl; split; intros.
            destruct (addr_dec a0 inum); subst.
            repeat rewrite Mem.upd_eq; eauto.
            intuition congruence.
            repeat rewrite Mem.upd_ne; eauto.
            simpl; split; intros.
            destruct (addr_dec inum0 inum); subst;
            try solve [intuition].
            rewrite Mem.upd_eq in H8, H9; eauto.
            cleanup.
            eapply H4 in D4; eauto; subst; eauto.
            rewrite Mem.upd_ne in H8, H9; eauto.
            destruct (addr_dec inum0 inum); subst.
            rewrite Mem.upd_eq in H1, H8; eauto.
            cleanup.
            unfold update_file in *; simpl; 
            repeat rewrite updn_length; eauto.
            rewrite Mem.upd_ne in H1, H8; eauto.
          }
        }
        {
          unfold same_for_user_except in *; cleanup.
          edestruct H1; exfalso. 
          eapply H10; eauto; congruence.
        }
      }
      {
        unfold refines, files_rep, files_inner_rep, file_map_rep in *; cleanup.
        destruct_fresh (x5 inum).
        edestruct H21; exfalso.
        eapply H27; eauto; congruence.
        unfold Inode.inode_rep, Inode.InodeAllocator.block_allocator_rep in *; cleanup.
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H31; eauto.
        cleanup; split_ors; cleanup;
        repeat cleanup_pairs; cleanup.
        rewrite nth_seln_eq in *.
        eapply nth_error_nth in D.
        rewrite H17 in D; congruence.
        unfold Inode.inode_map_rep in *; cleanup.
        rewrite H5, H31 in D5; simpl in *; congruence.
        lia.
        rewrite value_to_bits_length. 
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; 
        unfold Inode.InodeAllocatorParams.num_of_blocks in *. lia.
      }
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v1, upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v1))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
          [| | | eauto | |];
          try match goal with
              | [|- refines _ _ ] =>
              eauto
              end; eauto;
          try solve [repeat cleanup_pairs; simpl; eauto].


        repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        simpl; repeat exec_step;
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.
        simpl.
        
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }
      
      { solve_termination.
      repeat invert_exec; eauto.
      repeat invert_exec; eauto. }

        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        unfold DiskAllocator.write in *.
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination. }
        invert_step_crash; try solve [solve_illegal_state].
        unfold DiskAllocator.write in *.
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.  }
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination.  }
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.  }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination.
        erewrite <- inode_owners_are_same with (s1:= x4)(s2:= s2);
        [| | | eauto | |];
        try match goal with
            | [|- refines _ _ ] =>
            eauto
            end; eauto;
        try solve [repeat cleanup_pairs; simpl; eauto].
        repeat exec_step.
        simpl.
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].  }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.
        erewrite <- inode_owners_are_same with (s1:= x4)(s2:= s2);
        [| | | eauto | |];
        try match goal with
            | [|- refines _ _ ] =>
            eauto
            end; eauto;
        try solve [repeat cleanup_pairs; simpl; eauto].
        repeat exec_step.
        }
  }
  {
    invert_exec; cleanup.
    invert_exec; cleanup.
  }
  {
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination_after_abort. }
  }
  { 
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
all: eauto; exact AD.
Qed.
*)

Theorem Termination_Sensitive_write_input:
  forall u u' m inum off v1 v2,
    Termination_Sensitive
      u (write inum off v1) (write inum off v2) recover
      AD_valid_state (AD_related_states u' (Some inum))
      (authenticated_disk_reboot_list m).
Proof. Admitted. (*
  Opaque write_inner Inode.get_owner Inode.get_block_number.
  unfold Termination_Sensitive, AD_valid_state,
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
  2: { (* Write inner none *)
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
            erewrite nth_error_nth' with (d:= 0).
            destruct_fresh (Compare_dec.lt_dec (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  (fst (snd s2)
                     (Inode.InodeAllocatorParams.bitmap_addr +
                      S inum)))) 0) DiskAllocatorParams.num_of_blocks).
            setoid_rewrite D4.
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
          simpl in *; repeat exec_step.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
          exfalso; apply n;
          eapply block_nums_inbound; eauto.
          erewrite <- inode_allocations_are_same.
          4: eauto.
          all: eauto.
        }
        { symmetry in H16; solve_illegal_state. }
        {
            unfold DiskAllocatorParams.bitmap_addr,
            DiskAllocatorParams.num_of_blocks in *.
            apply nth_error_None in D3.
            rewrite value_to_bits_length in D3.
            pose proof DiskAllocatorParams.num_of_blocks_in_bounds; lia.
        }
        { symmetry in H16; solve_illegal_state. }
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
        }
      }
    }
  }
  {(** write_inner Some **)
  unfold  Inode.get_owner in *; simpl in *.
    eapply bind_reorder in H10.
    repeat invert_step;
    unfold Inode.InodeAllocator.read in *;
    repeat invert_step.

    Transparent write_inner.
    unfold write_inner in *.
    repeat invert_step.

    Transparent Inode.get_block_number.
    unfold Inode.get_block_number in *.
    repeat invert_step.
    unfold Inode.InodeAllocator.read in *; cleanup; try congruence.
    repeat invert_step; 
    
    unfold DiskAllocator.write in *; cleanup; try congruence;
    repeat invert_step; try congruence; try lia.

    exists (RFinished (fst s2, (upd
    (fst (snd s2))
    (DiskAllocatorParams.bitmap_addr +
     S
       (nth off
          (Inode.block_numbers
            (Inode.decode_inode
            (fst
            (snd s2)
            (Inode.InodeAllocatorParams.bitmap_addr +
            S inum))))
          0)) v2, upd
          (fst (snd s2))
          (DiskAllocatorParams.bitmap_addr +
           S
             (nth off
                (Inode.block_numbers
                  (Inode.decode_inode
                  (fst
                  (snd s2)
                  (Inode.InodeAllocatorParams.bitmap_addr +
                  S inum))))
                0)) v2)) (Some tt)).
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
          7: instantiate (1:= (s, (t, t0)) ); simpl; eauto.
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
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) off).
          setoid_rewrite D3.
          repeat exec_step.
          {
          simpl.
          repeat eapply bind_reorder_l.
          
          rewrite cons_app.
          setoid_rewrite cons_app at 3. 
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
                (fst (snd s2)
                   (Inode.InodeAllocatorParams.bitmap_addr +
                    S inum)))) 0) DiskAllocatorParams.num_of_blocks).
          simpl in *; repeat exec_step.
          simpl; setoid_rewrite used_blocks_are_allocated; eauto.
          repeat eapply bind_reorder_l.
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
      { match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end;
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end;
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end;
        [ unfold AD_related_states, refines_related, FD_related_states;
          do 2 eexists; intuition eauto;
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *; 
          cleanup; simpl in *; 
          subst; eauto
        |].
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v2, snd (snd s2)))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
  [| | | eauto | |];
  try match goal with
      | [|- refines _ _ ] =>
      eauto
      end; eauto;
  try solve [repeat cleanup_pairs; simpl; eauto].


  repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }

      invert_step; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { 
      match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2, upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end.
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end.
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end.
      destruct_fresh (x inum).
      {
        destruct_fresh (x0 inum).
        {
          unfold AD_related_states, refines_related, FD_related_states.
          exists (Mem.upd x inum (update_file f off v1)), (Mem.upd x0 inum (update_file f0 off v2)).
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *; 
          cleanup; simpl in *; 
          intuition eauto.
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              instantiate (1:= Mem.upd x4 a v1).
              eapply blocks_allocator_rep_upd; eauto.
            }
            {
                eapply file_map_rep_upd; eauto.
                destruct_fresh (x2 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
                split_ors; cleanup;
                rewrite H15, H17 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
                split_ors; cleanup;
                rewrite H15, H17 in D6; simpl in *; try congruence.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D; 
                rewrite H2 in D; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
              erewrite <- used_blocks_are_allocated with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))).
              simpl; eauto. 
              all: simpl; eauto.
              unfold refines, files_rep, files_inner_rep; simpl; 
              intuition eauto.

              eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              pose proof (block_nums_inbound inum off (fst s2, (snd (snd s2), snd (snd s2)))) as Hp.
               simpl in *; eapply Hp.
               unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
            }
            {
                eapply file_map_rep_upd; eauto.
                eapply nth_error_nth'; eauto.
                
                eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                simpl; eauto.
                simpl; eauto.

                destruct_fresh (x1 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H10 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply_fresh Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H21 in D6; simpl in *; try congruence.
                erewrite inode_allocations_are_same with (t2:= snd (snd s2)) in D.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D. 
                setoid_rewrite H2 in D; congruence.
                instantiate (1:= x);
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                instantiate (1:= x0);
                instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                simpl; eauto.
                simpl; eauto.
                eauto.
                eauto.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            instantiate (1:= Some inum).
            unfold same_for_user_except, addrs_match_exactly in *; cleanup.
            simpl; split; intros.
            destruct (addr_dec a0 inum); subst.
            repeat rewrite Mem.upd_eq; eauto.
            intuition congruence.
            repeat rewrite Mem.upd_ne; eauto.
            simpl; split; intros.
            destruct (addr_dec inum0 inum); subst;
            try solve [intuition].
            rewrite Mem.upd_ne in H5, H6; eauto.

            destruct (addr_dec inum0 inum); subst.
            rewrite Mem.upd_eq in H4, H5; eauto.
            cleanup.
            unfold update_file; simpl; 
            repeat rewrite updn_length.
            eapply H3; eauto.
            rewrite Mem.upd_ne in H4, H5; eauto.
          }
        }
        {
          unfold same_for_user_except in *; cleanup.
          edestruct H1; exfalso. 
          eapply H10; eauto; congruence.
        }
      }
      {
        unfold refines, files_rep, files_inner_rep, file_map_rep in *; cleanup.
        destruct_fresh (x5 inum).
        edestruct H21; exfalso.
        eapply H27; eauto; congruence.
        unfold Inode.inode_rep, Inode.InodeAllocator.block_allocator_rep in *; cleanup.
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H31; eauto.
        cleanup; split_ors; cleanup;
        repeat cleanup_pairs; cleanup.
        rewrite nth_seln_eq in *.
        eapply nth_error_nth in D.
        rewrite H17 in D; congruence.
        unfold Inode.inode_map_rep in *; cleanup.
        rewrite H5, H31 in D5; simpl in *; congruence.
        lia.
        rewrite value_to_bits_length. 
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; 
        unfold Inode.InodeAllocatorParams.num_of_blocks in *. lia.
      }
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v2, upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v2))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
          [| | | eauto | |];
          try match goal with
              | [|- refines _ _ ] =>
              eauto
              end; eauto;
          try solve [repeat cleanup_pairs; simpl; eauto].


        repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.
        simpl.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }
      invert_step_crash; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      unfold DiskAllocator.write in *.
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      cleanup; try solve [solve_illegal_state].
      invert_step_crash; try solve [solve_illegal_state].
      { 
      match goal with
      [H: refines ?s1 ?x,
      H0: refines ?s2 ?x0, 
      H1: same_for_user_except _ _ ?x ?x0,
      A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
        eapply Termination_Sensitive_recover in A;
        try instantiate (1:= (fst s2, (upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2, upd (fst (snd s2))
        (DiskAllocatorParams.bitmap_addr +
         S
           (nth off
              (Inode.block_numbers
                 (Inode.decode_inode
                    (fst (snd s2) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
        v2))) in A;
        unfold AD_valid_state, refines_valid, FD_valid_state; 
        intros; eauto
      end.
      repeat match goal with
      |  [A: fst ?x = fst ?y,
      A0: snd ?x = snd ?y |- _] =>
      assert(x = y); [repeat cleanup_pairs; eauto|];
        subst; clear A A0
      end.
      match goal with
      [A : AD_related_states _ _ _ _ -> 
      exists _, recovery_exec _ _ _ _ _ _ _ _ |- _] =>  
        edestruct A; clear A
      end.
      destruct_fresh (x inum).
      {
        destruct_fresh (x0 inum).
        {
          unfold AD_related_states, refines_related, FD_related_states.
          exists (Mem.upd x inum (update_file f off v1)), (Mem.upd x0 inum (update_file f0 off v2)).
          simpl in *; unfold refines in *;
          repeat cleanup_pairs;
          unfold files_rep in *; 
          cleanup; simpl in *; 
          intuition eauto.
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
            }
            {
              eapply file_map_rep_upd; eauto.
              destruct_fresh (x2 inum).
              unfold Inode.inode_rep, Inode.inode_map_rep,
              Inode.InodeAllocator.block_allocator_rep in *; cleanup.
              eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
              split_ors; cleanup;
              rewrite H15, H17 in D6; simpl in *; congruence.
              eauto.
              rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
              unfold Inode.inode_rep, Inode.inode_map_rep,
              Inode.InodeAllocator.block_allocator_rep in *; cleanup.
              eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H17; eauto; cleanup.
              split_ors; cleanup;
              rewrite H15, H17 in D6; simpl in *; try congruence.
              eapply nth_error_nth in D; eauto.
              rewrite <- nth_seln_eq in D; 
              rewrite H2 in D; congruence.
              eauto.
              rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
              unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.            }
          }
          {
            unfold files_inner_rep in *; cleanup.
            eexists; intuition eauto. 
            unfold Inode.inode_rep in *; cleanup.
            eexists; split.
            eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; [|
            intros; rewrite upd_ne; eauto].
            eauto.
            cleanup. 
            unfold Inode.InodeAllocatorParams.bitmap_addr, 
            DiskAllocatorParams.bitmap_addr, Inode.InodeAllocatorParams.num_of_blocks,
            DiskAllocatorParams.num_of_blocks in *.
            pose proof FSParameters.inodes_before_data; lia.
            eauto.
            
            eexists; split.
            {
              eapply blocks_allocator_rep_upd; eauto.
              erewrite <- used_blocks_are_allocated with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))).
              simpl; eauto. 
              all: simpl; eauto.
              unfold refines, files_rep, files_inner_rep; simpl; 
              intuition eauto.

              eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              pose proof (block_nums_inbound inum off (fst s2, (snd (snd s2), snd (snd s2)))) as Hp.
               simpl in *; eapply Hp.
               unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
              erewrite <- inode_allocations_are_same with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
              instantiate (1:= (tt, (t0, t0))).
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              unfold refines, files_rep, files_inner_rep; simpl.
              intuition eauto.
              simpl; eauto.
            }
            {
                eapply file_map_rep_upd; eauto.
                eapply nth_error_nth'; eauto.
                
                eapply block_numbers_in_length  with (s2:= (fst s2, (snd (snd s2), snd (snd s2)))); eauto.
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                unfold refines, files_rep, files_inner_rep; simpl.
                intuition eauto.
                simpl; eauto.
                simpl; eauto.

                destruct_fresh (x1 inum).
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H10 in D6; simpl in *; congruence.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep in *; cleanup.
                eapply_fresh Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H10; eauto; cleanup.
                split_ors; cleanup;
                rewrite H8, H21 in D6; simpl in *; try congruence.
                erewrite inode_allocations_are_same with (t2:= snd (snd s2)) in D.
                eapply nth_error_nth in D; eauto.
                rewrite <- nth_seln_eq in D. 
                setoid_rewrite H2 in D; congruence.
                instantiate (1:= x);
                instantiate (1:= (tt, (t0, t0))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                instantiate (1:= x0);
                instantiate (1:= (fst s2, (snd (snd s2), snd (snd s2)))).
                unfold refines, files_rep, files_inner_rep,
                Inode.inode_rep, Inode.inode_map_rep,
                Inode.InodeAllocator.block_allocator_rep; simpl.
                intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                eexists; intuition eauto.
                simpl; eauto.
                simpl; eauto.
                eauto.
                eauto.
                eauto.
                rewrite value_to_bits_length; apply Inode.InodeAllocatorParams.num_of_blocks_in_bounds.
                unfold Inode.inode_rep, Inode.inode_map_rep in *; cleanup; eauto.
            }
          }
          {
            instantiate (1:= Some inum).
            unfold same_for_user_except, addrs_match_exactly in *; cleanup.
            simpl; split; intros.
            destruct (addr_dec a0 inum); subst.
            repeat rewrite Mem.upd_eq; eauto.
            intuition congruence.
            repeat rewrite Mem.upd_ne; eauto.
            simpl; split; intros.
            destruct (addr_dec inum0 inum); subst;
            try solve [intuition].
            rewrite Mem.upd_ne in H5, H6; eauto.

            destruct (addr_dec inum0 inum); subst.
            rewrite Mem.upd_eq in H4, H5; eauto.
            cleanup.
            unfold update_file; simpl; 
            repeat rewrite updn_length.
            eapply H3; eauto.
            rewrite Mem.upd_ne in H4, H5; eauto.
          }
        }
        {
          unfold same_for_user_except in *; cleanup.
          edestruct H1; exfalso. 
          eapply H10; eauto; congruence.
        }
      }
      {
        unfold refines, files_rep, files_inner_rep, file_map_rep in *; cleanup.
        destruct_fresh (x5 inum).
        edestruct H21; exfalso.
        eapply H27; eauto; congruence.
        unfold Inode.inode_rep, Inode.InodeAllocator.block_allocator_rep in *; cleanup.
        eapply Inode.InodeAllocator.valid_bits_extract with (n:= inum) in H31; eauto.
        cleanup; split_ors; cleanup;
        repeat cleanup_pairs; cleanup.
        rewrite nth_seln_eq in *.
        eapply nth_error_nth in D.
        rewrite H17 in D; congruence.
        unfold Inode.inode_map_rep in *; cleanup.
        rewrite H5, H31 in D5; simpl in *; congruence.
        lia.
        rewrite value_to_bits_length. 
        pose proof Inode.InodeAllocatorParams.num_of_blocks_in_bounds; 
        unfold Inode.InodeAllocatorParams.num_of_blocks in *. lia.
      }
      match goal with
        [A : recovery_exec _ _ _ (fst ?s2, _) _ _ _ ?s2' |- _] =>  
          exists (Recovered (extract_state_r s2'));
          econstructor_recovery; [|
          instantiate (1 := (fst s2, (upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v2, upd (fst (snd s2))
      (DiskAllocatorParams.bitmap_addr +
       S
         (nth off
            (Inode.block_numbers
               (Inode.decode_inode
                  ((fst (snd s2)) (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) 0))
      v2))); eauto]
      end;
        repeat eapply bind_reorder_l;
        repeat (
          repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        repeat eapply bind_reorder_l;
          repeat exec_step;
          repeat substitute_facts;
          erewrite inode_owners_are_same with (s1:= x8)(s2:= s2);
          [| | | eauto | |];
          try match goal with
              | [|- refines _ _ ] =>
              eauto
              end; eauto;
          try solve [repeat cleanup_pairs; simpl; eauto].


        repeat (repeat eapply bind_reorder_l;
          repeat exec_step;
          substitute_facts;
          repeat eapply bind_reorder_l;
          repeat exec_step);
        repeat eapply bind_reorder_l;
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].

        rewrite cons_app.
        repeat econstructor.
        eapply data_block_inbounds; eauto.
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
        simpl; repeat exec_step;
        rewrite cons_app;
        eapply ExecBindCrash;
        repeat cleanup_pairs;
        repeat econstructor; eauto.
        simpl.
        
        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        erewrite inode_allocations_are_same.
        4: eauto.
        all: eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.

        eapply Inode.nth_error_some_lt in D2.
        eapply block_numbers_in_length.
        3: eauto.
        all: eauto.
        repeat cleanup_pairs; eauto.
        eapply nth_error_nth'; eauto.
        repeat cleanup_pairs; eauto.
       }
      
      { solve_termination.
      repeat invert_exec; eauto.
      repeat invert_exec; eauto. }

        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        unfold DiskAllocator.write in *.
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination. }
        invert_step_crash; try solve [solve_illegal_state].
        unfold DiskAllocator.write in *.
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.  }
        invert_step_crash; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination.  }
        cleanup; try solve [solve_illegal_state].
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.  }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination.
        erewrite <- inode_owners_are_same with (s1:= x4)(s2:= s2);
        [| | | eauto | |];
        try match goal with
            | [|- refines _ _ ] =>
            eauto
            end; eauto;
        try solve [repeat cleanup_pairs; simpl; eauto].
        repeat exec_step.
        simpl.
        try solve[
          eauto;
        repeat (rewrite cons_app;
        eapply ExecBindCrash);
        repeat cleanup_pairs;
        repeat econstructor; eauto].  }
        invert_step_crash; try solve [solve_illegal_state].
        { solve_termination_after_abort.
        erewrite <- inode_owners_are_same with (s1:= x4)(s2:= s2);
        [| | | eauto | |];
        try match goal with
            | [|- refines _ _ ] =>
            eauto
            end; eauto;
        try solve [repeat cleanup_pairs; simpl; eauto].
        repeat exec_step.
        }
  }
  {
    invert_exec; cleanup.
    invert_exec; cleanup.
  }
  {
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    cleanup; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination. }
    invert_step_crash; try solve [solve_illegal_state].
    { solve_termination_after_abort. }
  }
  { 
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
all: eauto; exact AD.
Qed.

*)