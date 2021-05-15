Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType SSECommon InodeSSE.


Theorem SelfSimulation_Exists_create:
  forall u u' m own ex,
    SelfSimulation_Exists
      u (create own) (create own) recover
      AD_valid_state (AD_related_states u' ex)
      (authenticated_disk_reboot_list m).
Proof.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  create;
  intros; 
  unfold refines, files_rep in *; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**create finished **)
   invert_exec.
   repeat invert_step;
   eapply lift2_invert_exec in H10; cleanup.
   {
    unfold refines, files_rep in *; cleanup.
     eapply_fresh SSE_alloc_inode in H6; eauto.
     2: setoid_rewrite H2; eauto.
     2: setoid_rewrite H1; eauto.
     cleanup.
     destruct x2; simpl in *; try solve [intuition congruence].
    eapply_fresh Inode.alloc_finished_oracle_eq in H6; eauto.
    destruct o; simpl in *; try solve [intuition congruence].

    destruct s2.
    eexists; econstructor_recovery.
    econstructor.
    eapply lift2_exec_step; eauto.
    simpl; repeat exec_step.
   }
   {
    unfold refines, files_rep in *; cleanup.
    eapply_fresh SSE_alloc_inode in H6; eauto.
    2: setoid_rewrite H2; eauto.
    2: setoid_rewrite H1; eauto.
    cleanup.
    destruct x2; simpl in *; try solve [intuition congruence].
   eapply_fresh Inode.alloc_finished_oracle_eq in H6; eauto.
   destruct o; simpl in *; try solve [intuition congruence].

   destruct s2.
   eexists; econstructor_recovery.
   econstructor.
   eapply lift2_exec_step; eauto.
   simpl; repeat exec_step.
   }
  }
  {
    repeat invert_exec.
    repeat invert_step_crash.
    {
      unfold refines, files_rep in *; logic_clean.
    eapply lift2_invert_exec in H10; logic_clean.
    eapply_fresh SSE_alloc_inode with (v':= own) in H8; eauto.
    logic_clean.
    destruct x2; simpl in *; try solve [intuition congruence].
   eapply_fresh Inode.alloc_finished_oracle_eq in H8; eauto.

   unfold files_inner_rep in *; logic_clean.
   eapply_fresh Inode.alloc_finished in H8; eauto.
   eapply_fresh Inode.alloc_finished in H9; eauto.
   cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
   {
    repeat invert_step_crash.
    destruct s2, s2.
    match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (fst s, fst s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       econstructor.
       eapply lift2_exec_step; eauto.
       simpl; repeat exec_step.
       simpl in *; eauto.
    }
    {
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; split.
      split; eauto.
      unfold files_inner_rep; eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq.
      apply b0.
      intros; repeat solve_bounds.
      instantiate (1:= Mem.upd x x7 {| owner:= own; blocks := []|}).
      
      {
        unfold file_map_rep in *; cleanup; split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x7); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        {
          intros.
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H1, H3; eauto.
          cleanup.
          unfold file_rep; simpl; intuition eauto.
          assert (i1 < @length addr []). {
          eapply nth_error_Some; eauto.
          congruence.
          }
          simpl in *; lia.
          }
          {
            rewrite Mem.upd_ne in H1, H3; eauto.
          }
        }
      }
      split.
      split; eauto.
      {
        unfold files_inner_rep; eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq.
      apply b.
      intros; repeat solve_bounds.
        instantiate (1:= Mem.upd x0 x6 {| owner:= own; blocks := []|}).
        unfold file_map_rep in *; cleanup; split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x6); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        {
          intros.
          destruct (addr_dec inum x6); subst.
          {
          rewrite Mem.upd_eq in H1, H3; eauto.
          cleanup.
          unfold file_rep; simpl; intuition eauto.
          assert (i1 < @length addr []). {
          eapply nth_error_Some; eauto.
          congruence.
          }
          simpl in *; lia.
          }
          {
            rewrite Mem.upd_ne in H1, H3; eauto.
          }
        }
      }
      {
        unfold same_for_user_except in *; cleanup.
        assert (x6 = x7). {
          eapply FileInnerSpecs.inode_missing_then_file_missing in H21; eauto.
          eapply FileInnerSpecs.inode_missing_then_file_missing in H11; eauto.
          destruct (Compare_dec.lt_dec x6 x7).
          {
            exfalso; eapply H23; eauto.
            edestruct a.
            destruct_fresh (x3 x6); eauto.
            eapply FileInnerSpecs.inode_exists_then_file_exists in D; eauto; cleanup.
            exfalso; eapply H1; eauto.
            congruence.
          }
          {
            apply PeanoNat.Nat.nlt_ge in n.
            inversion n; eauto.
            exfalso; eapply H19 with (i:=x7).
            lia.
            edestruct a.
            destruct_fresh (x2 x7); eauto.
            eapply FileInnerSpecs.inode_exists_then_file_exists in D; eauto; cleanup.
            exfalso; eapply H6; eauto.
            congruence.
          }
        }
        subst.
        split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x7); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        split; intros.
        {
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H3, H4; eauto.
          cleanup.
          simpl; intuition eauto.
          }
          {
            rewrite Mem.upd_ne in H3, H4; eauto.
          }
        }
        {
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H3, H1; eauto.
          cleanup.
          simpl; intuition eauto.
          }
          {
            rewrite Mem.upd_ne in H3, H1; eauto.
          }
        }
      }
    }
    {
    repeat invert_step_crash.
    destruct s2, s2.
    match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (snd s, snd s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       econstructor.
       eapply lift2_exec_step; eauto.
       simpl; repeat exec_step.
       rewrite cons_app;
       eapply ExecBindCrash; 
       repeat econstructor.
       simpl in *; eauto.
    }
    {
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
      unfold files_inner_rep; eexists; split; eauto.
      repeat cleanup_pairs.
      unfold files_inner_rep; eexists; split; eauto.
    }
  }
  {
    repeat invert_step_crash.
    destruct s2, s2.
    match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (fst s, fst s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       econstructor.
       eapply lift2_exec_step; eauto.
       simpl; repeat exec_step.
       rewrite cons_app;
       eapply ExecBindCrash;
       repeat econstructor.
       simpl in *; eauto.
    }
    {
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; split.
      split; eauto.
      unfold files_inner_rep; eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq.
      apply b0.
      intros; repeat solve_bounds.
      instantiate (1:= Mem.upd x x7 {| owner:= own; blocks := []|}).
      
      {
        unfold file_map_rep in *; cleanup; split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x7); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        {
          intros.
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H1, H3; eauto.
          cleanup.
          unfold file_rep; simpl; intuition eauto.
          assert (i1 < @length addr []). {
          eapply nth_error_Some; eauto.
          congruence.
          }
          simpl in *; lia.
          }
          {
            rewrite Mem.upd_ne in H1, H3; eauto.
          }
        }
      }
      split.
      split; eauto.
      {
        unfold files_inner_rep; eexists; split; eauto.
      eexists; split; eauto.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq.
      apply b.
      intros; repeat solve_bounds.
        instantiate (1:= Mem.upd x0 x6 {| owner:= own; blocks := []|}).
        unfold file_map_rep in *; cleanup; split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x6); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        {
          intros.
          destruct (addr_dec inum x6); subst.
          {
          rewrite Mem.upd_eq in H1, H3; eauto.
          cleanup.
          unfold file_rep; simpl; intuition eauto.
          assert (i1 < @length addr []). {
          eapply nth_error_Some; eauto.
          congruence.
          }
          simpl in *; lia.
          }
          {
            rewrite Mem.upd_ne in H1, H3; eauto.
          }
        }
      }
      {
        unfold same_for_user_except in *; cleanup.
        assert (x6 = x7). {
          eapply FileInnerSpecs.inode_missing_then_file_missing in H21; eauto.
          eapply FileInnerSpecs.inode_missing_then_file_missing in H11; eauto.
          destruct (Compare_dec.lt_dec x6 x7).
          {
            exfalso; eapply H23; eauto.
            edestruct a.
            destruct_fresh (x3 x6); eauto.
            eapply FileInnerSpecs.inode_exists_then_file_exists in D; eauto; cleanup.
            exfalso; eapply H1; eauto.
            congruence.
          }
          {
            apply PeanoNat.Nat.nlt_ge in n.
            inversion n; eauto.
            exfalso; eapply H19 with (i:=x7).
            lia.
            edestruct a.
            destruct_fresh (x2 x7); eauto.
            eapply FileInnerSpecs.inode_exists_then_file_exists in D; eauto; cleanup.
            exfalso; eapply H6; eauto.
            congruence.
          }
        }
        subst.
        split.
        {
          unfold addrs_match_exactly in *; intros.
          destruct (addr_dec a1 x7); subst.
          repeat rewrite Mem.upd_eq; eauto.
          intuition congruence.
          repeat rewrite Mem.upd_ne; eauto.
        }
        split; intros.
        {
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H3, H4; eauto.
          cleanup.
          simpl; intuition eauto.
          }
          {
            rewrite Mem.upd_ne in H3, H4; eauto.
          }
        }
        {
          destruct (addr_dec inum x7); subst.
          {
          rewrite Mem.upd_eq in H3, H1; eauto.
          cleanup.
          simpl; intuition eauto.
          }
          {
            rewrite Mem.upd_ne in H3, H1; eauto.
          }
        }
      }
    }
  }
}
{
    repeat invert_step_crash.
    {
    destruct s2, s2.
    match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (snd s, snd s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       econstructor.
       eapply lift2_exec_step; eauto.
       simpl; repeat exec_step.
       simpl in *; eauto.
    }
    {
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
      unfold files_inner_rep; eexists; split; eauto.
      repeat cleanup_pairs.
      unfold files_inner_rep; eexists; split; eauto.
    }
  }
  {
    destruct s2, s2.
    match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (snd s, snd s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       econstructor.
       eapply lift2_exec_step; eauto.
       simpl; repeat exec_step.
       rewrite cons_app;
       eapply ExecBindCrash;
       repeat constructor.
       simpl in *; eauto.
    }
    {
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
      unfold files_inner_rep; eexists; split; eauto.
      repeat cleanup_pairs.
      unfold files_inner_rep; eexists; split; eauto.
    }
  }
}
    }
    {
      eapply lift2_invert_exec_crashed in H9; cleanup.
      unfold refines, files_rep in *; cleanup.
     eapply_fresh SSE_alloc_inode in H6; eauto.
     2: setoid_rewrite H2; eauto.
     2: setoid_rewrite H1; eauto.
     cleanup.
     destruct x3; simpl in *; try solve [intuition congruence].
     eapply_fresh Inode.alloc_crashed in H6; eauto.
     eapply_fresh Inode.alloc_crashed in H8; eauto.
     destruct s2, s2.
     match goal with
        [H1: same_for_user_except _ _ ?x ?x0,
        A : recovery_exec' _ _ _ _ _ _ _ |- _] =>  
          eapply SelfSimulation_Exists_recover in A;
          try instantiate (1:= (s0, (snd s, snd s))) in A;
          unfold AD_valid_state, refines_valid, FD_valid_state; 
          intros; eauto
     end.
     edestruct H15.
     2: { 
       eexists; econstructor_recovery; [|eauto]; eauto.
       repeat rewrite <- app_assoc.
       eapply ExecBindCrash.
       eapply lift2_exec_step_crashed; eauto.
       simpl in *; eauto.
    }
    {
      repeat cleanup_pairs.
      simpl in *.
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
    }
  }
  }
Unshelve.
all: eauto.
all: exact AuthenticatedDisk.
Qed.