Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType.
Require Import TSCommon InodeTS TSAuthThenExec.


Opaque Inode.get_inode DiskAllocator.alloc Inode.extend.
Lemma TS_extend_inner:
forall o fm1 fm2 s1 s2 inum v v' ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst (snd s1)) ->
files_inner_rep fm2 (fst (snd s2)) ->
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s1 (extend_inner v inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s2 (extend_inner v' inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent extend_inner.  
unfold extend_inner; intros.
invert_step.
{
  eapply_fresh TS_alloc in H2; eauto.
  cleanup.
  destruct x2; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh DiskAllocator.alloc_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  unfold refines, files_rep, files_inner_rep in *; cleanup.
  eapply DiskAllocator.alloc_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh DiskAllocator.alloc_finished in H4; eauto.
  cleanup; split_ors; cleanup.
  
  eapply_fresh TS_extend in H3; eauto.
  cleanup.
  destruct x8; simpl in *; try solve [intuition congruence].
  eapply Inode.extend_finished_oracle_eq in H3; eauto; cleanup.

  eexists; split.
  econstructor.
  simpl; eapply H4.
  simpl; eauto.
  simpl; intuition congruence.   

  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.

    unfold Inode.inode_rep in *; cleanup.
    eexists; split.
    eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq with (s1:= t3); eauto.
    intros; repeat solve_bounds.
    eauto.
    eexists; intuition eauto.
    {
      unfold file_map_rep in *; cleanup.
      intuition eauto.
      eapply H19 in H20; eauto.
      unfold file_rep in *; cleanup.
      intuition eauto.
      eapply H23 in H24; cleanup.
      eexists; intuition eauto.
      rewrite Mem.upd_ne; eauto.
      intros Hnot; subst; congruence.
    }
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.

    unfold Inode.inode_rep in *; cleanup.
    eexists; split.
    eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; repeat solve_bounds.
    eauto.
    eexists; intuition eauto.
    {
      unfold file_map_rep in *; cleanup.
      intuition eauto.
      eapply H17 in H20; eauto.
      unfold file_rep in *; cleanup.
      intuition eauto.
      eapply H23 in H24; cleanup.
      eexists; intuition eauto.
      rewrite Mem.upd_ne; eauto.
      intros Hnot; subst; congruence.
    }
  }
}
{
  eapply_fresh TS_alloc in H2; eauto.
  cleanup.
  destruct x0; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh DiskAllocator.alloc_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].

  eexists; split.
  econstructor.
  simpl; eapply H3.
  simpl; eauto.
  repeat econstructor.
  simpl; intuition congruence.   
}
{
  repeat invert_step_crash.
  {
    eapply_fresh TS_alloc in H2; eauto.
    cleanup.
    destruct x; simpl in *; try solve [intuition congruence]. 
  
    exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash; eauto.
    simpl; intuition eauto.
  }
  {
    eapply_fresh TS_alloc in H3; eauto.
    logic_clean.
    destruct x3; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh DiskAllocator.alloc_finished_oracle_eq in H3; eauto.
    logic_clean.
    unfold refines, files_rep, files_inner_rep in *; logic_clean.
    eapply DiskAllocator.alloc_finished in H3; eauto.
    eapply_fresh DiskAllocator.alloc_finished in H2; eauto.
    cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
    {
      eapply_fresh TS_extend in H4; eauto.
      cleanup.
      destruct x8; simpl in *; try solve [intuition congruence].
      exists (Crashed s3); split.
      econstructor; simpl; eauto.
      simpl; eauto.
      simpl; intuition eauto.
      {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.

    unfold Inode.inode_rep in *; cleanup.
    eexists; split.
    eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq with (s1:= t3); eauto.
    intros; repeat solve_bounds.
    eauto.
    eexists; intuition eauto.
    {
      unfold file_map_rep in *; cleanup.
      intuition eauto.
      eapply H19 in H20; eauto.
      unfold file_rep in *; cleanup.
      intuition eauto.
      eapply H23 in H24; cleanup.
      eexists; intuition eauto.
      rewrite Mem.upd_ne; eauto.
      intros Hnot; subst; congruence.
    }
  }
  {
    repeat cleanup_pairs; simpl in *.
    unfold files_inner_rep; eexists; intuition eauto.

    unfold Inode.inode_rep in *; cleanup.
    eexists; split.
    eapply Inode.InodeAllocator.block_allocator_rep_inbounds_eq; eauto.
    intros; repeat solve_bounds.
    eauto.
    eexists; intuition eauto.
    {
      unfold file_map_rep in *; cleanup.
      intuition eauto.
      eapply H10 in H20; eauto.
      unfold file_rep in *; cleanup.
      intuition eauto.
      eapply H23 in H24; cleanup.
      eexists; intuition eauto.
      rewrite Mem.upd_ne; eauto.
      intros Hnot; subst; congruence.
    }
  }
  }
  {
      invert_step; eexists; split.
      repeat exec_step.
      simpl; intuition congruence.
  } 
}
}
Unshelve.
all: eauto.
Qed.
Opaque extend_inner.


Theorem Termination_Sensitive_extend:
  forall u u' m inum v1 ex,
    Termination_Sensitive
      u (extend inum v1) (extend inum v1) recover
      AD_valid_state (AD_related_states u' ex)
      (authenticated_disk_reboot_list m).
Proof.
  Opaque extend_inner.
  unfold Termination_Sensitive, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  extend;
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
     eapply_fresh TS_extend_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.extend_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
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
     eapply_fresh FileSpecs.extend_crashed in H14; eauto.
    eapply_fresh FileSpecs.extend_crashed in H1; eauto.
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
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
     }
   }
   {
     exfalso; eapply extend_crashed_exfalso; eauto.
   }
   {
     exfalso; eapply extend_crashed_exfalso.
     eapply same_for_user_except_symmetry. eauto.
     all: eauto.
   }
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
       instantiate (1:= ex).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
       {
         unfold same_for_user_except in *; cleanup.
         split; intros. 
         unfold addrs_match_exactly in *; intros.
         destruct (addr_dec a1 inum);
         [repeat rewrite Mem.upd_eq; eauto; intuition congruence
         |repeat rewrite Mem.upd_ne; eauto; intuition congruence].
         split; intros.
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H5, H16; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H16; eauto; cleanup].
         unfold extend_file in *; simpl in *.
         eapply e in H19; eauto.
         subst; eauto.
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H5, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H4; eauto; cleanup].
         unfold extend_file in *; simpl in *.
         eapply a0 in H7; eauto.
         cleanup; intuition eauto.
         repeat rewrite app_length; lia.
         }
       }
     }
   }
  }
  {
     intros.
     eapply_fresh TS_extend_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.extend_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
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


Theorem Termination_Sensitive_extend_input:
  forall u u' m inum v1 v2,
    Termination_Sensitive
      u (extend inum v1) (extend inum v2) recover
      AD_valid_state (AD_related_states u' (Some inum))
      (authenticated_disk_reboot_list m).
Proof.
  Opaque extend_inner.
  unfold Termination_Sensitive, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  extend;
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
     eapply_fresh TS_extend_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.extend_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
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
     eapply_fresh FileSpecs.extend_crashed in H14; eauto.
    eapply_fresh FileSpecs.extend_crashed in H1; eauto.
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
       instantiate (1:= Some inum).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
     }
   }
   {
     exfalso; eapply extend_crashed_exfalso; eauto.
   }
   {
     exfalso; eapply extend_crashed_exfalso.
     eapply same_for_user_except_symmetry. eauto.
     all: eauto.
   }
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
       instantiate (1:= Some inum).
       unfold AD_related_states, refines_related,
       FD_related_states in *; simpl;
       unfold refines, files_rep, files_crash_rep in *; simpl.
       do 2 eexists; intuition eauto.
       {
         unfold same_for_user_except in *; cleanup.
         split; intros. 
         unfold addrs_match_exactly in *; intros.
         destruct (addr_dec a1 inum);
         [repeat rewrite Mem.upd_eq; eauto; intuition congruence
         |repeat rewrite Mem.upd_ne; eauto; intuition congruence].
         split; intros.
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H5, H16; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H16; eauto; cleanup].
         intuition.
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H5, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H4; eauto; cleanup].
         unfold extend_file in *; simpl in *.
         eapply a0 in H7; eauto.
         cleanup; intuition eauto.
         repeat rewrite app_length; simpl; lia.
         }
       }
     }
   }
  }
  {
     intros.
     eapply_fresh TS_extend_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.extend_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
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