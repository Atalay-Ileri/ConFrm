Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType SSECommon InodeSSE.


Opaque Inode.get_inode DiskAllocator.alloc Inode.extend.
Lemma SSE_extend_inner:
forall o fm1 fm2 s1 s2 inum v v' ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (extend_inner v inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (extend_inner v' inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent extend_inner.  
unfold extend_inner; intros.
invert_step.
{
  eapply_fresh SSE_alloc in H2; eauto.
  cleanup.
  destruct x2; simpl in *; try solve [intuition congruence]. 
  
  eapply_fresh DiskAllocator.alloc_finished_oracle_eq in H2; eauto.
  cleanup; destruct o; try solve [intuition congruence].
  unfold refines, files_rep, files_inner_rep in *; cleanup.
  eapply DiskAllocator.alloc_finished in H2; eauto.
  cleanup; split_ors; cleanup.
  eapply_fresh DiskAllocator.alloc_finished in H4; eauto.
  cleanup; split_ors; cleanup.
  
  eapply_fresh SSE_extend in H3; eauto.
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
  eapply_fresh SSE_alloc in H2; eauto.
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
    eapply_fresh SSE_alloc in H2; eauto.
    cleanup.
    destruct x; simpl in *; try solve [intuition congruence]. 
  
    exists (Crashed s0); split.
    repeat exec_step.
    eapply ExecBindCrash; eauto.
    simpl; intuition eauto.
  }
  {
    eapply_fresh SSE_alloc in H3; eauto.
    logic_clean.
    destruct x3; simpl in *; try solve [intuition congruence]. 
    
    eapply_fresh DiskAllocator.alloc_finished_oracle_eq in H3; eauto.
    logic_clean.
    unfold refines, files_rep, files_inner_rep in *; logic_clean.
    eapply DiskAllocator.alloc_finished in H3; eauto.
    eapply_fresh DiskAllocator.alloc_finished in H2; eauto.
    cleanup; repeat split_ors; cleanup; try solve [intuition congruence].
    {
      eapply_fresh SSE_extend in H4; eauto.
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

Lemma SSE_auth_then_exec:
forall T (p1 p2: addr -> prog _ (option T)) inum,
(forall o fm1 fm2 s1 s2 ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (p1 inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (p2 inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None) /\
(forall s1 r1 s2 r2, ret1 = Finished s1 r1 -> ret2 = Finished s2 r2 -> (r1 = None <-> r2 = None))) -> 

forall o fm1 fm2 s1 s2 ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
refines s1 fm1 ->
refines s2 fm2 ->
exec (AuthenticatedDiskLayer.AuthenticatedDiskLang) u o s1 (auth_then_exec inum p1) ret1 ->
exists ret2, 
exec (AuthenticatedDiskLayer.AuthenticatedDiskLang) u o s2 (auth_then_exec inum p2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
  Opaque Inode.get_owner.
  unfold auth_then_exec; intros.
  destruct ret1.
  {
  repeat invert_exec.
  4: {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     3:{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H9; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H28 in H6; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H31 in H25; eauto; cleanup.
       eapply H32 in H22; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     simpl; intuition congruence.
   }
   2:{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].

     eapply H in H10; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     edestruct H14; eauto.
     destruct o; try solve [ intuition congruence]. 
     destruct s2.
     {
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     repeat econstructor.
     {
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H17; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H20; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh a0 in H1; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H24 in H20; eauto; cleanup.
       eapply H26 in H17; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite H1; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
    {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H11; eauto.
        2: rewrite H2; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
   }
   {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].

     eapply H in H10; eauto; cleanup.
     destruct x; simpl in *; try solve [ intuition congruence]. 
     edestruct H14; eauto.
     destruct o; try solve [ intuition congruence].
     destruct s2.
     {
     eexists; split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     repeat econstructor.
     {
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H18; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh a0 in H1; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H25 in H21; eauto; cleanup.
       eapply H27 in H18; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.
     simpl; intuition congruence.
     }
     {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite H1; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t5); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
    {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H11; eauto.
        2: rewrite H2; eauto.
      repeat cleanup_pairs; simpl in *.
      unfold refines, files_rep, files_inner_rep; eauto. 
      eexists; split; eauto.

      eexists; split.
      eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t4); eauto.
      intros; repeat solve_bounds.
      eauto.
    }
   }
  }
  {
  repeat invert_exec.
  split_ors; repeat invert_exec; cleanup.
  {
     eapply_fresh SSE_get_owner in H5; eauto; cleanup.
     destruct x0; simpl in *; try solve [ intuition congruence]. 
     destruct s2.
     exists (Crashed (s2, s0)); split.
     repeat rewrite <- app_assoc.
     eapply ExecBindCrash.
     eapply lift2_exec_step_crashed; eauto.
     simpl; intuition congruence.
  }
  {
    repeat invert_exec.
    eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x4; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
    repeat invert_step_crash.
    {
      destruct s2.
     exists (Crashed (s, s0)); split.
     econstructor.
     eapply lift2_exec_step; eauto.
     simpl; repeat exec_step.
     rewrite cons_app;
     eapply ExecBindCrash;
     repeat econstructor.
     simpl; intuition congruence.
    }
    {
      eapply H in H10; eauto; cleanup.
      destruct x1; simpl in *; try solve [ intuition congruence]. 
      
      destruct s2.
      {
      exists (Crashed (s2, s3)); split.
      repeat exec_step.
      repeat econstructor.
      eapply lift2_exec_step; eauto.
      repeat exec_step.

      simpl.
      rewrite cons_app;
      econstructor.
      repeat econstructor.
      {
        unfold refines, files_rep, files_inner_rep in *; 
        simpl in *; cleanup.
        eapply Inode.get_owner_finished in H6; eauto.
        2: rewrite e0; eauto.
        cleanup; split_ors; cleanup.
        eapply Inode.get_owner_finished in H7; eauto.
        2: rewrite e; eauto.
        cleanup; split_ors; cleanup.
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H13; eauto; cleanup.
        eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H16; eauto; cleanup.
        unfold same_for_user_except in *; cleanup.
        eapply_fresh a0 in H1; eauto; cleanup.
        unfold file_map_rep in *; cleanup.
        eapply H20 in H16; eauto; cleanup.
        eapply H22 in H13; eauto; cleanup.
        unfold file_rep in *; cleanup.
        congruence.
      }
      simpl; repeat exec_step.
      repeat rewrite <- app_assoc.
      eapply ExecBindCrash;
      repeat econstructor.
      eapply lift2_exec_step_crashed; eauto.
      simpl; intuition congruence.
      }
      {
          unfold refines, files_rep, files_inner_rep in *; 
          simpl in *; cleanup.
          eapply Inode.get_owner_finished in H6; eauto.
          2: rewrite H1; eauto.
        repeat cleanup_pairs; simpl in *.
        unfold refines, files_rep, files_inner_rep; eauto. 
        eexists; split; eauto.

        eexists; split.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
        intros; repeat solve_bounds.
        eauto.
      }
      {
          unfold refines, files_rep, files_inner_rep in *; 
          simpl in *; cleanup.
          eapply Inode.get_owner_finished in H7; eauto.
          2: rewrite H2; eauto.
        repeat cleanup_pairs; simpl in *.
        unfold refines, files_rep, files_inner_rep; eauto. 
        eexists; split; eauto.

        eexists; split.
        eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
        intros; repeat solve_bounds.
        eauto.
      }
    }
    {
     eapply H in H11; eauto; try logic_clean.
     destruct x2; simpl in *; try solve [ intuition congruence].
     {
       cleanup; repeat invert_step_crash.
       {
         edestruct H12; eauto.
         destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, s3)); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite e0; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite e; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H15; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H18; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh a0 in H1; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H22 in H18; eauto; cleanup.
            eapply H24 in H15; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          rewrite cons_app;
          eapply ExecBindCrash;
          repeat econstructor.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (fst s3, fst s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H26; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H29 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H32 in H26; eauto; cleanup.
            eapply H33 in H23; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          rewrite cons_app;
          eapply ExecBindCrash;
          simpl; repeat econstructor.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (fst s3, fst s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H23; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H26; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H29 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H32 in H26; eauto; cleanup.
            eapply H33 in H23; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, s3)); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H28 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H31 in H25; eauto; cleanup.
            eapply H32 in H22; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          rewrite cons_app;
          eapply ExecBindCrash;
          repeat econstructor; eauto.
          simpl; intuition congruence.
        }
       }
       {
        edestruct H12; eauto.
        destruct o; try solve [ intuition congruence]. 
        destruct s2.
        {
          exists (Crashed (s, (snd s3, snd s3))); split.
          repeat exec_step.
          repeat econstructor.
          eapply lift2_exec_step; eauto.
          repeat exec_step.
    
          simpl.
          rewrite cons_app;
          econstructor.
          repeat econstructor.
          {
            unfold refines, files_rep, files_inner_rep in *; 
            simpl in *; cleanup.
            eapply Inode.get_owner_finished in H6; eauto.
            2: rewrite H1; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H2; eauto.
            cleanup; split_ors; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H22; eauto; cleanup.
            eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H25; eauto; cleanup.
            unfold same_for_user_except in *; cleanup.
            eapply_fresh H28 in H6; eauto; cleanup.
            unfold file_map_rep in *; cleanup.
            eapply H31 in H25; eauto; cleanup.
            eapply H32 in H22; eauto; cleanup.
            unfold file_rep in *; cleanup.
            congruence.
          }
          simpl; repeat exec_step.
          econstructor.
          eapply lift2_exec_step; eauto.
          simpl; repeat exec_step.
          simpl; intuition congruence.
        }
       }
     }
     {
      unfold refines, files_rep, files_inner_rep in *; 
      simpl in *; logic_clean.
      eapply Inode.get_owner_finished in H6; eauto.
    repeat cleanup_pairs; simpl in *.
    unfold refines, files_rep, files_inner_rep; eauto. 
     eexists; split; eauto.

    eexists; split.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t2); eauto.
    intros; repeat solve_bounds.
    eauto.

  }
  {
      unfold refines, files_rep, files_inner_rep in *; 
      simpl in *; logic_clean.
      eapply Inode.get_owner_finished in H7; eauto.
    repeat cleanup_pairs; simpl in *.
    unfold refines, files_rep, files_inner_rep; eauto. 
    eexists; split; eauto.

    eexists; split.
    eapply DiskAllocator.block_allocator_rep_inbounds_eq with (s1:= t1); eauto.
    intros; repeat solve_bounds.
    eauto.
  }
}
{
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x0; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     exists (Crashed (s2, s)); split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H24; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H27 in H3; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H30 in H24; eauto; cleanup.
       eapply H31 in H21; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     rewrite cons_app;
     eapply ExecBindCrash;
     repeat econstructor.
     simpl; intuition congruence.
   }
   {
     eapply_fresh SSE_get_owner in H6; eauto; cleanup.
     destruct x0; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     exists (Crashed (s2, (snd s, snd s))); split.
     repeat exec_step.
     repeat econstructor.
     eapply lift2_exec_step; eauto.
     repeat exec_step.

     simpl.
     rewrite cons_app;
     econstructor.
     do 2 econstructor.
     {
       eapply AuthenticationLayer.ExecAuthFail.
       unfold refines, files_rep, files_inner_rep in *; 
       simpl in *; cleanup.
       eapply Inode.get_owner_finished in H6; eauto.
       2: rewrite H1; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H2; eauto.
       cleanup; split_ors; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H21; eauto; cleanup.
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H24; eauto; cleanup.
       unfold same_for_user_except in *; cleanup.
       eapply_fresh H27 in H3; eauto; cleanup.
       unfold file_map_rep in *; cleanup.
       eapply H30 in H24; eauto; cleanup.
       eapply H31 in H21; eauto; cleanup.
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     simpl; intuition congruence.
   }
   {
    destruct x4; simpl in *; try solve [ intuition congruence]. 
    eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
    destruct o; simpl in *; try solve [intuition congruence].
    repeat invert_step_crash.
    destruct s2.
    exists (Crashed (s, s0)); split.
    repeat exec_step.
    repeat econstructor.
    eapply lift2_exec_step; eauto.
    repeat exec_step.
    rewrite cons_app;
    eapply ExecBindCrash;
    repeat econstructor.
    simpl; intuition congruence.

    destruct s2.
    exists (Crashed (s, (snd s0, snd s0))); split.
    repeat exec_step.
    repeat econstructor.
    eapply lift2_exec_step; eauto.
    repeat exec_step.
    simpl; intuition congruence.
   }
  }
  }
Unshelve.
all: eauto.
all: exact AuthenticatedDisk.
Qed.

Theorem SelfSimulation_Exists_extend:
  forall u u' m inum v1 ex,
    SelfSimulation_Exists
      u (extend inum v1) (extend inum v1) recover
      AD_valid_state (AD_related_states u' ex)
      (authenticated_disk_reboot_list m).
Proof.
  Opaque extend_inner.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  extend;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**write finished **)
   invert_exec.
   eapply SSE_auth_then_exec in H11; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eexists; econstructor_recovery.
     eauto.
   }
   {
     intros.
     eapply_fresh SSE_extend_inner in H7; eauto.
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
    eapply_fresh SSE_auth_then_exec in H14; eauto.
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
          eapply SelfSimulation_Exists_recover in A;
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
          eapply SelfSimulation_Exists_recover in A;
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
          [rewrite Mem.upd_eq in H5, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H4; eauto; cleanup].
         unfold extend_file in *; simpl in *.
         eapply e in H17; eauto.
         subst; eauto.
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H3, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H3, H4; eauto; cleanup].
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
     eapply_fresh SSE_extend_inner in H7; eauto.
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


Theorem SelfSimulation_Exists_extend_input:
  forall u u' m inum v1 v2,
    SelfSimulation_Exists
      u (extend inum v1) (extend inum v2) recover
      AD_valid_state (AD_related_states u' (Some inum))
      (authenticated_disk_reboot_list m).
Proof.
  Opaque extend_inner.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  extend;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {(**write finished **)
   invert_exec.
   eapply SSE_auth_then_exec in H11; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eexists; econstructor_recovery.
     eauto.
   }
   {
     intros.
     eapply_fresh SSE_extend_inner in H7; eauto.
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
    eapply_fresh SSE_auth_then_exec in H14; eauto.
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
          eapply SelfSimulation_Exists_recover in A;
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
          eapply SelfSimulation_Exists_recover in A;
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
          [rewrite Mem.upd_eq in H5, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H4; eauto; cleanup].
         intuition.
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H3, H4; eauto; cleanup
         |rewrite Mem.upd_ne in H3, H4; eauto; cleanup].
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
     eapply_fresh SSE_extend_inner in H7; eauto.
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