Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language TSCommon InodeTS.


Lemma TS_auth_then_exec:
forall T (p1 p2: addr -> prog _ (option T)) inum,
(forall o fm1 fm2 s1 s2 ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
files_inner_rep fm1 (fst (snd s1)) ->
files_inner_rep fm2 (fst (snd s2)) ->
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s1 (p1 inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TDLang FSParameters.data_length) u o s2 (p2 inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None) /\
(forall s1 r1 s2 r2, ret1 = Finished s1 r1 -> ret2 = Finished s2 r2 -> (r1 = None <-> r2 = None))) -> 

forall o fm1 fm2 s1 s2 ret1 u u' ex,
same_for_user_except u' ex fm1 fm2 ->
refines s1 fm1 ->
refines s2 fm2 ->
exec (AuthenticatedDiskLayer.ADLang) u o s1 (auth_then_exec inum p1) ret1 ->
exists ret2, 
exec (AuthenticatedDiskLayer.ADLang) u o s2 (auth_then_exec inum p2) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
  Opaque Inode.get_owner.
  unfold auth_then_exec; intros.
  destruct ret1.
  {
  repeat invert_exec.
  4: {
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
       2: rewrite H18; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H9; eauto.
       2: rewrite H14; eauto.
       cleanup; split_ors; cleanup.
       match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
       unfold file_rep in *; cleanup.
       congruence.
     }
     simpl; repeat exec_step.
     simpl; intuition congruence.
   }
   2:{
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
       2: rewrite e2; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
        2: rewrite H18; eauto.
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
        2: rewrite H13; eauto.
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
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
       2: rewrite e2; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H11; eauto.
       2: rewrite e0; eauto.
       cleanup; split_ors; cleanup.
       match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
        2: rewrite H18; eauto.
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
        2: rewrite H13; eauto.
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
     eapply_fresh TS_get_owner in H5; eauto; cleanup.
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
    eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
        2: rewrite e2; eauto.
        cleanup; split_ors; cleanup.
        eapply Inode.get_owner_finished in H7; eauto.
        2: rewrite e0; eauto.
        cleanup; split_ors; cleanup.
        match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
          2: rewrite H14; eauto.
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
          2: rewrite H3; eauto.
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
            2: rewrite e2; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite e0; eauto.
            cleanup; split_ors; cleanup.
            match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
          eexists (Crashed (s, (_, (fst (snd s3), fst (snd s3))))); split.
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
            2: rewrite H18; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H14; eauto.
            cleanup; split_ors; cleanup.
            match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
          eexists (Crashed (s, (_, (fst (snd s3), fst (snd s3))))); split.
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
            2: rewrite H18; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H14; eauto.
            cleanup; split_ors; cleanup.
            match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
            2: rewrite H18; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H14; eauto.
            cleanup; split_ors; cleanup.
            match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
          eexists (Crashed (s, (_, (snd (snd s3), snd (snd s3))))); split.
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
            2: rewrite H18; eauto.
            cleanup; split_ors; cleanup.
            eapply Inode.get_owner_finished in H7; eauto.
            2: rewrite H14; eauto.
            cleanup; split_ors; cleanup.
            match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
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
       2: rewrite H17; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H12; eauto.
       cleanup; split_ors; cleanup.
       match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
     eapply_fresh TS_get_owner in H6; eauto; cleanup.
     destruct x0; simpl in *; try solve [ intuition congruence]. 
     eapply_fresh Inode.get_owner_finished_oracle_eq in H6; eauto.
     destruct o; simpl in *; try solve [intuition congruence].
     destruct s2.
     eexists (Crashed (s2, (_, (snd (snd s), snd (snd s))))); split.
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
       2: rewrite H17; eauto.
       cleanup; split_ors; cleanup.
       eapply Inode.get_owner_finished in H3; eauto.
       2: rewrite H12; eauto.
       cleanup; split_ors; cleanup.
       match goal with
       | [H: _ ?inum = Some _,
          H0: _ ?inum = Some _ |- _] =>
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H; eauto; cleanup;
       eapply_fresh FileInnerSpecs.inode_exists_then_file_exists in H0; eauto; cleanup
       end.
       unfold same_for_user_except in *; cleanup.
       match goal with
       | [H: ?fm1 ?inum = Some _,
          H0: ?fm2 ?inum = Some _,
          H1: forall (_: addr) (_ _: File), 
           ?fm1 _ = Some _ ->
           ?fm2 _ = Some _ ->
           _ = _ /\ _ = _ |- _] =>
           eapply_fresh H1 in H; eauto; cleanup
      end.
       unfold file_map_rep in *; cleanup.
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
    eexists (Crashed (s, (_, (snd (snd s0), snd (snd s0))))); split.
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
all: exact AD.
Qed.