Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia Language SameRetType SSECommon InodeSSE.


Lemma SSE_change_owner_inner:
forall o fm1 fm2 s1 s2 inum v v' ret1 u u',
same_for_user_except u' (Some inum) fm1 fm2 ->
files_inner_rep fm1 (fst s1) ->
files_inner_rep fm2 (fst s2) ->
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s1 (change_owner_inner v inum) ret1 ->
exists ret2, 
exec (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) u o s2 (change_owner_inner v' inum) ret2 /\
(extract_ret ret1 = None <-> extract_ret ret2 = None).
Proof.
Transparent change_owner_inner.  
unfold change_owner_inner; intros.
invert_step.
eapply_fresh SSE_change_owner in H2; eauto.
Qed.
Opaque change_owner_inner.


Theorem SelfSimulation_Exists_change_owner:
  forall u m inum v1,
    SelfSimulation_Exists
      u (change_owner inum v1) (change_owner inum v1) recover
      AD_valid_state (AD_related_states u (Some inum))
      (authenticated_disk_reboot_list m).
Proof.
  Opaque change_owner_inner.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_valid, refines_related,
  authenticated_disk_reboot_list, 
  change_owner;
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
     eapply_fresh SSE_change_owner_inner in H7.
     3: eauto.
     3: eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.change_owner_inner_finished_oracle_eq in H7; eauto.
      cleanup.
      eexists.
      intuition eauto; cleanup; eauto.
     }
     {
      eexists.
      intuition eauto; cleanup; eauto.
     }
     eauto.
   }
  }
  {
    invert_exec.
    eapply_fresh SSE_auth_then_exec in H14; eauto.
   {
     cleanup.
     destruct x1; simpl in *; try solve [intuition congruence].
     eapply_fresh FileSpecs.change_owner_crashed in H14; eauto.
    eapply_fresh FileSpecs.change_owner_crashed in H1; eauto.
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
     destruct (user_dec v1 (owner x1)); subst.
     {
       rewrite Mem.upd_nop in H10.
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
     unfold change_file_owner; cleanup; 
     destruct x1; simpl; eauto.
     }
     {
      exfalso; eapply change_owner_crashed_exfalso; eauto.
     }   
   }
   {
    destruct (user_dec v1 (owner x1)); subst.
    {
      rewrite Mem.upd_nop in H10.
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
    unfold change_file_owner; cleanup; 
    destruct x1; simpl; eauto.
    }
     {
      exfalso; eapply change_owner_crashed_exfalso.
      eapply same_for_user_except_symmetry. eauto.
      all: eauto.
     }
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
         destruct (addr_dec a inum);
         [repeat rewrite Mem.upd_eq; eauto; intuition congruence
         |repeat rewrite Mem.upd_ne; eauto; intuition congruence].
         split; intros.
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H5, H19; eauto; cleanup
         |rewrite Mem.upd_ne in H5, H19; eauto; cleanup].
         intuition.
         }
         {
          destruct (addr_dec inum0 inum);
          [rewrite Mem.upd_eq in H3, H5; eauto; cleanup
         |rewrite Mem.upd_ne in H3, H5; eauto; cleanup].
         unfold extend_file in *; simpl in *.
         eapply H18 in H7; eauto.
         cleanup; intuition eauto.
         }
       }
     }
   }
  }
  {
     intros.
     eapply_fresh SSE_change_owner_inner in H7; eauto.
     cleanup.
     destruct ret1, x1; simpl in * ; try solve [intuition congruence].
     {
      eapply SameRetType.change_owner_inner_finished_oracle_eq in H7; eauto.
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
