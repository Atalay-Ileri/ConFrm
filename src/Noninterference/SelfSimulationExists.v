Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia.

Definition AD_valid_state := refines_to_valid FileDiskRefinement FD_valid_state.
Definition AD_related_states u exc := refines_to_related FileDiskRefinement (FD_related_states u exc).

Ltac econstructor_recovery :=
  match goal with
  | [|- recovery_exec _ ?u [?o] _ [] _ _ _ ]=>
    eapply (@ExecFinished _ _ _ _ u o)
  | [|- recovery_exec _ ?u (?o :: _) _ (?rf :: _) _ _ _ ]=>
    eapply (@ExecRecovered _ _ _ _ u o _ _ _ rf)
  end.

Theorem SelfSimulation_Exists_recover:
  forall u n,
      SelfSimulation_Exists u recover recover recover
                            AD_valid_state (AD_related_states u None)
                            (authenticated_disk_reboot_list n).
Proof.
  induction n; simpl;
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_to_valid, refines_to_related,
  authenticated_disk_reboot_list in *;
  intros; cleanup; simpl in *.
  {
    invert_exec; cleanup.
    unfold recover in *; repeat invert_exec; simpl in *.
    invert_exec'' H11; simpl in *.
    repeat invert_exec.
    eexists.    
    econstructor_recovery.
    repeat econstructor.
  }
  {
    invert_exec; cleanup.
    unfold recover in *; repeat invert_exec; simpl in *.
    invert_exec'' H14; simpl in *.
    repeat invert_exec.
    repeat cleanup_pairs.    
    destruct s2, s1; simpl in *.
    edestruct IHn.
    3: apply H15.
    intros; eauto.
    intros; eauto.    
    instantiate (1:= (s0, (t2, t2))).
    unfold refines_to, files_rep in *; simpl in *.
    cleanup; do 2 eexists; intuition eauto.
    eexists.
    econstructor_recovery.
    repeat econstructor; eauto.
    simpl; eauto.
  }
Qed.

Theorem SelfSimulation_Exists_auth_then_exec:
  forall u m inum T (p1 p2: Inode.Inum -> prog (TransactionalDiskLayer.TransactionalDiskLang FSParameters.data_length) (option T)) ex,
    (forall n, SelfSimulation_Exists u (lift_L2 _ (p1 inum)) (lift_L2 _ (p2 inum)) recover
        AD_valid_state (AD_related_states u ex)
        (authenticated_disk_reboot_list n)) ->
    
    SelfSimulation_Exists
      u (auth_then_exec inum p1) (auth_then_exec inum p2) recover
      AD_valid_state (AD_related_states u ex)
      (authenticated_disk_reboot_list m).
Proof.
  unfold SelfSimulation_Exists, AD_valid_state,
  AD_related_states, FD_valid_state, FD_related_states,
  refines_to_valid, refines_to_related,
  authenticated_disk_reboot_list;
  intros; cleanup; simpl in *.
  destruct m; simpl in *.
  {
    unfold auth_then_exec in *; repeat invert_exec; cleanup.
    invert_exec'' H12; simpl in *; cleanup; repeat invert_exec.
    {
      invert_exec'' H11; simpl in *; cleanup; repeat invert_exec.
      {
        invert_exec'' H16; simpl in *; cleanup; repeat invert_exec.
        invert_exec'' H12; simpl in *; cleanup; repeat invert_exec.
        {
          invert_exec'' H16; simpl in *; cleanup; repeat invert_exec.
          unfold Inode.InodeAllocator.read in *; cleanup; repeat invert_exec.
          {
            invert_exec'' H11; simpl in *; cleanup; repeat invert_exec.
            { 
              invert_exec'' H12; simpl in *; cleanup; repeat invert_exec.
              {
                invert_exec'' H16; simpl in *; cleanup; repeat invert_exec.
                invert_exec'' H17; simpl in *; cleanup; repeat invert_exec.
                invert_exec'' H12; simpl in *; cleanup; repeat invert_exec.
                {
                  cleanup.
                  invert_exec'' H15; simpl in *; cleanup; repeat invert_exec.
                  {
                    invert_exec'' H12; simpl in *; cleanup; repeat invert_exec.
                    {
                      invert_exec'' H17; simpl in *; cleanup; repeat invert_exec.
                      {
                        invert_exec'' H16; simpl in *; cleanup; repeat invert_exec.
                        invert_exec'' H18; simpl in *; cleanup; repeat invert_exec.
                        invert_exec'' H14; simpl in *; cleanup; repeat invert_exec.
                        edestruct (H 0); simpl in *.
                        3: {
                          eapply (@ExecFinished _ _ _ _
                                 (Inode.owner (Inode.decode_inode (fst (snd s1)
                                 (Inode.InodeAllocatorParams.bitmap_addr + S inum)))) o1 _ _); eauto.
                        }
                        all: intros; eauto.
                        eexists; simpl.
                        econstructor_recovery.
                        simpl.
                        replace (OpToken
       (HorizontalComposition AuthenticationLayer.AuthenticationOperation
          (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
       (Token2 AuthenticationLayer.AuthenticationOperation
          (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
          TransactionalDiskLayer.Cont)
     :: OpToken
          (HorizontalComposition AuthenticationLayer.AuthenticationOperation
             (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
          (Token2 AuthenticationLayer.AuthenticationOperation
             (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
             TransactionalDiskLayer.Cont)
        :: Language.Cont
             (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
           :: Language.Cont
                (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                   (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
              :: Language.Cont
                   (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                      (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
                 :: OpToken
                      (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
                      (Token1 AuthenticationLayer.AuthenticationOperation
                         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
                         AuthenticationLayer.Cont)
                    :: o1 ++
                       [OpToken
                          (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                             (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
                          (Token2 AuthenticationLayer.AuthenticationOperation
                             (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
                             TransactionalDiskLayer.Cont);
                       Language.Cont
                         (HorizontalComposition AuthenticationLayer.AuthenticationOperation
                                                (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))])
                          with
   (((([OpToken (HorizontalComposition AuthenticationLayer.AuthenticationOperation
          (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
       (Token2 AuthenticationLayer.AuthenticationOperation
          (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
          TransactionalDiskLayer.Cont)] ++
    ([OpToken
      (HorizontalComposition AuthenticationLayer.AuthenticationOperation
         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
      (Token2 AuthenticationLayer.AuthenticationOperation
         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
         TransactionalDiskLayer.Cont)] ++
    [Language.Cont
      (HorizontalComposition AuthenticationLayer.AuthenticationOperation
         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))])) ++
    [Language.Cont
      (HorizontalComposition AuthenticationLayer.AuthenticationOperation
         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))]) ++
    [Language.Cont
      (HorizontalComposition AuthenticationLayer.AuthenticationOperation
         (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))]) ++
    (OpToken (HorizontalComposition AuthenticationLayer.AuthenticationOperation
            (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
            (Token1 AuthenticationLayer.AuthenticationOperation
             (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
              AuthenticationLayer.Cont) :: o1 ++
    [OpToken
       (HorizontalComposition AuthenticationLayer.AuthenticationOperation
        (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))
       (Token2 AuthenticationLayer.AuthenticationOperation
        (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length)
        TransactionalDiskLayer.Cont);
     Language.Cont
       (HorizontalComposition AuthenticationLayer.AuthenticationOperation
       (TransactionalDiskLayer.TransactionalDiskOperation FSParameters.data_length))])).

   repeat eapply ExecBind.
   repeat econstructor; eauto.
   {
     clear H H0 H1.
     unfold refines_to, files_rep,
     files_inner_rep, file_map_rep,
     Inode.inode_rep,
     Inode.InodeAllocator.block_allocator_rep,
     Inode.inode_map_rep in *;
     cleanup.
     eapply Inode.InodeAllocator.valid_bits_extract with (n := inum) in v0; eauto;
     try lia.          
     cleanup.
     eapply nth_error_nth with (d:= false) in D0; eauto.
     rewrite <- nth_seln_eq in D0.
     setoid_rewrite equal_f with (x5 :=  Inode.InodeAllocatorParams.bitmap_addr) in D0; eauto.
     split_ors; cleanup; try congruence.
     setoid_rewrite H0 in D0; congruence.
     
