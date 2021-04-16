Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia.
Require Import AuthenticationLayer TransactionalDiskLayer AuthenticatedDiskLayer.

Lemma exec_Crash_finished_exfalso:
forall O (L: Language O) u T (p: L.(prog) T) s s' r,
~exec L u [Language.Crash O] s p (Finished s' r).
Proof.
    unfold not; induction p; simpl; intros;
    invert_exec.
    symmetry in H2; apply app_eq_unit in H2;
    intuition cleanup;
    exfalso; eapply exec_empty_oracle; eauto.
Qed.

Lemma exec_finished_no_crash_tokens:
forall u T (p: Definitions.impl.(prog) T) o s s' r,
exec Definitions.impl u o s p (Finished s' r) -> 
(forall (t: Definitions.impl.(token)), In t o -> 
t <> Language.Crash _ /\ 
t <> OpToken AuthenticatedDiskOperation (Token1 AuthenticationOperation _ Crash) /\
t <> OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashBefore) /\
t <> OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashAfter) /\
t <> OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashDuringCommit)).
Proof.
    induction p; simpl; intros;
    invert_exec.
    {
        destruct o; invert_exec;
        destruct o; invert_exec;
        (inversion H0; cleanup;
        [ repeat (split; try congruence)
        | inversion H]).
    }
    {
        inversion H0; cleanup;
        [ repeat (split; try congruence)
        | inversion H].
    }
    {
        eapply in_app_iff in H1; split_ors; eauto.
    }
Qed.   

Lemma exec_crashed_exists_crash_token:
forall u T (p: Definitions.impl.(prog) T) o s s',
exec Definitions.impl u o s p (Crashed s') -> 
(exists (t: Definitions.impl.(token)), 
In t o /\
( 
t = Language.Crash _ \/
t = OpToken AuthenticatedDiskOperation (Token1 AuthenticationOperation _ Crash) \/
t = OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashBefore) \/
t = OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashAfter) \/
t = OpToken AuthenticatedDiskOperation (Token2 _ (TransactionalDiskOperation FSParameters.data_length) CrashDuringCommit))
).
Proof.
    induction p; simpl; intros;
    invert_exec.
    {
        destruct o; invert_exec;
        destruct o; invert_exec.
        all: eexists; split; [econstructor; eauto | eauto].
    }
    {
        eexists; split; [econstructor; eauto | eauto].
    }
    {
        split_ors; cleanup.
        edestruct IHp; eauto.
        cleanup.
        eexists; split.
        apply in_app_iff; eauto.
        eauto.

        edestruct H; eauto.
        cleanup.
        eexists; split.
        apply in_app_iff; eauto.
        eauto.
    }
Qed.   

Lemma exec_finished_not_crashed:
forall u T (p: Definitions.impl.(prog) T) o s s' s1 s1' r,
exec Definitions.impl u o s p (Finished s' r) -> 
~exec Definitions.impl u o s1 p (Crashed s1').
Proof.
  unfold not; intros.
  eapply exec_crashed_exists_crash_token in H0; cleanup.
  eapply exec_finished_no_crash_tokens in H; eauto.
  cleanup; intuition; subst; congruence.
Qed.

Lemma token_refines_same_read:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum off,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' None x x0 ->
    oracle_refines _ _ _ Definitions.abs FileDiskOperationRefinement _ u s1_imp 
    (|Read inum off|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ Definitions.abs FileDiskOperationRefinement _ u s2_imp 
    (|Read inum off|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    specialize H5 with (1:= H);
    specialize H4 with (1:= H0);
    repeat split_ors; cleanup; 
    repeat unify_execs; eauto.
    eapply SSERead 
    unfold read in H3.
    Search Finished Crashed.
    edestruct read_simulation; simpl. 
    2: apply H.
    2: instantiate (4:=0).



(*
Lemma oracle_refines_same:
forall u u' T (p1 p2: Definitions.abs.(prog) T) s1_imp s2_imp x x0 o_imp o_abs o_abs' get_reboot_state,
    (forall t t' T (p1 p2: Definitions.abs_core.(operation) T),
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' None x x0 ->
    token_refines _ u s1_imp  
    p1 get_reboot_state  o_imp t ->
    token_refines _ u s2_imp   
    p2 get_reboot_state o_imp t' ->
    t = t') ->
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' None x x0 ->
    oracle_refines _ _ _ Definitions.abs FileDiskOperationRefinement _ u s1_imp 
    p1 get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ Definitions.abs FileDiskOperationRefinement _ u s2_imp 
    p2 get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
    Proof.
    induction p1; simpl; intros; eauto.
    {
        cleanup.
        destruct p2; simpl in *; cleanup.
        erewrite H with (t:= x1)(t':=x2); eauto.
        split_ors; cleanup.

        invert_exec; simpl in *.
        {
            unfold refines, files_rep, files_reboot_rep in *.
            destruct o. 
            {
                simpl in *; 
                unfold refines, files_rep, files_reboot_rep in *;
                cleanup;
                edestruct H5; cleanup; eauto; try congruence.
                split; eauto.
                setoid_rewrite H0; eauto.
                exfalso; eapply exec_Crash_finished_exfalso in H6; eauto.
                
                unfold read, auth_then_exec in *; simpl in *.
                invert_exec.
                symmetry in H10; apply app_eq_unit in H10;
                intuition cleanup.
                exfalso; eapply exec_empty_oracle; eauto.
                Transparent Inode.get_owner.
                unfold Inode.get_owner in *.
                invert_exec.
                destruct x1; simpl in *; try congruence.
                destruct t; simpl in *; try congruence.
                invert_exec'' H11.
                destruct o1.
                exfalso; eapply exec_empty_oracle; eauto.
                rewrite <- app_comm_cons in H12.
                inversion H12; subst.
                unfold Inode.get_inode, Inode.InodeAllocator.read in *.
                invert_step.
        }
         eauto.
    }
    cleanup; simpl in *; try tauto; try lia.
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup; try tauto.
    eapply H in H10; eauto; subst; eauto.
Qed.
*)

Lemma recovery_oracles_refine_to_same:
         forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp x x0 u u' T (p1 p2: Definitions.abs.(prog) T),
         (forall o_imp o_abs o_abs' get_reboot_state,
         refines s1_imp x ->
            refines s2_imp x0 ->
        same_for_user_except u' None x x0 ->
        oracle_refines _ _ _ _ FileDiskOperationRefinement _ u s1_imp 
        p1 get_reboot_state  o_imp o_abs ->
        oracle_refines _ _ _ _ FileDiskOperationRefinement _ u s2_imp 
        p2 get_reboot_state  o_imp o_abs' ->
            o_abs = o_abs') ->
         
         refines s1_imp x ->
            refines s2_imp x0 ->
        same_for_user_except u' None x x0 ->
        recovery_oracles_refine_to FileDiskRefinement u s1_imp p1 
          (| Recover |) [] l_o_imp l_o_abs ->
        recovery_oracles_refine_to FileDiskRefinement u s2_imp p2
            (| Recover |) [] l_o_imp l_o_abs' ->
       l_o_abs = l_o_abs'.
       Proof.
           induction l_o_imp; simpl; intros; try tauto.
         cleanup; simpl in *; try tauto; try lia.
         repeat split_ors; cleanup;
         repeat unify_execs; cleanup; try tauto.
         eapply H in H10; eauto; subst; eauto.
       Qed.

       

Lemma ORS_recover:
forall u u' ex n,
oracle_refines_same_from_related FileDiskRefinement u 
(|Recover|)  (|Recover|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' ex).
Proof.
unfold oracle_refines_same_from_related,
refines_related.
    induction n;
    simpl; intros; cleanup.
    {
        destruct l_o_imp; simpl in *; cleanup; eauto; try tauto.
        repeat split_ors; cleanup; 
        try unify_execs; cleanup; try tauto.
        
        edestruct H13; edestruct H9.
        all: try solve [unfold refines,
        files_rep, files_reboot_rep in*;
        cleanup; simpl; eauto];
        cleanup; repeat unify_execs; cleanup.
    }
    {
    destruct l_o_imp; simpl in *; cleanup; eauto; try tauto.
    repeat split_ors; cleanup; 
    try unify_execs; cleanup; try tauto;
    simpl in *; try lia.
    
    edestruct H13; edestruct H9.
    all: try solve [unfold refines,
    files_rep, files_reboot_rep in*;
    cleanup; simpl; eauto];
    cleanup; repeat unify_execs; cleanup.

    edestruct H11; edestruct H8.
    all: try solve [unfold refines,
    files_rep, files_reboot_rep in*;
    cleanup; simpl; eauto];
    cleanup; repeat unify_execs; cleanup.

    erewrite IHn with (l_o_abs := l0) (l_o_abs' := l). 
    eauto.
    2: eauto.
    2: eauto.
    do 2 eexists. unfold refines, files_rep, files_crash_rep in *.
    repeat (split; eauto).
    }
Qed.

Lemma ORS_read:
forall u u' inum n off,
oracle_refines_same_from_related FileDiskRefinement u 
(|Read inum off|) (|Read inum off|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' None).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
         eapply recovery_oracles_refine_to_same; [| | |eauto| |]; eauto.
        (*Oracles refine same*)
        admit.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.

         eapply_fresh H13 in H;
         eapply_fresh H9 in H2;
         clear H9 H13;
         cleanup; repeat split_ors; cleanup;
         repeat unify_execs; cleanup; eauto.

         eapply_fresh H11 in H;
         eapply_fresh H8 in H2;
         clear H8 H11;
         cleanup; repeat split_ors; cleanup;
         repeat unify_execs; cleanup; eauto.
         erewrite ORS_recover with (l_o_abs := l0) (l_o_abs':= l); eauto.
         unfold refines_related; simpl.
         do 2 eexists. 
         unfold refines, files_rep, files_crash_rep in *.
        repeat (split; eauto).
     }
Admitted.
