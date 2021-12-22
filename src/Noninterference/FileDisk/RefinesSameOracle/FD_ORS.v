Require Import AuthenticationLayer TransactionalDiskLayer AuthenticatedDiskLayer.
Require Import Framework File FileDiskLayer FileDiskNoninterference FileDiskRefinement.
Require Import FunctionalExtensionality Lia TSCommon SameRetType.


Lemma write_refines_same_core_input:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum off v v',
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' (Some inum) x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|Write inum off v|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|Write inum off v'|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    {
        unfold write in *.
        eapply auth_then_exec_same_type_ret in H3; eauto.
        intuition congruence.
        intros; 
        eapply write_inner_same_type_ret; eauto.
    }
    {
        repeat split_ors; cleanup; try lia; try congruence.
        unfold same_for_user_except in *; cleanup.
        edestruct H1; exfalso.
        apply H8; eauto; congruence.
        unfold same_for_user_except in *; cleanup.
        eapply H8 in H11; eauto; cleanup.
        split_ors; cleanup; try lia; tauto.
    }
    {
        unfold write in *.
        eapply auth_then_exec_same_type_ret in H3; eauto.
        intuition congruence.
        intros; 
        eapply write_inner_same_type_ret; eauto.
    }
    {
        repeat split_ors; cleanup; try lia; try congruence.
        unfold same_for_user_except in *; cleanup.
        edestruct H1; exfalso.
        apply H12; eauto; congruence.
        unfold same_for_user_except in *; cleanup.
        eapply H11 in H4; eauto; cleanup.
        split_ors; cleanup; try lia; tauto.
    }
    {
        eapply write_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        congruence.
    }
    {
        eapply write_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        congruence.
    }
    Unshelve.
    all: eauto.
Qed.



Lemma write_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum off v v' ex,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' ex x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|Write inum off v|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|Write inum off v'|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    {
        unfold write in *.
        eapply auth_then_exec_same_type_ret in H3; eauto.
        intuition congruence.
        intros; 
        eapply write_inner_same_type_ret; eauto.
    }
    {
        repeat split_ors; cleanup; try lia; try congruence.
        unfold same_for_user_except in *; cleanup.
        edestruct H1; exfalso.
        apply H8; eauto; congruence.
        unfold same_for_user_except in *; cleanup.
        eapply H8 in H11; eauto; cleanup.
        split_ors; cleanup; try lia; tauto.
    }
    {
        unfold write in *.
        eapply auth_then_exec_same_type_ret in H3; eauto.
        intuition congruence.
        intros; 
        eapply write_inner_same_type_ret; eauto.
    }
    {
        repeat split_ors; cleanup; try lia; try congruence.
        unfold same_for_user_except in *; cleanup.
        edestruct H1; exfalso.
        apply H12; eauto; congruence.
        unfold same_for_user_except in *; cleanup.
        eapply H11 in H4; eauto; cleanup.
        split_ors; cleanup; try lia; tauto.
    }
    {
        inversion H15; intuition.
    }
    {
        inversion H10; intuition.
    }
Qed.


Lemma extend_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum v v' ex,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' ex x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|Extend inum v|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|Extend inum v'|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    all: try solve [
        unfold extend in *;
        eapply auth_then_exec_same_type_ret in H3; eauto;[
        intuition congruence |
        intros; 
        eapply extend_inner_same_type_ret; eauto] ].
    all: try solve [
        repeat split_ors; cleanup; try lia; try congruence; 
        [ unfold same_for_user_except in *; cleanup;
        edestruct H1; exfalso;
        match goal with
        [H: ?x _ = Some _,
        H0: ?x0 _ = None,
        H1: ?x _ <> None -> ?x0 _ <> None |- _] =>
        apply H1; eauto; congruence
        end
        |unfold same_for_user_except in *; cleanup;
        match goal with
        [H: ?x ?inum = Some _,
        H0: forall _ _ _, ?x _ = Some _ -> _ |- _] =>
        eapply H0 in H; eauto; cleanup;
        try split_ors; cleanup; try lia; tauto
        end] ].
    {
        eapply extend_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        congruence.
    }
    {
        eapply extend_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        congruence.
    }
    Unshelve.
    all: eauto.
Qed.




Lemma change_owner_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum v,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' (Some inum) x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|ChangeOwner inum v|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|ChangeOwner inum v|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    all: try solve [
        repeat split_ors; cleanup; try lia; try congruence; 
        [ unfold same_for_user_except in *; cleanup;
        edestruct H1; exfalso;
        match goal with
        [H: ?x _ = Some _,
        H0: ?x0 _ = None,
        H1: ?x _ <> None -> ?x0 _ <> None |- _] =>
        apply H1; eauto; congruence
        end
        |unfold same_for_user_except in *; cleanup;
        match goal with
        [H: ?x ?inum = Some _,
        H0: forall _ _ _, ?x _ = Some _ -> _ |- _] =>
        eapply H0 in H; eauto; cleanup;
        try split_ors; cleanup; try lia; tauto
        end] ].

    all: try solve [
        unfold change_owner in *;
        eapply auth_then_exec_same_type_ret in H3; eauto;[
        intuition congruence |
        intros; 
        eapply change_owner_inner_same_type_ret; eauto] ].
    {
        eapply change_owner_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        congruence.
    }
    {
        eapply change_owner_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        congruence.
    }
    Unshelve.
    all: eauto.
Qed.


Lemma delete_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' inum ex,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' ex x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|Delete inum|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|Delete inum|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    all: try solve [
        repeat split_ors; cleanup; try lia; try congruence; 
        [ unfold same_for_user_except in *; cleanup;
        edestruct H1; exfalso;
        match goal with
        [H: ?x _ = Some _,
        H0: ?x0 _ = None,
        H1: ?x _ <> None -> ?x0 _ <> None |- _] =>
        apply H1; eauto; congruence
        end
        |unfold same_for_user_except in *; cleanup;
        match goal with
        [H: ?x ?inum = Some _,
        H0: forall _ _ _, ?x _ = Some _ -> _ |- _] =>
        eapply H0 in H; eauto; cleanup;
        try split_ors; cleanup; try lia; tauto
        end] ].

    all: try solve [
        unfold delete in *;
        eapply auth_then_exec_same_type_ret in H3; eauto;[
        intuition congruence |
        intros; 
        eapply delete_inner_same_type_ret; eauto] ].
    {
        eapply delete_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        congruence.
    }
    {
        eapply delete_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        congruence.
    }
    Unshelve.
    all: eauto.
Qed.

Lemma create_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' own ex,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' ex x x0 ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s1_imp 
    (|Create own|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ FD FDOperationRefinement _ u s2_imp 
    (|Create own|) get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs'.
Proof.
    simpl; intros; cleanup.
    repeat match goal with
    [H: refines ?s _ ,
    H0: forall _, files_rep _ ?s -> _ |- _] =>

    specialize H0 with (1:= H)
    end;
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup;
    repeat split_ors; cleanup;
    eauto; try lia; try congruence.
    all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
    eauto; try congruence].
    all: try solve [
        eapply create_same_type_ret in H3; eauto; intuition congruence].
    {
        unfold same_for_user_except in *; cleanup.
        destruct (Compare_dec.lt_dec x5 x6).
        edestruct H1; exfalso.
        eapply H12; eauto.
        destruct_fresh (x x5); eauto.
        exfalso; eapply H14; eauto.
        eapply Compare_dec.not_lt in n.
        inversion n; subst; eauto.

        edestruct H1; exfalso.
        eapply H7.
        instantiate (1:= x6); lia.
        destruct_fresh (x0 x6); eauto.
        exfalso; eapply H16. 
        2: eauto.
        congruence.
    }

{
    unfold same_for_user_except in *; cleanup.
    edestruct H1.
    exfalso; eapply H12; eauto.
}
{
    unfold same_for_user_except in *; cleanup.
    edestruct H1.
    exfalso; eapply H11; eauto.
}

    
    {
        eapply create_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        congruence.
    }
    {
        eapply create_crashed_same_token in H2.
        5: apply H3.
        all: eauto.
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
        }
        2:{
            simpl.
            intros.
            unfold refines in *;
            repeat match goal with
            |[H: files_rep _ ?s,
            H0 : files_rep _ ?s |- _] =>

            eapply FileInnerSpecs.files_rep_eq in H; eauto; subst
            end.
            right.
            eexists; intuition eauto.
            right; eexists; intuition eauto.
        }
        congruence.
    }
    {
        unfold same_for_user_except in *; cleanup.
        destruct (Compare_dec.lt_dec x5 x6).
        edestruct H1; exfalso.
        eapply H12; eauto.
        destruct_fresh (x x5); eauto.
        exfalso; eapply H14; eauto.
        eapply Compare_dec.not_lt in n.
        inversion n; subst; eauto.

        edestruct H1; exfalso.
        eapply H7.
        instantiate (1:= x6); lia.
        destruct_fresh (x0 x6); eauto.
        exfalso; eapply H16. 
        2: eauto.
        congruence.
    }
    Unshelve.
    all: eauto.
Qed.






Lemma recovery_oracles_refine_to_same:
    forall l_o_imp l_o_abs l_o_abs' s1_imp s2_imp x x0 u u' ex T (p1 p2: FD.(prog) T),
    (forall o_imp o_abs o_abs' get_reboot_state,
    refines s1_imp x ->
    refines s2_imp x0 ->
same_for_user_except u' ex x x0 ->
oracle_refines _ _ _ _ FDOperationRefinement _ u s1_imp 
p1 get_reboot_state  o_imp o_abs ->
oracle_refines _ _ _ _ FDOperationRefinement _ u s2_imp 
p2 get_reboot_state  o_imp o_abs' ->
    o_abs = o_abs') ->
    
    refines s1_imp x ->
    refines s2_imp x0 ->
same_for_user_except u' ex x x0 ->
recovery_oracles_refine_to FDRefinement u s1_imp p1 
    (| Recover |) [] l_o_imp l_o_abs ->
recovery_oracles_refine_to FDRefinement u s2_imp p2
    (| Recover |) [] l_o_imp l_o_abs' ->
l_o_abs = l_o_abs'.
Proof.
    induction l_o_imp; simpl; intros; try tauto.
    cleanup; simpl in *; try tauto; try lia.
    repeat split_ors; cleanup;
    repeat unify_execs; cleanup; try tauto.
    eapply H in H10; eauto; subst; eauto.
Unshelve.
eauto.
    Qed.


Lemma ORS_recover_stronger:
forall (u: user)(n : nat)
  (l_o_imp : list (oracle AD))
  (l_o_abs l_o_abs' : list (oracle FD))
  (s1_imp s2_imp : state AD),
  (exists sa1 sa2 : state FD,
   Simulation.Definitions.refines FDRefinement s1_imp sa1 /\
   Simulation.Definitions.refines FDRefinement s2_imp sa2) ->
recovery_oracles_refine_to FDRefinement u s1_imp 
  (| Recover |) (| Recover |) (authenticated_disk_reboot_list n) l_o_imp
  l_o_abs ->
recovery_oracles_refine_to FDRefinement u s2_imp 
  (| Recover |) (| Recover |) (authenticated_disk_reboot_list n) l_o_imp
  l_o_abs' -> l_o_abs = l_o_abs'.
Proof.
    induction n;
    simpl; intros; cleanup.
    {
        destruct l_o_imp; simpl in *; cleanup; eauto; try tauto.
        repeat split_ors; cleanup; 
        try unify_execs; cleanup; try tauto.
        specialize (H5 (fun s => s)).
        specialize (H8 (fun s => s)).
        cleanup; try tauto.
        
        edestruct H7; edestruct H6.
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
    specialize (H5 (fun s => s)).
    specialize (H8 (fun s => s)).
    cleanup; try tauto.
    
    edestruct H7; edestruct H6.
    all: try solve [unfold refines,
    files_rep, files_reboot_rep in*;
    cleanup; simpl; eauto];
    cleanup; repeat unify_execs; cleanup.

    edestruct H10; edestruct H7.
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


Lemma ORS_recover:
forall u u' ex n,
oracle_refines_same_from_related FDRefinement u 
(|Recover|)  (|Recover|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' ex).
Proof.
unfold oracle_refines_same_from_related,
refines_related; intros.
eapply ORS_recover_stronger; eauto.
cleanup; eauto.
Qed.


Lemma ORS_create:
forall u u' n own ex,
oracle_refines_same_from_related FDRefinement u 
(|Create own|) (|Create own|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' ex).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | | eauto | |]; eauto.
        intros.
        eapply create_refines_same_core; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         specialize (H6 (fun s => s)).
         specialize (H9 (fun s => s)).
         cleanup; try tauto.

         erewrite create_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite create_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.

Lemma ORS_change_owner:
forall u u' n inum own,
oracle_refines_same_from_related FDRefinement u 
(|ChangeOwner inum own|) (|ChangeOwner inum own|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' (Some inum)).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | | eauto | |]; eauto.
        intros.
        eapply change_owner_refines_same_core; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.

        specialize (H6 (fun s => s)).
        specialize (H9 (fun s => s)).
        cleanup; try tauto.

         erewrite change_owner_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite change_owner_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.


Lemma ORS_delete:
forall u u' n inum ex,
oracle_refines_same_from_related FDRefinement u 
(|Delete inum|) (|Delete inum|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' ex).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | | eauto | |]; eauto.
        intros.
        eapply delete_refines_same_core; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.

        specialize (H6 (fun s => s)).
        specialize (H9 (fun s => s)).
        cleanup; try tauto.

         erewrite delete_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite delete_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.



Lemma ORS_write:
forall u u' inum n off v,
oracle_refines_same_from_related FDRefinement u 
(|Write inum off v|) (|Write inum off v|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' None).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | | eauto | |]; eauto.
        intros.
        eapply write_refines_same_core; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         specialize (H6 (fun x => x)).
         specialize (H9 (fun x => x)).
         simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         erewrite write_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite write_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.


Lemma ORS_write_input:
forall u u' inum n off v v',
oracle_refines_same_from_related FDRefinement u 
(|Write inum off v|) (|Write inum off v'|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' (Some inum)).
Proof. 
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | | eauto | |]; eauto.
        intros.
        eapply write_refines_same_core_input; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         specialize (H6 (fun x => x)).
         specialize (H9 (fun x => x)).
         simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         erewrite write_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite write_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.

Lemma ORS_extend:
forall u u' inum n v v' ex,
oracle_refines_same_from_related FDRefinement u 
(|Extend inum v|) (|Extend inum v'|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' ex).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | |eauto| |]; eauto.
        intros.
        eapply extend_refines_same_core; [| | eauto| |]; eauto.
     }
     {
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.


        specialize (H6 (fun s => s)).
        specialize (H9 (fun s => s)).
        cleanup; try tauto.

         erewrite extend_refines_same_core with (o_abs := [OpToken FDOp x6]).
        eauto.
        3: eauto.
        apply H.
        apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite extend_refines_same_core with (o_abs := [OpToken FDOp x4]).
        4: eauto.
        2: apply H.
        2: apply H2.
        all: try solve [simpl; eexists; intuition eauto].

        erewrite ORS_recover_stronger with (l_o_abs:= l0).
        eauto.
        2: eauto.
        2: eauto.
        unfold refines_related; simpl.
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
        all: repeat unify_execs; cleanup; eauto.
        all: do 2 eexists; split; [| split; [| eauto]];
            unfold refines, files_rep, files_crash_rep in *; simpl in *; cleanup; eauto.
        }
        Unshelve.
        all: eauto.
Qed.

Lemma ORS_read:
forall u u' inum n off,
oracle_refines_same_from_related FDRefinement u 
(|Read inum off|) (|Read inum off|) (|Recover|) 
(authenticated_disk_reboot_list n) (same_for_user_except u' None).
Proof.
    unfold oracle_refines_same_from_related,
    refines_related; intros; destruct n; simpl in *; cleanup.
     {
        eapply recovery_oracles_refine_to_same; [| | |eauto| |]; eauto.
        intros; simpl in *.
        cleanup. 
        repeat match goal with
        [H: refines ?s _ ,
        H0: forall _, files_rep _ ?s -> _ |- _] =>

        specialize H0 with (1:= H)
        end;
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup;
        repeat split_ors; cleanup;
        eauto; try lia; try congruence.
        all: try solve [exfalso; eapply exec_finished_not_crashed_AD; 
        eauto; try congruence].
     }
     {
         
         destruct l_o_imp; simpl in *; try tauto.
         cleanup; try tauto.
         repeat split_ors; cleanup; 
         repeat unify_execs; cleanup;
         simpl in *; try lia.
         specialize (H6 (fun s => s)).
         specialize (H9 (fun s => s)).
         cleanup; try tauto.

         eapply_fresh H8 in H;
         eapply_fresh H7 in H2;
         clear H8 H7;
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
Qed.
