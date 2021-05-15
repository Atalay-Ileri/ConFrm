Require Import Framework LoggedDiskLayer TransactionCacheLayer TransactionalDiskLayer.
Require Import TransactionalDiskRefinement.
Require Import FunctionalExtensionality Lia FileDiskNoninterference.

Lemma read_refines_same_core:
forall u u' o_imp s1_imp s2_imp x x0  get_reboot_state 
o_abs o_abs' a v v' ex,
    refines s1_imp x ->
    refines s2_imp x0 ->
    same_for_user_except u' ex x x0 ->
    oracle_refines _ _ _ TransactionalDisk TransactionalDiskOperationRefinement _ u s1_imp 
    (|Read a v|) get_reboot_state  o_imp o_abs ->
    oracle_refines _ _ _ TransactionalDisk TransactionalDiskOperationRefinement _ u s2_imp 
    (|Read a v'|) get_reboot_state  o_imp o_abs' ->
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
    all: try solve [exfalso; eapply exec_finished_not_crashed_AuthenticatedDisk; 
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
