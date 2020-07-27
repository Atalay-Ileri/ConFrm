Require Import Framework FSParameters TransactionCacheLayer TransactionalDiskLayer.
Require Import Transaction TransactionToTransactionalDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Omega.

Set Nested Proofs Allowed.

Notation "'low'" := TransactionCacheLang.
Notation "'high'" := (TransactionalDiskLang data_length).
Notation "'refinement'" := TransactionalDiskRefinement.

Section TransactionalDiskBisimulation.

  Lemma addrs_match_upd:
    forall A AEQ V1 V2 (m1: @mem A AEQ V1) (m2: @mem A AEQ V2) a v,
      addrs_match m1 m2 ->
      m2 a <> None ->
      addrs_match (upd m1 a v) m2.
  Proof.
    unfold addrs_match; intros; simpl.
    destruct (AEQ a a0); subst;
    [rewrite upd_eq in *
    |rewrite upd_ne in *]; eauto.
  Qed.

  Lemma cons_l_neq:
    forall V (l:list V) v,
      ~ v::l = l.
  Proof.
    induction l; simpl; intros; try congruence.
  Qed.

  Lemma mem_union_some_l:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a v,
      m1 a = Some v ->
      mem_union m1 m2 a = Some v.
  Proof.
    unfold mem_union; simpl; intros.
    cleanup; eauto.
  Qed.
  
  Lemma mem_union_some_r:
    forall AT AEQ V (m1: @mem AT AEQ V) m2 a,
      m1 a = None ->
      mem_union m1 m2 a = m2 a.
  Proof.
    unfold mem_union; simpl; intros.
    cleanup; eauto.
  Qed.

  Lemma addrs_match_mem_union1 :
    forall A AEQ V (m1 m2: @mem A AEQ V),
      addrs_match m1 (mem_union m1 m2).
  Proof.
    unfold addrs_match; intros.
    destruct_fresh (m1 a); try congruence.
    erewrite mem_union_some_l; eauto.
  Qed.

  Lemma addrs_match_empty_mem:
    forall A AEQ V1 V2 (m: @mem A AEQ V1),
      addrs_match (@empty_mem A AEQ V2) m.
  Proof.
    unfold addrs_match, empty_mem;
    simpl; intros; congruence.
  Qed.
  
  Lemma apply_list_app:
    forall A AEQ V  l l' (m: @mem A AEQ V), 
      apply_list m (l++l') =
      apply_list (apply_list m l) l'.
  Proof.
    induction l; simpl; eauto.
  Qed.
  
  Lemma apply_list_get_latest_eq :
    forall l a,
      get_latest l a = apply_list empty_mem (rev l) a.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite apply_list_app; simpl.
    destruct (addr_eq_dec a0 (fst a)); subst.          
    rewrite upd_eq; eauto.
    rewrite upd_ne; eauto.
  Qed.

  Lemma empty_mem_some_false:
    forall A AEQ V (m: @mem A AEQ V) a v,
      m = empty_mem ->
      m a <> Some v.
  Proof.
    intros.
    rewrite H.
    unfold empty_mem; simpl; congruence.
  Qed.

  Lemma apply_list_in:
    forall A AEQ V (l: list (A * V)) (m: @mem A AEQ V) a v,
      In a (map fst l) ->
      apply_list (upd m a v) l = apply_list m l.
  Proof.
    induction l; intros; simpl in *; intuition.
    cleanup.
    rewrite upd_repeat; eauto.
    simpl.
    destruct (AEQ a0 a1); subst.
    rewrite upd_repeat; eauto.
    rewrite upd_comm; eauto.
  Qed.

  Lemma mem_union_upd_batch_eq:
    forall A AEQ V (l: list (A * V)) (m m1: @mem A AEQ V),
      mem_union (apply_list m1 l) m =
      upd_batch (mem_union m1 m) (dedup_last AEQ (map fst l))
                (dedup_by_list AEQ (map fst l) (map snd l)).
  Proof.
    induction l; simpl; intros; eauto.
    destruct a; simpl.
    destruct (in_dec AEQ a (map fst l)); eauto.
    rewrite apply_list_in; eauto.
    simpl; eauto.
    rewrite <- mem_union_upd; eauto.
  Qed.

  Lemma upd_batch_none:
    forall A AEQ V (l1: list A) l2 (m: @mem A AEQ V) a,
      upd_batch m l1 l2 a = None ->
      m a = None.
  Proof.
    induction l1; simpl; intros; eauto.
    destruct l2; eauto.
    apply IHl1 in H.
    destruct (AEQ a a0); subst.
    rewrite upd_eq in *; eauto; congruence.
    rewrite upd_ne in *; eauto.
  Qed.

  
  Lemma dedup_last_in:
    forall A AEQ (l: list A) a,
      In a l <-> In a (dedup_last AEQ l).
  Proof.
    induction l; simpl; intros; try tauto.
    destruct (AEQ a a0); subst; split; intros; eauto.
    destruct (in_dec AEQ a0 l); simpl; eauto.
    apply IHl; eauto.
    intuition.
    destruct (in_dec AEQ a l); simpl; intuition eauto.
    apply IHl; eauto.
    right; apply IHl; eauto.

    right; destruct (in_dec AEQ a l); intuition eauto.
    apply IHl; eauto.
    inversion H; intuition.
    apply IHl; eauto.
  Qed.
  
  Lemma dedup_last_NoDup:
    forall A AEQ (l: list A),
      NoDup (dedup_last AEQ l).
  Proof.
    induction l; simpl; intros; try constructor.
    destruct (in_dec AEQ a l); eauto.
    constructor; eauto.
    intuition.
    apply dedup_last_in in H; eauto.
  Qed.

  Lemma apply_list_in_not_none:
    forall A AEQ V (l: list (A * V)) (m: @mem A AEQ V) a, 
      In a (dedup_last AEQ (map fst (rev l))) ->
      apply_list m (rev l) a <> None.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite map_app in *.
    rewrite apply_list_app; simpl in *.
    destruct a; simpl in *.
    destruct (AEQ a a0).
    rewrite upd_eq; eauto; congruence.
    rewrite upd_ne; eauto.
    apply dedup_last_in in H.
    apply IHl.
    apply dedup_last_in.
    apply in_app_or in H; simpl in *; intuition eauto.
  Qed.
              
  
  Theorem exec_compiled_preserves_refinement:
    exec_compiled_preserves_refinement refinement.
  Proof.
    unfold exec_compiled_preserves_refinement.
    induction p2; simpl; intros; cleanup.
     { (** Op p **)
       destruct p; simpl in *.
      
       { (** Start **)
         repeat match goal with
          |[H: exec _ _ _ _ _ |- _ ] =>
           inversion H; cleanup; clear H
          |[H: Language.exec' _ _ _ _ |- _ ] =>
           inversion H; cleanup; clear H
          |[H: Operation.exec _ _ _ _ _ |- _ ] =>
           inversion H; cleanup; clear H
          end;
         cleanup;
         simpl; eauto.
         
         exists (empty_mem, snd x).
         unfold refines_to in *; simpl; cleanup;
         eexists; simpl; intuition eauto.
         simpl; apply addrs_match_empty_mem. 
         
         exists (empty_mem, snd x).
         unfold refines_to in *; simpl; cleanup;
         eexists; intuition eauto.
         simpl; apply addrs_match_empty_mem.
      }
       { (** Read **)
         unfold read in *.
         cleanup; repeat invert_exec;
         simpl; eauto;
         try split_ors; repeat cleanup;
         repeat (
             match goal with
             |[H: exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Language.exec' _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Operation.exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             end;
             cleanup;
             simpl; eauto).
      }
       { (** Write **)
         unfold write in *;
         cleanup; repeat invert_exec;
         simpl; eauto;
         try split_ors; repeat cleanup;
         repeat (
             match goal with
             |[H: exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Language.exec' _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Operation.exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             end;
             cleanup;
             simpl; eauto).

         unfold refines_to in *; simpl; cleanup;
         intuition eauto.
         
        exists (upd (fst x) a v, snd x).
        eexists; intuition eauto.
        simpl.
        rewrite apply_list_app; simpl.
        setoid_rewrite H0; eauto.
        simpl; rewrite apply_list_app; simpl.
        apply addrs_match_upd; eauto.

        unfold refines_to in *; simpl; cleanup;
        intuition eauto.
         
        exists (upd (fst x) a v, snd x).
        eexists; intuition eauto.
        simpl.
        rewrite apply_list_app; simpl.
        setoid_rewrite H0; eauto.
        simpl; rewrite apply_list_app; simpl.
        apply addrs_match_upd; eauto.      
      }
       { (** Commit **)
         unfold commit in *;
         cleanup; repeat invert_exec;
         simpl; eauto;
         try split_ors; repeat cleanup;
         repeat (
             match goal with
             |[H: exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Language.exec' _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Operation.exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             end;
             cleanup;
             simpl; eauto).
         
        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (empty_mem, mem_union (fst x) (snd x)).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.
          simpl.
          rewrite H0, H2.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          apply mem_union_upd_batch_eq.
          simpl in *.
          apply upd_batch_none in H5; eauto.

        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (empty_mem, snd x).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.

          exfalso; eapply H5.
          apply dedup_last_dedup_by_list_length_le.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          repeat rewrite map_length; eauto.

          simpl in *; cleanup.
          exists (empty_mem, snd x).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.

        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (empty_mem, mem_union (fst x) (snd x)).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.
          simpl.
          rewrite H0, H2.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          apply mem_union_upd_batch_eq.
          apply upd_batch_none in H5; eauto.

        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (empty_mem, snd x).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.

          exfalso; eapply H5.
          apply dedup_last_dedup_by_list_length_le.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          repeat rewrite map_length; eauto.

          exists (empty_mem, snd x).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.

        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (fst x, mem_union (fst x) (snd x)).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.
          eapply H1; eauto.
          eapply upd_batch_none; eauto.
          simpl; rewrite H0, H2.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          apply mem_union_upd_batch_eq.          
          apply upd_batch_none in H5; eauto.

        - unfold refines_to in *; simpl; cleanup;
          intuition eauto.
          exists (fst x, mem_union (fst x) (snd x)).
          eexists; intuition eauto.
          simpl.
          unfold addrs_match in *; intuition eauto; simpl in *.
          eapply H1; eauto.
          eapply upd_batch_none; eauto.
          simpl; rewrite H0, H2.
          repeat rewrite <- map_fst_split.
          repeat rewrite <- map_snd_split.
          apply mem_union_upd_batch_eq.
          apply upd_batch_none in H6; eauto.
          
       }
       { (** Abort **)
         unfold abort in *;
         cleanup; repeat invert_exec;
         simpl; eauto;
         try split_ors; repeat cleanup;
         repeat (
             match goal with
             |[H: exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Language.exec' _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             |[H: Operation.exec _ _ _ _ _ |- _ ] =>
              inversion H; cleanup; clear H
             end;
             cleanup;
             simpl; eauto).
         
        exists (empty_mem, snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.        
        unfold addrs_match; intuition eauto.

        exists (empty_mem, snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.        
        unfold addrs_match; intuition eauto.
      }
    }
    {(** Ret **)
      repeat invert_exec;
      cleanup;
      simpl; eauto.
    }
    {(** Bind **)
      repeat invert_exec;
      cleanup;
      simpl in *; eauto.

      {(** Finished **)
        edestruct IHp2; eauto; simpl in *.
        edestruct H; eauto; simpl in *.
      }
      {(** Crashed **)
        split_ors; cleanup.
        - edestruct IHp2; eauto; simpl in *.

        - edestruct IHp2; eauto; simpl in *.
          edestruct H; eauto; simpl in *.
      }
    }
  Qed.
    

  Theorem exec_preserves_refinement:
    exec_preserves_refinement refinement.
  Proof.
    unfold exec_preserves_refinement.
    induction p; simpl; intros; cleanup.
    { (** Op p **)
      destruct p; simpl in *;
      repeat invert_exec;
      cleanup;
      try match goal with
          |[H: exec' _ _ _ _ _ |- _ ] =>
           inversion H
          end;
      cleanup;
      simpl; eauto.
      { (** Start **)
        exists (Some [], snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.
        
        unfold addrs_match; intuition eauto.
      }
      { (** Start **)
        exists (Some [], snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.        
        unfold addrs_match; intuition eauto.
      }
      { (** Write **)
        unfold refines_to in *; simpl; cleanup;
        intuition eauto.

        exists (Some ((a,v)::x0), snd x).
        eexists; intuition eauto.
        simpl.
        rewrite apply_list_app; simpl.
        setoid_rewrite H0; eauto.
        simpl; rewrite apply_list_app; simpl.
        unfold addrs_match in *; intuition eauto; simpl in *.
        destruct (addr_dec a a0); subst; cleanup; eauto.
        rewrite upd_ne in H4; eauto.
      }
      { (** Write **)
        unfold refines_to in *; simpl; cleanup;
        intuition eauto.

        exists (Some ((a,v)::x0), snd x).
        eexists; intuition eauto.
        simpl.
        rewrite apply_list_app; simpl.
        setoid_rewrite H1; eauto.
        simpl; rewrite apply_list_app; simpl.
        unfold addrs_match in *; intuition eauto; simpl in *.
        destruct (addr_dec a a0); subst; cleanup; eauto.
        rewrite upd_ne in H5; eauto.
      }
      { (** Commit **)
        unfold refines_to in *; simpl; cleanup;
        intuition eauto.

        exists (Some [], mem_union (apply_list empty_mem (rev x0)) (snd x)).
        eexists; intuition eauto.
        simpl; apply addrs_match_empty_mem.
        simpl in *; eauto.
        apply mem_union_none_sel in H5; cleanup; eauto.
      }
      { (** Commit **)
        unfold refines_to in *; simpl; cleanup;
        intuition eauto.

        exists (Some [], mem_union (apply_list empty_mem (rev x0)) (snd x)).
        eexists; intuition eauto.
        simpl;  apply addrs_match_empty_mem.
        simpl in *; eauto.
        apply mem_union_none_sel in H6; cleanup; eauto.
      }
      { (** Commit **)
        unfold refines_to in *; simpl; cleanup;
        intuition eauto.

        exists (Some x0, mem_union (apply_list empty_mem (rev x0)) (snd x)).
        eexists; intuition eauto.
        simpl.
        unfold addrs_match in *; intuition eauto; simpl in *.
        destruct_fresh (apply_list empty_mem (rev x0) a); try congruence.
        erewrite mem_union_some_l in H6; eauto; congruence.
        simpl in *; eauto.
        apply mem_union_none_sel in H6; cleanup; eauto.
      }
      
      { (** Abort **)
        exists (Some [], snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.
        unfold addrs_match; intuition eauto.
      }
      { (** Abort **)
        exists (Some [], snd x).
        unfold refines_to in *; simpl; cleanup;
        eexists; intuition eauto.
        unfold addrs_match; intuition eauto.
      }
    }
    {(** Ret **)
      repeat invert_exec;
      cleanup;
      simpl; eauto.
    }
    {(** Bind **)
      repeat invert_exec;
      cleanup;
      simpl; eauto.

      {(** Finished **)
        edestruct IHp; eauto; simpl in *.
        edestruct H; eauto; simpl in *.
      }
      {(** Crashed **)
        split_ors; cleanup.
        - edestruct IHp; eauto; simpl in *.

        - edestruct IHp; eauto; simpl in *.
          edestruct H; eauto; simpl in *.
      }
    }
  Qed.
  
  (** w(c)p and s(c)p implications **)
  Lemma wp_low_to_high_read :
    forall a,
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wp_low_to_high_prog'; intros; cleanup.
    simpl in H1; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.
    eexists; intuition eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H2; eauto.
    simpl in *; intuition eauto.

    cleanup; simpl in *; cleanup; eauto;
    intuition eauto; unfold refines_to in *; cleanup;
    try congruence.
    destruct s1; simpl in *; cleanup.
    unfold read in *; repeat (simpl in *; cleanup);
    try rewrite apply_list_get_latest_eq in D1; eauto;
    try solve [left; intuition eauto; repeat (eexists; intuition eauto) ];
    try solve [right; intuition eauto; omega ].
    right; intuition eauto; try omega.
    repeat (eexists; intuition eauto).
  Qed.

  Lemma wp_high_to_low_read :
    forall a,
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wp_high_to_low_prog'; intros; cleanup.
    simpl in *; cleanup.
    repeat (invert_exec; repeat cleanup).
    destruct H3; try solve [cleanup; repeat split_ors; cleanup ].
    
    cleanup.
    eapply exec_to_wp; eauto; simpl.
    split; eauto.
    repeat (split_ors; cleanup); try congruence; try omega;
    eapply exec_to_sp with (P := fun o s => refines_to s s2') in H;
    unfold read in H; repeat (simpl in *; cleanup); eauto; try omega; try congruence.
    
    rewrite apply_list_get_latest_eq in D0; cleanup; simpl in *; cleanup;
    unfold refines_to in H; simpl in *; cleanup;    
    repeat split_ors; cleanup; eauto;
    try setoid_rewrite H2 in D; cleanup; eauto.

    rewrite apply_list_get_latest_eq in D0; cleanup; simpl in *; cleanup;
    unfold refines_to in H; simpl in *; cleanup;    
    repeat split_ors; cleanup; eauto;
    try setoid_rewrite H2 in D; cleanup; eauto.

    setoid_rewrite H2 in H1;
    cleanup.
    setoid_rewrite H2 in H1;
    cleanup.

    setoid_rewrite H3 in H1;
    cleanup.
    setoid_rewrite H3 in H1;
    cleanup.

    rewrite apply_list_get_latest_eq in D0; cleanup; simpl in *; cleanup;
    unfold refines_to in H; simpl in *; cleanup;    
    repeat split_ors; cleanup; eauto;
    try setoid_rewrite H2 in D; cleanup; eauto.

    rewrite apply_list_get_latest_eq in D0; cleanup; simpl in *; cleanup;
    unfold refines_to in H; simpl in *; cleanup;    
    repeat split_ors; cleanup; eauto;
    try setoid_rewrite H2 in D; cleanup; eauto.

    repeat (split_ors; cleanup); try omega.
    eapply exec_to_wp; eauto; simpl.
    split; eauto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2') in H;
    unfold read in H; repeat (simpl in *; cleanup); eauto; try omega; try congruence.
  Qed.

 
  Lemma wcp_low_to_high_read :
    forall a,
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wcp_low_to_high_prog'; intros; cleanup.
    simpl in H, H0, H1, H2; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H1; eauto; cleanup.

    split_ors; cleanup; eauto.
    eapply exec_to_scp with (P:= fun o s => refines_to s s2 /\ s = s1 /\ o = o1) in H2; eauto.
    clear H.
    unfold read in *;
    repeat (try split_ors; repeat cleanup; simpl in * ); try omega;
    try solve [try (inversion H; clear H; cleanup);
    eexists; intuition eauto].
    eexists; intuition eauto.

    eapply exec_to_scp with (P:= fun o s => refines_to s s2 /\ s = s1 /\ o = o1) in H2; eauto.
    clear H.
    unfold read in *;
    repeat (try split_ors; repeat cleanup; simpl in * ); try omega;

    try solve [
          try (inversion H1; clear H1; cleanup);
          eexists; intuition eauto;
          right; left; intuition eauto;
          try destruct s1; simpl in *; cleanup;
          unfold refines_to in *; simpl in *; cleanup;
          match goal with
            |[H: get_latest _ _ = _ |- _ ] =>
             rewrite apply_list_get_latest_eq in H
          end;
          eexists; eauto ];
    try solve [
          eexists; intuition eauto;
          right; right; intuition eauto; omega].
Qed.
  
  Lemma wcp_high_to_low_read :
    forall a,
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Read a|).
  Proof.
    unfold wcp_high_to_low_prog'; simpl; intros; cleanup.
    repeat (split_ors; cleanup);
    repeat invert_exec;
    cleanup;
    repeat match goal with
    | [H: Operation.exec _ _ _ _ _ |- _ ] =>
      inversion H; clear H; cleanup
    | [H: exec' _ _ _ _ _ |- _ ] =>
      inversion H; clear H; cleanup
    end;
    eapply exec_to_wcp; eauto.
  Qed.

  Lemma wp_low_to_high_write :
    forall a vl,
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wp_low_to_high_prog'; simpl; intros; cleanup.
    apply wp_to_exec in H; cleanup.
    eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2) in H2; eauto.
    unfold write in *.
    repeat (simpl in *; cleanup).
    
    - eexists; intuition eauto; cleanup.
      left; simpl in *; intuition eauto.
      unfold refines_to in *; simpl in *; cleanup; intuition eauto.
      unfold refines_to in *; simpl in *; cleanup.
      eexists; intuition eauto.
      simpl; rewrite apply_list_app; eauto.
      omega.
      right; left; intuition eauto.      
      unfold refines_to in *; simpl in *; cleanup; intuition eauto.

    - eexists; intuition eauto; cleanup.
      simpl in *.
      left; intuition eauto.      
      unfold refines_to in *; simpl in *; cleanup; intuition eauto.
      unfold refines_to in *; simpl in *; cleanup; intuition eauto.      
      simpl in *; cleanup.
      simpl in *.
      eexists; intuition eauto.
      simpl.
      rewrite apply_list_app; simpl.
      apply upd_repeat.
      omega.
      right; left; intuition eauto.
      unfold refines_to in *; simpl in *; cleanup; intuition eauto.

    - eexists; intuition eauto; cleanup; try omega.
Qed.

  Lemma wp_high_to_low_write :
    forall a vl,
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wp_high_to_low_prog'; simpl; intros; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s1 s /\ s = s2 /\ o = [OpOracle (TransactionalDiskOperation data_length) x]) in H2; eauto.
    simpl in *; cleanup.
    

    repeat (split_ors; cleanup); try omega.
    - eapply exec_to_wp; simpl; eauto.
      eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
      unfold write in *.
      repeat (simpl in *; cleanup; try omega).
      unfold refines_to in *; simpl in *; cleanup.
      split; auto.
      
      destruct s1; simpl in *; cleanup.
      eexists; intuition eauto.
      simpl in *; cleanup.
      rewrite apply_list_app; simpl; eauto.
      simpl in *; cleanup.
      rewrite apply_list_app; simpl; eauto.
      unfold addrs_match in *; intros.
      destruct (addr_dec a a0); subst; eauto.
      rewrite upd_ne in H; eauto.
      
      destruct s1; simpl in *; cleanup.
      simpl in *; cleanup.
      exfalso; eapply cons_l_neq; eauto.

    - eapply exec_to_wp; simpl; eauto.
      eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1 /\ o = o1) in H; eauto.
      unfold write in *.
      repeat (simpl in *; cleanup; try omega).
      
      unfold refines_to in *; simpl in *; cleanup.
      split; auto.
      destruct s1; simpl in *.
      inversion H11; subst; clear H11.
      inversion H3; subst; clear H3.
      symmetry in H2; exfalso; eapply cons_l_neq; eauto.
      
      destruct s1; simpl in *; cleanup.
      unfold refines_to in *; simpl in *; cleanup.
      split; auto.
      eexists; intuition eauto.

    - eapply exec_to_wp; simpl; eauto.
      eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
      unfold write in *.
      repeat (simpl in *; cleanup; try omega).
            
      destruct s1; simpl in *; cleanup.
      unfold refines_to in *; simpl in *; cleanup.
      split; auto.
      eexists; intuition eauto.
  Qed.

  
  Lemma wcp_low_to_high_write :
    forall a vl,
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
    eapply wcp_to_exec in H; cleanup.
    eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    split_ors; cleanup;
    eexists; intuition eauto.

    right; intuition eauto.
    eapply exec_to_scp with (P := fun o s => refines_to s s2 /\ s = s1 /\ o = o1) in H2; eauto.
    unfold write in *;
    repeat (simpl in *; cleanup; try split_ors);
    try (inversion H; cleanup; clear H);
    destruct s1; simpl in *; cleanup; simpl in *; eauto;
    try (destruct s; simpl in *; try congruence);
    try solve [cleanup; exfalso; eapply cons_l_neq; eauto].
    cleanup.
    left; intuition eauto.
    unfold refines_to in *; simpl in *; cleanup; intuition eauto.

    unfold refines_to in *; simpl in *; cleanup.
    eexists; intuition eauto.
    simpl; rewrite apply_list_app; simpl; eauto.
  Qed.

  Lemma wcp_high_to_low_write :
    forall a vl,
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Write a vl|).
  Proof.
    unfold wcp_high_to_low_prog'; simpl; intros; cleanup.
    repeat split_ors; cleanup; repeat invert_exec;
    try inversion H8; try clear H8; cleanup;
    try inversion H9; try clear H9; cleanup;
    eapply exec_to_wcp; eauto;
    repeat (split_ors; cleanup); eauto;
    
    repeat invert_exec;
    repeat match goal with
           | [H: Operation.exec _ _ _ _ _ |- _ ] =>
             inversion H; clear H; cleanup
           | [H: exec' _ _ _ _ _ |- _ ] =>
             inversion H; clear H; cleanup
           end; try omega.
    
    unfold refines_to in *; simpl in *; cleanup.
    eexists; intuition eauto.
    simpl; rewrite apply_list_app; simpl; eauto.
    setoid_rewrite H2; eauto.
    simpl in *; cleanup.
    rewrite apply_list_app; simpl; eauto.
    apply addrs_match_upd; eauto.
      

    -
      eapply exec_to_scp with (P := fun o s => refines_to s s2' /\ s = s1 /\ o = o1) in H; eauto.
      unfold write in *;
      repeat (simpl in *; cleanup; try split_ors);
      try (inversion H; cleanup; clear H);
      destruct s1; simpl in *; cleanup; simpl in *; eauto;
      try (destruct s; simpl in *; try congruence);
      try solve [cleanup; exfalso; eapply cons_l_neq; eauto].
      omega.
      Unshelve.
      all: eauto.
  Qed.

  Lemma wp_low_to_high_start :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl; eauto.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wp_high_to_low_start :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    destruct x0; simpl; split; auto.
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wcp_low_to_high_start :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    repeat (split_ors; cleanup; eauto);
    inversion H3; clear H3; cleanup; eauto;
    eexists; intuition eauto.
    right; split; eauto.    
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
    right; split; eauto.    
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wcp_high_to_low_start :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Start|).
  Proof.
    unfold wcp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1, H2; cleanup.
    repeat (split_ors; cleanup);
    repeat invert_exec; cleanup;
    eapply exec_to_wcp; eauto.

    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.

    simpl; unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  
  Lemma wp_low_to_high_abort :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
     unfold wp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
    simpl in *; cleanup.
    eexists; intuition eauto.
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl; eauto.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wp_high_to_low_abort :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    destruct x0; simpl; split; auto.
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wcp_low_to_high_abort :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    repeat (split_ors; cleanup; eauto);
    inversion H3; clear H3; cleanup; eauto;
    eexists; intuition eauto.
    right; split; eauto.    
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
    right; split; eauto.    
    unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  Lemma wcp_high_to_low_abort :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Abort|).
  Proof.
    unfold wcp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1, H2; cleanup.
    repeat (split_ors; cleanup);
    repeat invert_exec; cleanup;
    eapply exec_to_wcp; eauto.

    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.

    simpl; unfold refines_to in *; cleanup; eauto.
    eexists; intuition eauto.
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
  Qed.

  
  Lemma wp_low_to_high_commit :
    wp_low_to_high_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
    simpl in *; cleanup.
    eexists; repeat (split; eauto); simpl in *;
    unfold refines_to in *; simpl in *; cleanup; eauto.
    eexists; repeat (split; eauto).
    simpl; eauto.
    apply addrs_match_empty_mem.
    unfold not in *; intros.
    apply mem_union_none_sel in H2.
    cleanup; eauto.
  Qed.

  Lemma wp_high_to_low_commit :
    wp_high_to_low_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1; cleanup.
    repeat (split_ors; cleanup).

    repeat invert_exec; cleanup.    
    eapply exec_to_wp; eauto.
    destruct x0; simpl; split; auto.
    eapply exec_to_sp with (P := fun o s => refines_to s s2 /\ s = s1) in H; eauto.
    simpl in *; cleanup; simpl in *.
    unfold refines_to in *; cleanup; eauto.
    eexists; repeat (split; eauto).
    simpl.
    unfold addrs_match; intros.
    unfold empty_mem in *; simpl in *; congruence.
    simpl in *.
    inversion H; subst; eauto.
    simpl; unfold not in *; intros.
    apply mem_union_none_sel in H11.
    cleanup; eauto.
  Qed.

  Lemma wcp_low_to_high_commit :
    wcp_low_to_high_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wcp_low_to_high_prog'; simpl; intros; cleanup.
    split_ors; cleanup; eapply exec_deterministic_wrt_oracle in H2; eauto; cleanup.
    unfold refines_to in *; simpl in *; cleanup.
    repeat (split_ors; cleanup; eauto);
    try (inversion H6; clear H6; simpl in *; cleanup); eauto;
    eexists; repeat (split; eauto);
    try solve [left; split; eauto; eexists; eauto;
               unfold not in *; intros; eauto];
    try solve [ right; left; split; eauto;
                eexists; intuition eauto;
                try apply addrs_match_mem_union1;
                unfold not in *; simpl in *; intros; eauto;
                match goal with
                |[H: mem_union _ _ _ = None |- _] =>
                 apply mem_union_none_sel in H
                end; cleanup; eauto];
    try solve [right; right; split; eauto;
               eexists; intuition eauto;
               simpl; try apply addrs_match_empty_mem;
               unfold not in *; simpl in *; intros; eauto;
               match goal with
                |[H: mem_union _ _ _ = None |- _] =>
                 apply mem_union_none_sel in H
               end; cleanup; eauto].
  Qed.

  Lemma wcp_high_to_low_commit :
    wcp_high_to_low_prog' _ _ _ _ refinement _ (|Commit|).
  Proof.
    unfold wcp_high_to_low_prog'; intros; cleanup.
    simpl in H, H0, H1, H2; cleanup.
    repeat (split_ors; cleanup);
    repeat invert_exec; cleanup;
    eapply exec_to_wcp; eauto.

    repeat
      match goal with
      | [H: Operation.exec _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      | [H: exec' _ _ _ _ _ |- _ ] =>
        inversion H; clear H; cleanup
      end.

    eapply exec_to_scp with (P:= fun o s => refines_to s s2 /\ s = s1) in H; eauto.
    simpl in *; cleanup.
    repeat (try split_ors; cleanup; simpl in *);
            try (inversion H; clear H; cleanup);
            try (destruct s1; simpl in *; cleanup);
            
    simpl in *; unfold refines_to in *; cleanup; simpl in *; eauto;
    eexists; intuition eauto; cleanup; eauto.
            
   inversion H1; clear H1; cleanup.
   subst; simpl in *; eauto.
   simpl in *; unfold refines_to in *; cleanup.
   simpl in *; eauto;
   eexists; intuition eauto.
   simpl; apply addrs_match_empty_mem.
   rewrite H0 in H3; congruence.
    match goal with
    |[H: mem_union _ _ _ = None |- _] =>
     apply mem_union_none_sel in H; destruct H
    end; eauto.
  Qed.
      
  Theorem sbs_read :
    forall a,
      StrongBisimulationForProgram refinement (|Read a|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    eapply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_read.
    apply wp_high_to_low_read.    
    apply wcp_low_to_high_read.
    apply wcp_high_to_low_read.
  Qed.

  Theorem sbs_write :
    forall a lv,
      StrongBisimulationForProgram refinement (|Write a lv|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    eapply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_write.
    apply wp_high_to_low_write.
    apply wcp_low_to_high_write.
    apply wcp_high_to_low_write.
  Qed.

  Theorem sbs_start :
      StrongBisimulationForProgram refinement (|Start|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_start.
    apply wp_high_to_low_start.
    apply wcp_low_to_high_start.
    apply wcp_high_to_low_start.
  Qed.

  Theorem sbs_abort :
      StrongBisimulationForProgram refinement (|Abort|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_abort.
    apply wp_high_to_low_abort.
    apply wcp_low_to_high_abort.
    apply wcp_high_to_low_abort.
  Qed.

  Theorem sbs_commit :
      StrongBisimulationForProgram refinement (|Commit|).              
  Proof.
    intros.
    eapply bisimulation_from_wp_prog; eauto.
    exact exec_preserves_refinement.
    exact exec_compiled_preserves_refinement.
    apply Build_WP_Bisimulation_prog.
    apply wp_low_to_high_commit.
    apply wp_high_to_low_commit.
    apply wcp_low_to_high_commit.
    apply wcp_high_to_low_commit.
  Qed.

  Hint Resolve sbs_read sbs_write sbs_start sbs_abort sbs_commit : core.
  
  Theorem sbs :
      StrongBisimulation refinement.              
  Proof.
    apply bisimulation_restrict_prog.
    induction p; eauto.
    destruct p; eauto.
    apply sbs_ret.
    apply sbs_bind; eauto.
  Qed.

  Hint Resolve sbs : core.

  Theorem sbs_general:
    forall valid_state_h valid_prog_h,
      exec_compiled_preserves_validity refinement
        (refines_to_valid refinement valid_state_h) ->
      
      exec_preserves_validity high valid_state_h ->
      
      StrongBisimulationForValidStates refinement
        (refines_to_valid refinement valid_state_h)
        valid_state_h     
        valid_prog_h.  
  Proof.
    intros.
    eapply bisimulation_restrict_state; eauto.
  Qed.

End TransactionalDiskBisimulation.

Section TransferToTransactionCache.

Lemma high_oracle_exists_ok:
    high_oracle_exists refinement.
Proof.
  unfold high_oracle_exists; simpl.
  induction p2; simpl; intros; cleanup.
  { (** Op p **)
    destruct p; simpl in *.
    { (** Start **)
      destruct s1'.
      { (** Finished **)
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        simpl in *; cleanup.
        do 2 eexists; intuition eauto.
        left; do 2 eexists; intuition eauto.
        destruct s; simpl in *; subst; eauto.
      }
      { (** Crashed **)
        eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        simpl in *; cleanup.
        split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
        try (inversion H1; clear H1); cleanup; eauto;
        try solve [
              do 2 eexists; intuition eauto;
              right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
      }
    }
    { (** Read **)
      destruct s1'.
      { (** Finished **)
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        unfold read in Hx; simpl in Hx; cleanup;
        cleanup; simpl in *; cleanup;
        do 2 eexists; intuition eauto;
        left; do 2 eexists; intuition eauto;
        destruct s; cleanup; simpl in *; cleanup; eauto.
      }
      { (** Crashed **)
        eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        unfold read in Hx; repeat (simpl in *; cleanup).
        split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
        try (inversion H1; clear H1); cleanup; eauto;
        try solve [             
           do 2 eexists; intuition eauto;
           right; do 2 eexists; intuition eauto;
           destruct s; simpl in *; cleanup; eauto ].
      
        do 2 eexists; intuition eauto;
        right; do 2 eexists; intuition eauto;
        destruct s; simpl in *; cleanup; eauto.       
      }
    }
    { (** Write **)
      destruct s1'.
      { (** Finished **)
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        unfold write in Hx; simpl in *; cleanup;
        cleanup; simpl in *; cleanup;      
        try destruct s; cleanup; simpl in *; cleanup; eauto;
        
        do 2 eexists; intuition eauto;
        left; do 2 eexists; intuition eauto;
        try destruct s; cleanup; simpl in *; cleanup; eauto.
        right; right; eexists; intuition eauto.
        omega.
        right; left; intuition eauto.
        omega.
      }
      { (** Crashed **)
        eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        unfold write in Hx; repeat (simpl in *; cleanup).
        split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
        inversion H1; clear H1; cleanup; eauto;
        try solve [    
              do 2 eexists; intuition eauto;
              right; do 2 eexists; intuition eauto;
              destruct s; simpl in *; cleanup; eauto ].
        do 2 eexists; intuition eauto;
        right; do 2 eexists; intuition eauto;
        destruct s; simpl in *; cleanup; eauto.
      }
    }
    { (** Commit **)
      destruct s1'.
      { (** Finished **)
        eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
        simpl in *; cleanup.
        cleanup; simpl in *; cleanup;        
        do 2 eexists; intuition eauto;
        left; do 2 eexists; intuition eauto;
        destruct s; cleanup; simpl in *; cleanup; eauto;
        eexists; intuition eauto.
        
        rewrite <- map_fst_split, <- map_snd_split.
        rewrite mem_union_upd_batch_eq; eauto.
        
        exfalso; apply H; apply dedup_last_NoDup.
        

        exfalso; apply H2; apply dedup_last_dedup_by_list_length_le.
        rewrite <- map_fst_split, <- map_snd_split; repeat rewrite map_length; omega.
        unfold refines_to in *; cleanup; simpl in *; eauto.
        cleanup.

         unfold refines_to in *; simpl in *;
         cleanup; exfalso; eauto;
         match goal with
         | [H: addrs_match _ _ |- _ ] =>
           unfold addrs_match in H;
           eapply H
         end; eauto;
         apply apply_list_in_not_none; eauto;
         rewrite map_fst_split; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
       simpl in *; cleanup.
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       
       try solve [
             inversion H1; clear H1; cleanup; eauto;        
             do 2 eexists; intuition eauto;
             right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ];

       
       try solve [
             try (inversion H1; clear H1; cleanup; eauto);  
             repeat (split_ors; cleanup);
             try solve [
                   exfalso;
                   match goal with
                   | [H: ~ NoDup _ |- _] =>
                     apply H
                   end; apply dedup_last_NoDup ];
             try solve [
                   exfalso;
                   match goal with
                   | [H: ~ length _ = length _ |- _] =>
                     apply H
                   end;
                   apply dedup_last_dedup_by_list_length_le; eauto;        
                   rewrite <- map_fst_split, <- map_snd_split;
                   repeat rewrite map_length; eauto ];
             try solve [
                   unfold refines_to in *; simpl in *;
                   cleanup; exfalso; eauto;
                   match goal with
                   | [H: addrs_match _ _ |- _ ] =>
                     unfold addrs_match in H;
                     eapply H
                   end; eauto;
                   apply apply_list_in_not_none; eauto;
                   rewrite map_fst_split; eauto ];
             
             do 2 eexists; intuition eauto;
             right; do 2 eexists; intuition eauto;
             try solve [
                   right; left; intuition eauto;
                   destruct s; simpl in *; cleanup; eauto;
                   eexists; intuition eauto;        
                   setoid_rewrite mem_union_upd_batch_eq;
                   rewrite mem_union_empty_mem;
                   rewrite map_fst_split, map_snd_split; eauto ];
             try solve [
                   right; right; intuition eauto;
                   destruct s; simpl in *; cleanup; eauto;
                   eexists; intuition eauto;        
                   setoid_rewrite mem_union_upd_batch_eq;
                   rewrite mem_union_empty_mem;
                   rewrite map_fst_split, map_snd_split; eauto ]
           ].
       }
    }
    
  - (** Abort **)
    destruct s1'.
    {
      eapply exec_to_sp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
      simpl in *; cleanup.
      do 2 eexists; intuition eauto.
      left; do 2 eexists; intuition eauto.
      destruct s; simpl in *; subst; eauto.
    }
    {
      eapply exec_to_scp with (P := fun o s => refines_to s x /\ o = o1 /\ s = s1) in H0 as Hx; eauto.
      simpl in *; cleanup.
       split_ors; cleanup; repeat (simpl in *; try split_ors; cleanup);
       try (inversion H1; clear H1); cleanup; eauto;
       try solve [
             do 2 eexists; intuition eauto;
             right; do 2 eexists; intuition eauto;
             destruct s; simpl in *; cleanup; eauto ].
    }
  }
  - (** Ret **)
    destruct s1'; eexists; eauto.
  - (** Bind **)
    invert_exec.
    + (** Finished **)
      edestruct IHp2; eauto.
      eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *;  eauto.
      cleanup; simpl in *; eauto.
      edestruct H; eauto.
      do 5 eexists; repeat (split; eauto).
      right; eauto.
      do 3 eexists; repeat (split; eauto).
    + (* Crashed *)
      split_ors; cleanup.
      * (* p1 crashed *)
        edestruct IHp2; eauto.
        do 5 eexists; repeat (split; eauto).
      * (* p2 Crashed *)
        edestruct IHp2; eauto.
        eapply_fresh exec_compiled_preserves_refinement in H1; simpl in *; eauto.
        cleanup; simpl in *; eauto.
        edestruct H; eauto.
        do 5 eexists; repeat (split; eauto).
        right; eauto.
        do 3 eexists; repeat (split; eauto).
        Unshelve.
        all: constructor.
Qed.


Theorem transfer_to_TransactionCache:
    forall related_states_h
    valid_state_h
    valid_prog_h,
    
    SelfSimulation
      high
      valid_state_h
      valid_prog_h
      related_states_h ->
    
    oracle_refines_to_same_from_related refinement related_states_h ->

    exec_compiled_preserves_validity refinement                           
    (refines_to_valid refinement valid_state_h) ->
    
    SelfSimulation
      low
      (refines_to_valid refinement valid_state_h)
      (compiles_to_valid refinement valid_prog_h)
      (refines_to_related refinement related_states_h).
Proof.
  intros; eapply transfer_high_to_low; eauto.
  apply sbs.
  apply high_oracle_exists_ok.
Qed.

End TransferToTransactionCache.
