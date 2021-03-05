Require Import Framework TotalMem FSParameters CachedDiskLayer.
Require Import Log RepImplications Specs LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Lia.

Set Nested Proofs Allowed.

Local Notation "'imp'" := CachedDiskLang.
Local Notation "'abs'" := (LoggedDiskLang log_length data_length).
Local Notation "'refinement'" := LoggedDiskRefinement.


  Definition cached_disk_reboot_list l_selector : list (imp.(state) -> imp.(state)) :=
    (map (fun selector (s: imp.(state)) =>
            (empty_mem, (fst (snd s), select_total_mem selector (snd (snd s)))))
         l_selector).

  Definition logged_disk_reboot_list n := repeat (fun s : abs.(state) => s) n.

  Ltac unify_execs :=
    match goal with
    |[H : recovery_exec ?u ?x ?y ?z ?a ?b ?c _,
      H0 : recovery_exec ?u ?x ?y ?z ?a ?b ?c _ |- _ ] =>
     eapply recovery_exec_deterministic_wrt_reboot_state in H; [| apply H0]
    | [ H: exec ?u ?x ?y ?z ?a _,
        H0: exec ?u ?x ?y ?z ?a _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec' ?u ?x ?y ?z _,
        H0: exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec _ ?u ?x ?y ?z _,
        H0: Language.exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    end.
  
  Lemma recovery_oracles_refine_to_length:
    forall O_imp O_abs (L_imp: Language O_imp) (L_abs: Language O_abs) (ref: Refinement L_imp L_abs)
      l_o_imp l_o_abs T (u: user) s (p1: L_abs.(prog) T) rec l_rf u, 
      recovery_oracles_refine_to ref u s p1 rec l_rf l_o_imp l_o_abs ->
      length l_o_imp = length l_o_abs.
  Proof.
    induction l_o_imp; simpl; intros; eauto.
    tauto.
    destruct l_o_abs; try tauto; eauto.
  Qed.

  Lemma select_mem_synced:
    forall A AEQ V (m: @mem A AEQ (V * list V)) selector (a: A) vs,
      select_mem selector m a = Some vs ->
      snd vs = nil.
  Proof.
    unfold select_mem; intros.
    destruct (m a); try congruence.
    inversion H; simpl; eauto.
  Qed.

  Lemma map_addr_list_eq_map_map:
    forall txns s hdr_state log_state valid_part hdr hdr_blockset log_blocksets,
      log_rep_explicit hdr_state log_state valid_part hdr txns hdr_blockset log_blocksets s ->
      map addr_list txns =
      map (map (Init.Nat.add data_start))
          (map (map (fun a => a - data_start)) (map addr_list txns)).
  Proof.
    intros.
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite map_noop; eauto.
    intros.
    unfold log_rep_explicit, log_rep_inner, txns_valid in *;
    simpl in *; cleanup_no_match.
    eapply Forall_forall in H9; eauto.
    unfold txn_well_formed in H9; simpl in *; cleanup_no_match.
    eapply Forall_forall in H13; eauto; lia.
  Qed.

  

  Lemma sumbool_agree_addr_dec:
    forall n x y,
      sumbool_agree (addr_dec x y) (addr_dec (n + x) (n + y)).
  Proof.
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x y);
    destruct (addr_dec (n + x) (n + y)); eauto;
    try congruence; try lia.
  Qed.
  
  Theorem abstract_oracles_exist_wrt_recover:
    forall l_selector u, 
      abstract_oracles_exist_wrt refinement refines_to_reboot u (|Recover|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_to_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto.
      eexists; intuition eauto.
      destruct t.
      left.
      eexists; intuition eauto.
      eapply recover_finished in H8; eauto.
      unify_execs; cleanup.
    }
    { 
      eapply IHl_selector in H12; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x0); simpl.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H0; eauto.
      intros; unify_execs; cleanup.
      eexists; repeat split; eauto;
      simpl in *.
      right.
      eexists; repeat split; eauto.
      intros.
      eapply_fresh recover_crashed in H11; eauto.
      logic_clean; eauto.
      eauto.
      
      eapply_fresh recover_crashed in H11; eauto.
      cleanup; repeat split_ors;
      simpl in *; unfold cached_log_reboot_rep in H0;
      cleanup;
      try eapply reboot_rep_to_reboot_rep in H0;
      try eapply crash_rep_recover_to_reboot_rep in H0;
      try eapply log_rep_to_reboot_rep in H0;
      eexists; unfold cached_log_reboot_rep; simpl;
      eexists; intuition eauto;
      match goal with
      |[H: select_total_mem _ _ _ = _ |- _ ]=>
       eapply select_total_mem_synced in H
      end; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_recover':
    forall l_selector u, 
      abstract_oracles_exist_wrt refinement refines_to u (|Recover|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_to_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto.
      eexists; intuition eauto.
      destruct t.
      left.
      eexists; intuition eauto.
      unfold refines_to, cached_log_reboot_rep in *; cleanup.
      eapply recover_finished in H7; eauto.
      eexists; intuition eauto.
      unify_execs; cleanup.
    }
    {
      unfold refines_to, cached_log_rep in *.
      cleanup.
      eapply log_rep_to_reboot_rep_same in H0.
              
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
      repeat split; eauto;
      intros; simpl in *; try unify_execs; cleanup.
      eapply recovery_oracles_refine_to_length in H1; eauto.
      eexists; repeat split; eauto.
      right.
      eexists; repeat split; eauto.
      intros.
      
      eapply_fresh recover_crashed in H10; eauto.
      logic_clean; eauto.
      eauto.
      
      eapply_fresh recover_crashed in H10; eauto;
      [|
        unfold cached_log_reboot_rep;
        eexists; intuition eauto
      ].
      cleanup; repeat split_ors;
      simpl in *; unfold cached_log_reboot_rep in H1;
      cleanup;
      try eapply reboot_rep_to_reboot_rep in H1;
      try eapply crash_rep_recover_to_reboot_rep in H1;
      try eapply log_rep_to_reboot_rep in H1;
      eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
      eexists; intuition eauto;
      match goal with
      |[H: select_total_mem _ _ _ = _ |- _ ]=>
       eapply select_total_mem_synced in H
      end; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_read:
    forall l_selector a u, 
      abstract_oracles_exist_wrt refinement refines_to u (|Read a|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_to_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto; simpl in *; try unify_execs; cleanup.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply_fresh read_finished in H7; eauto; cleanup.
      cleanup; eauto.
    }
    {
      unfold refines_to, cached_log_rep in *.
      cleanup.
      eapply_fresh log_rep_to_reboot_rep_same in H0.
              
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
      repeat split; eauto; intros; simpl in *; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_to_length in H1; eauto.
      
      eexists; repeat split; eauto.
      right; eexists; intuition eauto.      
      eapply_fresh read_crashed in H10; cleanup; eauto.
      eauto.
      {        
        eapply_fresh read_crashed in H10; cleanup; eauto.
        eapply reboot_rep_to_reboot_rep in Hx.
        eexists; unfold cached_log_reboot_rep; simpl.
        eexists; simpl; intuition eauto.
        unfold cached_log_reboot_rep; simpl.
        eexists; intuition eauto.
        simpl in *.
        eapply select_total_mem_synced in H1; eauto.
      }
    }
  Qed.

  Arguments cached_log_rep: simpl never.
  Arguments cached_log_crash_rep: simpl never.
  
  Theorem abstract_oracles_exist_wrt_write:
    forall l_selector l_a l_v u,
      abstract_oracles_exist_wrt refinement refines_to u (|Write l_a l_v|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_to_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto; try unify_execs; cleanup.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply_fresh write_finished in H7; eauto.
      unfold refines_to, cached_log_rep in *;
      cleanup; eauto.
      intuition eauto.
    }
    {
      unfold refines_to, cached_log_rep in *.
      cleanup.
      eapply_fresh write_crashed in H10; eauto.
      2: unfold cached_log_rep; eexists; eauto.
              
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      repeat split_ors.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H3; cleanup.
        left.
        unfold cached_log_rep in *; simpl in *; cleanup.
        eexists; intuition eauto.
        rewrite <- H6.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H4; eauto.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        rewrite H4; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      unfold cached_log_crash_rep in *; cleanup.
      split_ors; cleanup.
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        right.
        eexists; right; intuition eauto.
        right.
        unfold cached_log_crash_rep; simpl.
        intuition eauto.
        unfold cached_log_rep in *; cleanup.
        left; eexists; intuition eauto.
        setoid_rewrite <- H8.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H11; eauto.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        rewrite H11; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        
        unfold cached_log_rep in *; cleanup.
        left; intuition eauto.
        eapply crash_rep_log_write_to_reboot_rep in H3.
        unfold cached_log_reboot_rep.
        eexists; intuition eauto.
        simpl.

        unfold log_rep, log_reboot_rep, log_rep_general in *.
        logic_clean.
        erewrite map_addr_list_eq_map_map; eauto.
        rewrite shift_list_upd_batch_set_comm; eauto.
        setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
        rewrite shift_list_upd_batch_set_comm; eauto.
        rewrite shift_select_total_mem_synced.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H11; eauto.       
        repeat rewrite <- shift_list_upd_batch_set_comm.        
        repeat erewrite <- map_addr_list_eq_map_map; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H11; eauto.

        all: try apply sumbool_agree_addr_dec.
        all: try eapply log_rep_forall2_txns_length_match; eauto.
        all: unfold log_rep, log_rep_general; eauto.
        intros; apply H9; lia.
      }
      {
        eapply_fresh crash_rep_header_write_to_reboot_rep in H3.
        split_ors.
        {
          exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
          repeat split; eauto; intros; try unify_execs; cleanup.
          eapply recovery_oracles_refine_to_length in H1; eauto.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          right.
          eexists; right; intuition eauto.
          right.
          unfold cached_log_crash_rep; simpl.
          intuition eauto.
          unfold cached_log_rep in *; cleanup.
          right; do 2 eexists; intuition eauto;
          repeat rewrite <- sync_list_upd_batch_set in *.
          setoid_rewrite <- H8.
          setoid_rewrite <- H9.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite H13; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.

          setoid_rewrite <- H9.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite H13; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          
          unfold cached_log_rep in *; cleanup.
          left; intuition eauto.
          unfold cached_log_reboot_rep.
          eexists; intuition eauto.
          simpl.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.

          unfold log_rep, log_reboot_rep, log_rep_general in *.
          logic_clean.
          erewrite map_addr_list_eq_map_map; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          rewrite shift_select_total_mem_synced.
          
          repeat rewrite <- shift_list_upd_batch_set_comm.        
          repeat erewrite <- map_addr_list_eq_map_map; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H13; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          all: try eapply log_rep_forall2_txns_length_match; eauto.
          intros; apply H11; lia.
        }
        {
          exists ([OpToken (LoggedDiskOperation log_length data_length) CrashAfter]::x); simpl.
          repeat split; eauto; intros; try unify_execs; cleanup.
          eapply recovery_oracles_refine_to_length in H1; eauto.
          eexists; repeat split; eauto; try unify_execs; cleanup.        
          right.
          eexists; right; intuition eauto.
          right.
          unfold cached_log_crash_rep; simpl.
          intuition eauto.
          unfold cached_log_rep in *; cleanup.
          right; do 2 eexists; intuition eauto.
          repeat rewrite <- sync_list_upd_batch_set in *.

          setoid_rewrite <- H8.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H13; eauto.
          setoid_rewrite H9; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.

          setoid_rewrite <- H9.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H13; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          
          unfold cached_log_rep in *; cleanup.
          right; intuition eauto.
          unfold cached_log_reboot_rep.
          eexists; intuition eauto.
          simpl.
          
          unfold log_rep, log_reboot_rep, log_rep_general in *.
          logic_clean.
          erewrite map_addr_list_eq_map_map; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          rewrite shift_select_total_mem_synced.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H13; eauto.       
          repeat rewrite <- shift_list_upd_batch_set_comm.        
          repeat erewrite <- map_addr_list_eq_map_map; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H13;
          setoid_rewrite H9; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          all: try eapply log_rep_forall2_txns_length_match; eauto.
          all: unfold log_rep, log_rep_general; eauto.
          intros; apply H11; lia.
        }
        (** Non-colliding selector goal **)
        admit.
      }
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashAfter]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto; try unify_execs; cleanup.        
        right.
        eexists; right; intuition eauto.
        left.
        unfold cached_log_crash_rep in *; simpl; cleanup.
        intuition eauto.
        unfold cached_log_rep in *; cleanup.
        eexists; intuition eauto.
        repeat rewrite <- sync_list_upd_batch_set in *.
        setoid_rewrite <- H8.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H11; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H11; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H9; cleanup.
        right; left; eauto.
        unfold cached_log_crash_rep in *;
        simpl in *; cleanup.
        eexists; intuition eauto.
        setoid_rewrite <- H8.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H9; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H9; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H11; cleanup.
        right; right; eauto.
        unfold cached_log_crash_rep in *;
        simpl in *; cleanup.
        eexists; intuition eauto.
        (* setoid_rewrite <- H6. *)
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H11; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H11; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      {
        repeat split_ors.
        {
          unfold cached_log_rep in *; cleanup; eauto;
          try eapply log_rep_to_reboot_rep in H3;
          eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
          eexists; intuition eauto.
          eapply select_total_mem_synced in H6; eauto.
        }
        {
          unfold cached_log_crash_rep in *; cleanup; eauto.
          split_ors; cleanup.
          split_ors; cleanup.
          {
            eapply crash_rep_log_write_to_reboot_rep in H1.
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H9; eauto.
          }
          {
            eapply crash_rep_header_write_to_reboot_rep in H1.
            split_ors;
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H12; eauto.
            eapply select_total_mem_synced in H12; eauto.
            (** Non-colliding selector goal **)
            admit.
          }
          split_ors; cleanup.
          {
            eapply log_rep_to_reboot_rep in H1.
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H9; eauto.
          }
          split_ors; cleanup.
          {
            eapply crash_rep_apply_to_reboot_rep in H1.
            split_ors;
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H8; eauto.
            eapply select_total_mem_synced in H8; eauto.
          }
          {
            eapply log_rep_to_reboot_rep in H1.
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H9; eauto.
          }
        }
      }
    }
  Admitted.

  Fixpoint not_init {T} (p_abs: abs.(prog) T) :=
    match p_abs with
    |Op _ o =>
     match o with
     | Init _ => False
     | _ => True
     end
    |Ret _ => True
    |Bind p1 p2 =>
     not_init p1 /\ (forall r, not_init (p2 r))
    end.
    
  Theorem abstract_oracles_exists_logged_disk:
    forall T (p_abs: abs.(prog) T) l_selector u,
      not_init p_abs ->
      abstract_oracles_exist_wrt refinement refines_to u p_abs (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt; induction p_abs;
    simpl; intros; cleanup_no_match.
    {(** OPS **)
      destruct o; intuition.
      eapply abstract_oracles_exist_wrt_read; eauto.
      eapply abstract_oracles_exist_wrt_write; eauto.
      eapply abstract_oracles_exist_wrt_recover'; eauto.
    }
    {
      repeat invert_exec; cleanup.
      {
        rewrite <- H2; simpl.
        exists [[Language.Cont (LoggedDiskOperation log_length data_length)]]; simpl; intuition.
        right; intuition eauto.
        unify_execs; cleanup.
      }
      {
        destruct l_selector; simpl in *; try congruence; cleanup.
        repeat invert_exec.
        invert_exec'' H9.
        eapply abstract_oracles_exist_wrt_recover in H11; eauto.
        cleanup.
        exists ([Language.Crash (LoggedDiskOperation log_length data_length)]::x0);
        simpl; intuition eauto.
        apply recovery_oracles_refine_to_length in H1; eauto.
        left; eexists; intuition eauto.
        econstructor.
        invert_exec'' H2; eauto.
        unfold refines_to, cached_log_rep in *.
        cleanup.
        eapply log_rep_to_reboot_rep in H1.
        unfold refines_to_reboot, cached_log_reboot_rep.
        do 2 eexists; intuition eauto.
        eapply select_total_mem_synced in H2; eauto.
      }
    }
    {
      repeat invert_exec.
      {
        invert_exec'' H12.
        edestruct IHp_abs; eauto.
        instantiate (2:= []); simpl.
        eapply ExecFinished; eauto.
        edestruct H.
        eauto.
        2: {
          instantiate (3:= []); simpl.
          eapply ExecFinished; eauto.
        }
        eapply exec_compiled_preserves_refinement_finished in H10; eauto.
        simpl in *; cleanup; try tauto.
        simpl in *.
        exists ([o0 ++ o]); intuition eauto.
        do 4 eexists; intuition eauto.
        right; simpl; repeat eexists; intuition eauto.
        invert_exec; split_ors; cleanup; repeat (unify_execs; cleanup).        
        eapply finished_not_crashed_oracle_prefix in H10; eauto.
        eapply exec_finished_deterministic_prefix in H10; eauto; cleanup.
        unify_execs; cleanup.
      }
      {
        destruct l_selector; simpl in *; try congruence; cleanup.
        invert_exec'' H11.
        {
          edestruct IHp_abs; eauto.
          instantiate (2:= []); simpl.
          instantiate (1:= RFinished d1' r).
          eapply ExecFinished; eauto.
          edestruct H.
          eauto.
          2: {
            instantiate (3:= t::l_selector); simpl.
            instantiate (1:= Recovered (extract_state_r ret)).
            econstructor; eauto.
          }
          eapply exec_compiled_preserves_refinement_finished in H9; eauto.
          simpl in *; cleanup; try tauto.
          simpl in *.
          exists ((o0 ++ o)::l); intuition eauto.
          - invert_exec; try split_ors; repeat (unify_execs; cleanup).
            eapply exec_finished_deterministic_prefix in H9; eauto; cleanup.
            unify_execs; cleanup.
          - invert_exec; cleanup; try split_ors; try cleanup;
            repeat (unify_execs; cleanup).
            exfalso; eapply finished_not_crashed_oracle_prefix in H9; eauto.
            eapply exec_finished_deterministic_prefix in H9; eauto; cleanup.
            unify_execs; cleanup; eauto.
            specialize H6 with (1:= H14); cleanup.
            do 4 eexists; intuition eauto.
            right; simpl; repeat eexists; intuition eauto.
          - invert_exec; cleanup; try split_ors; try cleanup;
            repeat (unify_execs; cleanup).
            exfalso; eapply finished_not_crashed_oracle_prefix in H9; eauto.
            eapply exec_finished_deterministic_prefix in H9; eauto; cleanup.
            unify_execs; cleanup; eauto.
            specialize H6 with (1:= H14); cleanup; eauto.
        }
        {
          edestruct IHp_abs; eauto.
          instantiate (2:= t::l_selector); simpl.
          instantiate (1:= Recovered (extract_state_r ret)).
          econstructor; eauto.
          simpl in *; cleanup; try tauto.
          simpl in *.
          exists (o::l); intuition eauto.
          - invert_exec; cleanup; try split_ors;
            cleanup; repeat (unify_execs; cleanup).            
            exfalso; eapply finished_not_crashed_oracle_prefix in H6; eauto.
          - invert_exec; cleanup; try split_ors;
            cleanup; repeat (unify_execs; cleanup).
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H8; eauto; cleanup.
            specialize H5 with (1:= H8).
            clear H7.
            logic_clean; eauto.
            exists o1, o2, o, nil; intuition eauto.
            rewrite app_nil_r; eauto.
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6;
            eauto; cleanup.
          - invert_exec; cleanup; try split_ors;
            cleanup; repeat (unify_execs; cleanup).
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6; eauto; cleanup.
            specialize H5 with (1:= H8).
            clear H7.
            logic_clean; eauto.
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6;
            eauto; cleanup.
        }
      }
    }
  Qed.


(*
Section TransferToCachedDisk.

  Theorem transfer_to_CachedDisk:
    forall related_states_h
      valid_state_h
      valid_prog_h,
      
      SelfSimulation
        LoggedDiskLang
        valid_state_h
        valid_prog_h
        related_states_h ->
      
      oracle_refines_to_same_from_related LoggedDiskRefinement related_states_h ->
      
      exec_compiled_preserves_validity LoggedDiskRefinement                           
                                       (refines_to_valid LoggedDiskRefinement valid_state_h) ->
      
      SelfSimulation
        CachedDiskLang
        (refines_to_valid LoggedDiskRefinement valid_state_h)
        (compiles_to_valid LoggedDiskRefinement valid_prog_h)
        (refines_to_related LoggedDiskRefinement related_states_h).
  Proof.
    intros; eapply transfer_high_to_low; eauto.
    apply sbs.
    apply high_oracle_exists_ok.
  Qed.

End TransferToCachedDisk.
*)
