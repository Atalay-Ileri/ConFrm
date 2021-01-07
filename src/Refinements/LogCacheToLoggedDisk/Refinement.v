Require Import Framework TotalMem FSParameters CachedDiskLayer.
Require Import Log RepImplications Specs LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Lia.

Set Nested Proofs Allowed.

Local Notation "'imp'" := CachedDiskLang.
Local Notation "'abs'" := (LoggedDiskLang data_length).
Local Notation "'refinement'" := LoggedDiskRefinement.




Section LoggedDiskBisimulation.

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

  Lemma select_total_mem_synced:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)) selector (a: A) vs,
      select_total_mem selector m a = vs ->
      snd vs = nil.
  Proof.
    unfold select_total_mem; intros.
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

  Lemma shift_select_total_mem_synced:
    forall A AEQ V (tm: @total_mem A AEQ (V * list V)) selector f,
      (forall a, snd (tm (f a)) = []) ->
      shift f (select_total_mem selector tm) = shift f tm.
  Proof.
    intros.
    extensionality a; simpl.
    unfold shift, select_total_mem; simpl.
    rewrite select_for_addr_synced; eauto.
    erewrite <- (H a).
    destruct_fresh (tm (f a)); eauto.
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
      exists  [ [OpToken (LoggedDiskOperation data_length) Cont] ]; simpl.
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
      exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x0); simpl.
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
      exists  [ [OpToken (LoggedDiskOperation data_length) Cont] ]; simpl.
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
      exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
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
      exists  [ [OpToken (LoggedDiskOperation data_length) Cont] ]; simpl.
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
      exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
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
      exists  [ [OpToken (LoggedDiskOperation data_length) Cont] ]; simpl.
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
        exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
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
      {
        exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
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
        setoid_rewrite <- H4.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H6; eauto.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        rewrite H6; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        
        unfold cached_log_rep in *; cleanup.
        left; intuition eauto.
        eapply crash_rep_log_write_to_reboot_rep in H3.
        unfold cached_log_reboot_rep.
        eexists; intuition eauto.
        simpl.

        (*** NEW ******)
        unfold log_rep, log_reboot_rep, log_rep_general in *.
        logic_clean.
        erewrite map_addr_list_eq_map_map; eauto.
        rewrite shift_list_upd_batch_set_comm; eauto.
        setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
        rewrite shift_list_upd_batch_set_comm; eauto.
        rewrite shift_select_total_mem_synced.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H6; eauto.       
        repeat rewrite <- shift_list_upd_batch_set_comm.        
        repeat erewrite <- map_addr_list_eq_map_map; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H6; eauto.

        all: try apply sumbool_agree_addr_dec.
        all: try eapply log_rep_forall2_txns_length_match; eauto.
        all: unfold log_rep, log_rep_general; eauto.
        intros; apply H5; lia.
      }
      {
        eapply_fresh crash_rep_header_write_to_reboot_rep in H3.
        split_ors.
        {
          exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
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
          setoid_rewrite <- H4.
          setoid_rewrite <- H5.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite H8; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.

          setoid_rewrite <- H5.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite H8; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          
          unfold cached_log_rep in *; cleanup.
          left; intuition eauto.
          unfold cached_log_reboot_rep.
          eexists; intuition eauto.
          simpl.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.

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
          setoid_rewrite <- H8; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          all: try eapply log_rep_forall2_txns_length_match; eauto.
          intros; apply H6; lia.
        }
        {
          exists ([OpToken (LoggedDiskOperation data_length) CrashAfter]::x); simpl.
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

          setoid_rewrite <- H4.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H8; eauto.
          setoid_rewrite H5; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.

          setoid_rewrite <- H5.
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H8; eauto.
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
          eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H8; eauto.       
          repeat rewrite <- shift_list_upd_batch_set_comm.        
          repeat erewrite <- map_addr_list_eq_map_map; eauto.
          repeat rewrite total_mem_map_shift_comm in *.
          repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
          setoid_rewrite <- H8;
          setoid_rewrite H5; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          all: try eapply log_rep_forall2_txns_length_match; eauto.
          all: unfold log_rep, log_rep_general; eauto.
          intros; apply H6; lia.
        }
        (** Non-colliding selector goal **)
        admit.
      }
      {
        exists ([OpToken (LoggedDiskOperation data_length) CrashAfter]::x); simpl.
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
        setoid_rewrite <- e.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H3; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H3; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      {
        exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H4; cleanup.
        right; left; eauto.
        unfold cached_log_crash_rep in *;
        simpl in *; cleanup.
        eexists; intuition eauto.
        setoid_rewrite <- H6.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H4; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H4; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eauto.
      }
      {
        exists ([OpToken (LoggedDiskOperation data_length) CrashBefore]::x); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_to_length in H1; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H4; cleanup.
        right; right; eauto.
        unfold cached_log_crash_rep in *;
        simpl in *; cleanup.
        eexists; intuition eauto.
        setoid_rewrite <- H6.
        eapply empty_mem_list_upd_batch_eq_list_upd_batch_total in H4; eauto.
        repeat rewrite total_mem_map_shift_comm in *.
        repeat rewrite total_mem_map_fst_list_upd_batch_set in *.
        setoid_rewrite <- H4; eauto.
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
          {
            eapply crash_rep_log_write_to_reboot_rep in H1.
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H5; eauto.
          }
          {
            eapply crash_rep_header_write_to_reboot_rep in H1.
            split_ors;
            eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
            eexists; intuition eauto.
            eapply select_total_mem_synced in H6; eauto.
            eapply select_total_mem_synced in H6; eauto.
            (** Non-colliding selector goal **)
            admit.
          }
        }
        {
          unfold cached_log_crash_rep in *; cleanup; eauto.
          eapply log_rep_to_reboot_rep in H1.
          eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
          eexists; intuition eauto.
          eapply select_total_mem_synced in H5; eauto.
        }
        {
          unfold cached_log_crash_rep in *; cleanup; eauto.
          eapply crash_rep_apply_to_reboot_rep in H1.
          split_ors;
          eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
          eexists; intuition eauto.
          eapply select_total_mem_synced in H4; eauto.
          eapply select_total_mem_synced in H4; eauto.
        }
        {
          unfold cached_log_crash_rep in *; cleanup; eauto.
          eapply log_rep_to_reboot_rep in H1.
          eexists; unfold refines_to_reboot, cached_log_reboot_rep; simpl;
          eexists; intuition eauto.
          eapply select_total_mem_synced in H5; eauto.
        }
      }
    }
  Admitted.
    
  Theorem abstract_oracles_exists_logged_disk:
    forall T (p_abs: abs.(prog) T) l_selector u, 
      abstract_oracles_exist_wrt refinement refines_to u p_abs (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt; induction p_abs;
    simpl; intros; cleanup.
    {(** OPS **)
      destruct o.
      eapply abstract_oracles_exist_wrt_read; eauto.
      eapply abstract_oracles_exist_wrt_write; eauto.
      eapply abstract_oracles_exist_wrt_recover'; eauto.
    }
    {
      repeat invert_exec; cleanup.
      {
        rewrite <- H1; simpl.
        exists [[Language.Cont (LoggedDiskOperation data_length)]]; simpl; intuition.
        right; intuition eauto.
        unify_execs; cleanup.
      }
      {
        destruct l_selector; simpl in *; try congruence; cleanup.
        repeat invert_exec.
        invert_exec'' H8.
        eapply abstract_oracles_exist_wrt_recover in H10; eauto.
        cleanup.
        exists ([Language.Crash (LoggedDiskOperation data_length)]::x0);
        simpl; intuition eauto.
        apply recovery_oracles_refine_to_length in H0; eauto.
        left; eexists; intuition eauto.
        econstructor.
        invert_exec'' H1; eauto.
        unfold refines_to, cached_log_rep in *.
        cleanup.
        eapply log_rep_to_reboot_rep in H0.
        unfold refines_to_reboot, cached_log_reboot_rep.
        do 2 eexists; intuition eauto.
        eapply select_total_mem_synced in H1; eauto.
      }
    }
    {
      repeat invert_exec.
      {
        invert_exec'' H10.
        edestruct IHp_abs; eauto.
        instantiate (2:= []); simpl.
        eapply ExecFinished; eauto.
        edestruct H.
        2: {
          instantiate (3:= []); simpl.
          eapply ExecFinished; eauto.
        }
        (** refinement preserved via finished execs **)
        admit.
        simpl in *; cleanup; try tauto.
        simpl in *.
        exists ([o0 ++ o]); intuition eauto.
        do 4 eexists; intuition eauto.
        right; simpl; repeat eexists; intuition eauto.
        invert_exec; split_ors; cleanup; repeat (unify_execs; cleanup).        
        eapply finished_not_crashed_oracle_prefix in H8; eauto.
        eapply exec_finished_deterministic_prefix in H8; eauto; cleanup.
        unify_execs; cleanup.
      }
      {
        destruct l_selector; simpl in *; try congruence; cleanup.
        invert_exec'' H9.
        {
          edestruct IHp_abs; eauto.
          instantiate (2:= []); simpl.
          instantiate (1:= RFinished d1' r).
          eapply ExecFinished; eauto.
          edestruct H.
          2: {
            instantiate (3:= t::l_selector); simpl.
            instantiate (1:= Recovered (extract_state_r ret)).
            econstructor; eauto.
          }
          (** refinement preserved via finished execs **)
          admit.
          simpl in *; cleanup; try tauto.
          simpl in *.
          exists ((o0 ++ o)::l); intuition eauto.
          - invert_exec; try split_ors; repeat (unify_execs; cleanup).
            eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
            unify_execs; cleanup.
          - invert_exec; cleanup; try split_ors; try cleanup;
            repeat (unify_execs; cleanup).
            exfalso; eapply finished_not_crashed_oracle_prefix in H7; eauto.
            eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
            unify_execs; cleanup; eauto.
            specialize H4 with (1:= H12); cleanup.
            do 4 eexists; intuition eauto.
            right; simpl; repeat eexists; intuition eauto.
          - invert_exec; cleanup; try split_ors; try cleanup;
            repeat (unify_execs; cleanup).
            exfalso; eapply finished_not_crashed_oracle_prefix in H7; eauto.
            eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
            unify_execs; cleanup; eauto.
            specialize H4 with (1:= H12); cleanup; eauto.
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
            exfalso; eapply finished_not_crashed_oracle_prefix in H4; eauto.
          - invert_exec; cleanup; try split_ors;
            cleanup; repeat (unify_execs; cleanup).
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6; eauto; cleanup.
            specialize H3 with (1:= H6).
            clear H5.
            logic_clean; eauto.
            exists o1, o2, o, nil; intuition eauto.
            rewrite app_nil_r; eauto.
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6;
            eauto; cleanup.
          - invert_exec; cleanup; try split_ors;
            cleanup; repeat (unify_execs; cleanup).
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6; eauto; cleanup.
            specialize H3 with (1:= H6).
            clear H5.
            logic_clean; eauto.
            eapply_fresh exec_deterministic_wrt_oracle_prefix in H6;
            eauto; cleanup.
        }
      }
    }
  Admitted.

  Lemma ext_or_take_out:
    forall A P Q R,
      (exists a: A, P a) \/ (exists a: A, Q a) \/ (exists a : A, R a)->
      exists a: A, P a \/ Q a \/ R a.
  Proof.
    intros; intuition (cleanup; eauto).
  Qed.

  Lemma select_total_mem_synced_noop:
    forall A AEQ V (m: @total_mem A AEQ (V * list V)) selector,
      (forall a vs, m a = vs -> snd vs = nil) ->
      select_total_mem selector m = m.
  Proof.
    intros; extensionality a.
    unfold select_total_mem; simpl.
    destruct (m a) eqn:D; eauto.
    apply H in D; subst; eauto.
    simpl in *; subst; eauto.
    rewrite select_for_addr_synced; simpl; eauto.
  Qed.
  
Lemma recovery_simulation :
  forall l_selector u,
    SimulationForProgramGeneral _ _ _ _ refinement u _ (|Recover|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector))
                         refines_to_reboot refines_to.
Proof.
  unfold SimulationForProgramGeneral; induction l_selector; simpl; intros; cleanup.
  {
    destruct l_o_imp; intuition; simpl in *.
    cleanup; intuition.
    invert_exec; simpl in *; cleanup; intuition.
    specialize H2 with (1:= H12).
    cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
    
    eexists; intuition eauto.
    unfold logged_disk_reboot_list in *; simpl.
    simpl in *; destruct l; simpl in *; try lia.
    instantiate (1:= RFinished s_abs tt). 
    repeat econstructor.
    unfold refines_to, refines_to_reboot in *;
    simpl in *; cleanup; eauto.
    simpl; eauto.
  }
  {
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; intuition eauto; repeat (unify_execs; cleanup).
    clear H1.
    specialize H2 with (1:= H11).
    cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
    edestruct IHl_selector; eauto.
    instantiate (1:= s_abs).
    all: eauto.
    unfold refines_to_reboot in *; logic_clean.
    eapply_fresh recover_crashed in H11; eauto.
    cleanup; simpl in *; split; eauto.
    unfold cached_log_reboot_rep in *; cleanup.

    eapply ext_or_take_out in H3.
    cleanup.
    exists x1.
    simpl; split.
    cleanup; repeat split_ors;
    simpl in *; cleanup;
    try eapply reboot_rep_to_reboot_rep in H3;
    try eapply crash_rep_recover_to_reboot_rep in H3;
    try eapply log_rep_to_reboot_rep in H3;
    intuition eauto.
     
    assert (A: (map addr_list x1) = (map (map (Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x1)))). {
        rewrite map_map.
        setoid_rewrite map_ext_in at 2.
        rewrite map_id; eauto.
        intros.
        rewrite map_map.
        setoid_rewrite map_ext_in.
        rewrite map_id; eauto.
        intros; simpl.
        unfold log_rep, log_rep_general, log_crash_rep,
        log_reboot_rep, log_rep_explicit,
        log_rep_inner, txns_valid in *.
        simpl in *; logic_clean.
        repeat split_ors; cleanup;
        match goal with
        | [H: Forall (txn_well_formed _ _ _ _) _,
              H0: In _ (map _ _) |- _] =>
          apply in_map_iff in H0; logic_clean; subst;
          eapply Forall_forall in H; eauto;
          unfold txn_well_formed in H; logic_clean
        end;
        match goal with
        |[H: Forall (fun _ => _ > _ /\ _ >= _) _ |- _] =>
         eapply Forall_forall in H; eauto
        end;
        lia.
      }
      simpl.
      rewrite A.
      rewrite shift_list_upd_batch_set_comm.
      rewrite <- shift_select_total_mem_comm.
      rewrite select_total_mem_synced_noop.
      rewrite <- shift_list_upd_batch_set_comm.
      setoid_rewrite <- A; eauto.
      repeat split_ors; logic_clean; eauto;
      
      repeat rewrite total_mem_map_shift_comm in *;
      rewrite <- sync_list_upd_batch_set in H6;
      rewrite total_mem_map_fst_sync_noop in H6;
      eauto.
      
      {
        unfold sumbool_agree; intros.
        destruct (addr_dec x2 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
      }
      {
        intros.
        rewrite shift_some in H6.
        split_ors;
        rewrite H5 in H6; eauto.
        lia.
        unfold sync in H6.
        destruct_fresh (snd (snd s_imp) (data_start + a0));
        setoid_rewrite D in H6; inversion H6; simpl; eauto.
        lia.
      }
      {
        unfold sumbool_agree; intros.
        destruct (addr_dec x2 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
      }
      simpl in *.
      intros.
      eapply select_total_mem_synced in H6; eauto.
      
      simpl in *; logic_clean.
      exists (Recovered (extract_state_r x)).
      unfold logged_disk_reboot_list in *; simpl in *.
      econstructor.
      repeat econstructor; eauto.
      eauto.
  }
Qed. 

Lemma read_simulation :
  forall a l_selector u,
    SimulationForProgram refinement u (|Read a|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;
                        unify_execs; cleanup].
    {
      specialize H1 with (1:= H10).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      eapply_fresh read_finished in H10; cleanup; eauto.
      destruct l_selector; simpl in *; try congruence; cleanup.
      destruct l; simpl in *; try lia.
      unfold logged_disk_reboot_list; simpl.
      split_ors; cleanup.
      {
        exists (RFinished s_abs (s_abs a));
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
      {
        exists (RFinished s_abs value0);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
      }
    }
    {
      clear H1.
      specialize H3 with (1:= H9).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct l_selector; simpl in *; try congruence; cleanup.
      eapply_fresh read_crashed in H9; cleanup.
      
      edestruct recovery_simulation; eauto.
      unfold refines_to in *.
      apply H4 in H0.
      unfold refines_to_reboot; simpl.
      instantiate (1:= s_abs).
      unfold cached_log_rep, cached_log_reboot_rep in *; cleanup.
      eapply_fresh log_rep_to_reboot_rep in H1.
      intuition eauto.
      eexists; intuition eauto.
      simpl; eauto.

      unfold log_rep, log_reboot_rep, log_rep_general in *.
      logic_clean.
      setoid_rewrite map_addr_list_eq_map_map at 2; eauto.
      rewrite shift_list_upd_batch_set_comm; eauto.
      rewrite shift_select_total_mem_synced.      
      repeat rewrite <- shift_list_upd_batch_set_comm.        
      repeat erewrite <- map_addr_list_eq_map_map; eauto.
      
      all: try apply sumbool_agree_addr_dec.
      intros; apply H5; lia.
      apply select_total_mem_synced in H3; eauto.
      
      exists (Recovered (extract_state_r x)); simpl; intuition eauto.
      unfold logged_disk_reboot_list; simpl.
      eapply ExecRecovered; eauto.
      repeat econstructor.
    }
Qed.

Lemma write_simulation :
  forall l_a l_v l_selector u,
    SimulationForProgram refinement u (|Write l_a l_v|) (|Recover|)
                         (cached_disk_reboot_list l_selector)
                         (logged_disk_reboot_list (length l_selector)).
Proof.
  unfold SimulationForProgram, SimulationForProgramGeneral; simpl; intros; cleanup.
  
    invert_exec; simpl in *; cleanup; intuition;
    cleanup; try solve [intuition eauto; try congruence;    
    unify_execs; cleanup].
    {
      specialize H1 with (1:= H10).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      {
        eapply write_finished in H10; eauto.
        destruct l_selector; simpl in *; try congruence; cleanup.
        destruct l; simpl in *; try lia.
        unfold logged_disk_reboot_list; simpl.
        split_ors; cleanup.
        {
          exists (RFinished s_abs tt);
          simpl; intuition eauto.
          eapply ExecFinished.
          repeat econstructor; eauto.
          (** Need ~NoDup here **)
          admit.
          destruct x1; eauto.
        }
      {
        exists (RFinished (upd_batch s_abs l_a l_v) tt);
        simpl; intuition eauto.
        eapply ExecFinished.
        repeat econstructor; eauto.
        (** Need NoDup here **)
        admit.
        (** Need length l_a = length l_v here **)
        admit.
        destruct x1; eauto.
      }
    }
    {
      split_ors; cleanup;
      try unify_execs; cleanup;
      destruct l_selector; simpl in *; try congruence; cleanup.
      split_ors; cleanup;
      try unify_execs; cleanup;
      destruct l_selector; simpl in *; try congruence; cleanup.
    }
    }
    {
      unfold refines_to in *.
      clear H1.
      specialize H3 with (1:= H9).
      cleanup; intuition eauto; cleanup; try unify_execs; cleanup.
      destruct l_selector; simpl in *; try congruence; cleanup.
      
      repeat split_ors; cleanup; try unify_execs; cleanup.
      {
        specialize H4 with (1:= H0).
        repeat split_ors.
        {
          unfold cached_log_rep in *; cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.
            split.          
            eapply log_rep_to_reboot_rep in H3.
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H7; eauto.
          }
          {
          exists (Recovered (extract_state_r x2)); simpl; intuition eauto.        
          unfold logged_disk_reboot_list; simpl.
          eapply ExecRecovered.
          repeat econstructor.
          unfold refines_to, cached_log_rep in *; cleanup.
          unfold log_rep, log_reboot_rep, log_rep_general in *.
          logic_clean.
          erewrite map_addr_list_eq_map_map; eauto.
          rewrite shift_list_upd_batch_set_comm; eauto.
          erewrite <- shift_select_total_mem_synced.      
          repeat rewrite <- shift_list_upd_batch_set_comm.        
          repeat erewrite <- map_addr_list_eq_map_map; eauto.
          
          all: try apply sumbool_agree_addr_dec.
          intros; apply H5; lia.
          }
      }
        {
          unfold cached_log_crash_rep in *; cleanup.
          eapply crash_rep_apply_to_reboot_rep in H1.
          repeat split_ors; edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.          
            split.          
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H3; eauto.
          }
          {
            exists (Recovered (extract_state_r x1)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines_to, cached_log_rep in *; cleanup.
            unfold log_rep, log_reboot_rep, log_rep_general in *.
            logic_clean.
            erewrite map_addr_list_eq_map_map; eauto.
            rewrite shift_list_upd_batch_set_comm; eauto.
            erewrite <- shift_select_total_mem_synced.      
            repeat rewrite <- shift_list_upd_batch_set_comm.        
            repeat erewrite <- map_addr_list_eq_map_map; eauto.
            
            all: try apply sumbool_agree_addr_dec.
            (** Investigate this further **)
            admit.
          }
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.          
            split.
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H3; eauto.
          }
          {
            exists (Recovered (extract_state_r x1)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines_to, cached_log_rep in *; cleanup.
            simpl in *.
            unfold log_rep, log_reboot_rep, log_rep_general in *.
            logic_clean.
            erewrite map_addr_list_eq_map_map; eauto.
            rewrite shift_list_upd_batch_set_comm; eauto.
            erewrite <- shift_select_total_mem_synced.      
            repeat rewrite <- shift_list_upd_batch_set_comm.        
            repeat erewrite <- map_addr_list_eq_map_map; eauto.
            
            all: try apply sumbool_agree_addr_dec.
            intros; apply H5; lia.
            (** Need select_mem = m fact here **)
            admit.
          }
        }        
        {
          unfold cached_log_crash_rep in H1; cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.          
            split.          
            eapply log_rep_to_reboot_rep in H1.
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H3; eauto.
          }
          {
            exists (Recovered (extract_state_r x)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines_to, cached_log_rep in *; simpl in *; cleanup; eauto.
            (** Need select_mem = m fact here **)
            admit.
          }
        }
      }        
      {
        specialize H4 with (1:= H0).
        unfold cached_log_crash_rep in *; cleanup.
        edestruct recovery_simulation; eauto;
        try solve [eapply H3; eauto].
        {
          unfold refines_to_reboot, cached_log_reboot_rep; simpl.          
          split.          
          eapply log_rep_to_reboot_rep in H1.
          eexists; intuition eauto.
          intros.
          apply select_total_mem_synced in H4; eauto.
        }
        {
          exists (Recovered (extract_state_r x1)); simpl; intuition eauto.        
          unfold logged_disk_reboot_list; simpl.
          eapply ExecRecovered.
          repeat econstructor; eauto.
          (** Nodup goal **)
          admit.
          (** Length goal **)
          admit.
          (** Bound goal **)
          admit.            
          unfold refines_to, cached_log_rep in *; simpl in *; cleanup; eauto.
          setoid_rewrite H3; eauto.
          {
            unfold log_rep, log_rep_general in H1.
            rewrite <- sync_list_upd_batch_set.
            (** Need select_mem = m fact here **)
            admit.
          }
        }
        {
          specialize H3 with (1:= H0); cleanup.
          split_ors; cleanup.
          
        {
          unfold cached_log_reboot_rep in *; simpl in *;
          cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.
            split.       
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H4; eauto.
          }
          {
            exists (Recovered (extract_state_r x1)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor.
            unfold refines_to, cached_log_rep in *; simpl in *; cleanup; eauto.
          }
        }
        
        {
          unfold cached_log_reboot_rep in *; simpl in *;
          cleanup.
          edestruct recovery_simulation; eauto;
          try solve [eapply H3; eauto].
          {
            unfold refines_to_reboot, cached_log_reboot_rep; simpl.          
            split.       
            eexists; intuition eauto.
            intros.
            apply select_total_mem_synced in H5; eauto.
          }
          {
            exists (Recovered (extract_state_r x1)); simpl; intuition eauto.        
            unfold logged_disk_reboot_list; simpl.
            eapply ExecRecovered.
            repeat econstructor; eauto.
            (** Nodup goal **)
            admit.
            (** Length goal **)
            admit.
            (** Bound goal **)
            admit.  
            unfold refines_to, cached_log_rep in *; simpl in *; cleanup; eauto.
            setoid_rewrite H4; eauto.
            }
          }
      }
    }
  Admitted.


Theorem sbs_read :
  forall a,
    StrongBisimulationForProgram LoggedDiskRefinement (|Read a|).              
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
    StrongBisimulationForProgram LoggedDiskRefinement (|Write a lv|).              
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


Hint Resolve sbs_read sbs_write : core.

Theorem sbs :
  StrongBisimulation LoggedDiskRefinement.              
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
    exec_compiled_preserves_validity LoggedDiskRefinement
                                     (refines_to_valid LoggedDiskRefinement valid_state_h) ->
    
    exec_preserves_validity LoggedDiskLang valid_state_h ->
    
    StrongBisimulationForValidStates LoggedDiskRefinement
                                     (refines_to_valid LoggedDiskRefinement valid_state_h)
                                     valid_state_h      
                                     valid_prog_h.  
Proof.
  intros.
  eapply bisimulation_restrict_state; eauto.
Qed.
End LoggedDiskBisimulation.

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
