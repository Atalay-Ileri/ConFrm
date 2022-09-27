Require Import Framework TotalMem FSParameters CachedDiskLayer.
Require Import Log Log.RepImplications Specs LogCache LoggedDiskLayer LogCacheToLoggedDisk.Definitions.
Require Import ClassicalFacts FunctionalExtensionality Lia Eqdep.

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
    |[H : exec_with_recovery ?u ?x ?y ?z ?a ?b ?c _,
      H0 : exec_with_recovery ?u ?x ?y ?z ?a ?b ?c _ |- _ ] =>
     eapply exec_with_recovery_deterministic_wrt_reboot_state in H; [| apply H0]
    | [ H: exec ?u ?x ?y ?z ?a _,
        H0: exec ?u ?x ?y ?z ?a _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec' ?u ?x ?y ?z _,
        H0: exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec _ ?u ?x ?y ?z _,
        H0: LayerImplementation.exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    end.
  
  Lemma recovery_oracles_refine_length:
    forall O_imp O_abs (L_imp: Layer O_imp) (L_abs: Layer O_abs) (ref: Refinement L_imp L_abs)
      l_o_imp l_o_abs T (u: user) s (p1: L_abs.(prog) T) rec l_rf u, 
      recovery_oracles_refine ref u s p1 rec l_rf l_o_imp l_o_abs ->
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
      abstract_oracles_exist_wrt refinement refines_reboot u (|Recover|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto.
      left.
      eexists; intuition eauto.
      destruct t.
      eexists; intuition eauto.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.
      eapply_fresh recover_finished in H8; eauto.
    }
    { 
      eapply IHl_selector in H12; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x0); simpl.
      repeat split; eauto; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_length in H0; eauto.
      right.
      eexists; repeat split; eauto.
      eexists; repeat split; eauto.
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
      abstract_oracles_exist_wrt refinement refines u (|Recover|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto.
      destruct t.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      unfold refines, cached_log_reboot_rep in *; cleanup.
      left.
      eexists; intuition eauto.
      eapply recover_finished in H7; eauto.
    }
    {
      unfold refines, cached_log_rep in *.
      cleanup.
      eapply log_rep_to_reboot_rep_same in H0.
              
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
      repeat split; eauto;
      intros; simpl in *; try unify_execs; cleanup.
      eapply recovery_oracles_refine_length in H1; eauto.
      right.
      eexists; repeat split; eauto.
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
      eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
      eexists; intuition eauto;
      match goal with
      |[H: select_total_mem _ _ _ = _ |- _ ]=>
       eapply select_total_mem_synced in H
      end; eauto.
    }
  Qed.

  Theorem abstract_oracles_exist_wrt_read:
    forall l_selector a u, 
      abstract_oracles_exist_wrt refinement refines u (|Read a|) (|Recover|) (cached_disk_reboot_list l_selector).
  Proof.
    unfold abstract_oracles_exist_wrt, refines_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto; simpl in *; try unify_execs; cleanup.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.

      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply_fresh read_finished in H7; eauto; cleanup.
      cleanup; eauto.
    }
    {
      unfold refines, cached_log_rep in *.
      cleanup.
      eapply_fresh log_rep_to_reboot_rep_same in H0.
              
      eapply abstract_oracles_exist_wrt_recover in H11; eauto; cleanup.
      exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x); simpl.
      repeat split; eauto; intros; simpl in *; try (unify_execs; cleanup).
      eapply recovery_oracles_refine_length in H1; eauto.

      right; eexists; intuition eauto.      
      eexists; intuition eauto.  
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
  
  Fixpoint non_colliding_selector_rec {T}
u (R: state CachedDiskLang -> T -> Prop) 
l_selector (rec: prog CachedDiskLang unit) l_o s1 :=
  match l_selector with
  | nil => True
  | selector :: ls =>
    match l_o with
    | nil => True
    | o::lo =>
    forall s1', 
    (exists s2, R s1 s2) ->
    exec CachedDiskLang u o s1 rec (Crashed s1') ->
    non_colliding_selector selector (snd s1') /\
    non_colliding_selector_rec u R ls rec lo 
    (empty_mem, (fst (snd s1'), 
    select_total_mem selector (snd (snd s1'))))
    end
  end.

Definition non_colliding_selector_list {T T'}
u (R: state CachedDiskLang -> T -> Prop) 
(Rc: state CachedDiskLang -> T -> Prop) 
l_selector 
(p: prog CachedDiskLang T') 
(rec: prog CachedDiskLang unit) l_o s1 :=
match l_selector with
  | nil => True
  | selector :: ls =>
    match l_o with
    | nil => True
    | o::lo =>
    forall s1', 
    (exists s2, R s1 s2) ->
    exec CachedDiskLang u o s1 p (Crashed s1') ->
    non_colliding_selector selector (snd s1') /\
    non_colliding_selector_rec u Rc ls rec lo 
    (empty_mem, (fst (snd s1'), 
    select_total_mem selector (snd (snd s1'))))
    end
  end.


  Theorem abstract_oracles_exist_wrt_write:
    forall l_selector l_a l_v u l_o s1 s1',
      
    non_colliding_selector_list
    u refines refines_reboot l_selector
    (refinement.(Simulation.Definitions.compile) (|Write l_a l_v|)) 
    (refinement.(Simulation.Definitions.compile) (|Recover|))  
      l_o s1 ->

      abstract_oracles_exist_wrt_explicit refinement refines u 
      (|Write l_a l_v|) (|Recover|) (cached_disk_reboot_list l_selector)
      l_o s1 s1'.
  Proof. 
    unfold abstract_oracles_exist_wrt_explicit, refines_reboot; induction l_selector;
    simpl; intros; cleanup; invert_exec.
    {
      exists  [ [OpToken (LoggedDiskOperation log_length data_length) Cont] ]; simpl.
      intuition eauto; try unify_execs; cleanup.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eexists; intuition eauto.
      left.
      eexists; intuition eauto.
      eexists; intuition eauto.
      eapply_fresh write_finished in H8; eauto.
      unfold refines, cached_log_rep in *;
      cleanup; eauto.
      split_ors; cleanup.
      {
        clear H5.
        left; eexists; intuition eauto.
        rewrite <- H9.
        setoid_rewrite H0 in H2.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eexists; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
      }
      {
        right; eexists; intuition eauto.
        rewrite <- H12.
        setoid_rewrite H0 in H2.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eexists; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
      }
    }
    {
      unfold refines, cached_log_rep in *.
      cleanup.
      unfold log_rep in *; cleanup.
      eapply_fresh write_crashed_oracle in H11; eauto.
              
      eapply abstract_oracles_exist_wrt_recover in H13; eauto; cleanup.
      repeat split_ors.
      cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto.
        eexists; repeat split; eauto.
        right.
        eexists; left.
        repeat split; eauto.
        unfold cached_log_rep in H4; cleanup.
        left.
        unfold cached_log_rep in *; simpl in *; cleanup.
        repeat split; eauto.
        eexists; repeat split; eauto.
        rewrite <- H12.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eexists; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        eexists; eauto.
        {
          unfold log_header_rep, log_rep_general, 
          log_rep_explicit, log_header_block_rep in *; cleanup.
          eauto.
        }
      }
      unfold cached_log_crash_rep in *; cleanup.
      split_ors; cleanup.
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        right.
        eexists; right; repeat split; eauto.
        right.
        unfold cached_log_crash_rep; simpl.
        repeat split; eauto.
        unfold cached_log_rep in *; cleanup.
        left; eexists; repeat split; eauto.
        eexists; repeat split; eauto.
        setoid_rewrite H0 in H13.
        setoid_rewrite <- H9.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.

        {
          unfold log_header_rep, log_rep_general, 
          log_rep_explicit, log_header_block_rep in *; cleanup.
          eauto.
        }
        (*
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
        *)
      }
      {
        eapply_fresh crash_rep_header_write_to_reboot_rep' in H4.
        split_ors.
        {
          exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
          repeat split; eauto; intros; try unify_execs; cleanup.
          eapply recovery_oracles_refine_length in H2; eauto.
          right.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          right.
          eexists; right; repeat split; eauto.
          right.
          unfold cached_log_crash_rep; simpl.
          repeat split; eauto.
          unfold cached_log_rep in *; cleanup.
          right; do 2 eexists; repeat split; eauto;
          repeat rewrite <- sync_list_upd_batch_set in *.
          setoid_rewrite <- H12.
          setoid_rewrite <- H13.
          setoid_rewrite H0 in H19.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.

          setoid_rewrite <- H13.
          setoid_rewrite H0 in H19.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.

          {
            unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
            intuition eauto.
          }

          unfold cached_log_rep in *; cleanup.
          left; repeat split; eauto.
          unfold cached_log_reboot_rep_explicit_part.
          do 2 eexists; repeat split; eauto.
          simpl; eexists; repeat split; eauto.

          unfold log_rep, log_header_rep,
          log_reboot_rep_explicit_part, log_rep_general in *.
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
          setoid_rewrite H0 in H19.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.

          all: try apply sumbool_agree_addr_dec.
          all: try solve [eapply log_rep_forall2_txns_length_match; unfold log_rep, log_rep_general; eauto].
          intros; apply H14; lia.
          unfold select_total_mem.
          setoid_rewrite H9; simpl.
          unfold select_for_addr; cleanup; eauto.
          erewrite addr_list_to_blocks_length_eq; eauto.
          rewrite map_length; eauto.
        }
        split_ors; cleanup.
        {
          exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
          repeat split; eauto; intros; try unify_execs; cleanup.
          eapply recovery_oracles_refine_length in H2; eauto.
          right.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          right.
          eexists; right; repeat split; eauto.
          right.
          unfold cached_log_crash_rep; simpl.
          repeat split; eauto.
          unfold cached_log_rep in *; cleanup.
          right; do 2 eexists; repeat split; eauto;
          repeat rewrite <- sync_list_upd_batch_set in *.
          setoid_rewrite <- H12.
          setoid_rewrite <- H13.
          setoid_rewrite H0 in H22.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.

          setoid_rewrite <- H13.
          setoid_rewrite H0 in H22.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.

          {
            unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
            intuition eauto.
          }

          unfold cached_log_rep in *; cleanup.
          right; left; repeat split; eauto.
          unfold cached_log_reboot_rep_explicit_part.
          do 2 eexists; repeat split; eauto.
          simpl; eexists; repeat split; eauto.

          unfold log_rep, log_header_rep,
          log_reboot_rep_explicit_part, log_rep_general in *.
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
          setoid_rewrite H0 in H22.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.

          all: try apply sumbool_agree_addr_dec.
          all: try solve [eapply log_rep_forall2_txns_length_match; unfold log_rep, log_rep_general; eauto].
          intros; apply H14; lia.
          {
            split_ors; cleanup.
            {
              unfold log_header_rep, log_rep_general, 
              log_rep_explicit, log_header_block_rep in *; cleanup.
              left; intuition eauto.
              exists (x6 - count (current_part (decode_header (fst (snd (snd s1) hdr_block_num))))).

              unfold log_crash_rep, 
              log_reboot_rep_explicit_part, 
              log_rep_explicit, log_header_block_rep in *; logic_clean.
              simpl in *; rewrite H41 in H9; inversion H9.
              subst.
              repeat rewrite encode_decode_header in *.
              rewrite H4 in *.

              unfold log_reboot_rep_explicit_part,
              log_rep_explicit, log_rep_inner,
              header_part_is_valid, txns_valid in *; 
              simpl in *; logic_clean.

              repeat match goal with 
              |[H: count (_ _) = _|- _] =>
                rewrite H in *
              end.

              repeat match goal with 
              |[H: map _ _ = records (_ _)|- _] =>
                rewrite <- H in *
              end.
              repeat rewrite map_map in *. 
              repeat rewrite map_app in *; simpl in *.
              rewrite fold_left_app in H19; simpl in *.

              match goal with 
              |[H: Forall _ (_ ++ [_]) |- _] =>
                eapply forall_app_l in H;
                inversion H; subst
              end.
              unfold txn_well_formed in *; logic_clean.
              match goal with 
              |[H: addr_count _ = _,
                H0: data_count _ = _,
                H1: addr_blocks _ = _ |- _] =>
                rewrite H, H0, H1 in *
              end.
              erewrite addr_list_to_blocks_length_eq in H19.
              2: apply map_length.

              repeat rewrite <- PeanoNat.Nat.add_assoc.
              repeat rewrite Minus.le_plus_minus_r by lia.
              unfold select_total_mem in *; simpl in *.
              repeat split; eauto.
              lia.
              intros Hx.
              apply H21.
              rewrite Hx.
              edestruct H25; eauto.
              instantiate (1:= x6 -
              fold_left PeanoNat.Nat.add
          (map (fun x : txn => addr_count (record x) + data_count (record x))
             x2) 0).
              lia.
              repeat rewrite <- PeanoNat.Nat.add_assoc in *.
              repeat rewrite Minus.le_plus_minus_r in * by lia.
              eauto.
            }
            {
              unfold log_header_rep, log_rep_general, 
              log_rep_explicit, log_header_block_rep in *; cleanup.
              right; intuition eauto.
              exists x6.

              unfold log_crash_rep, 
              log_reboot_rep_explicit_part, 
              log_rep_explicit, log_header_block_rep in *; logic_clean.
              simpl in *; rewrite H41 in H9; inversion H9.
              subst.
              repeat rewrite encode_decode_header in *.
              rewrite H4 in *.

              unfold log_reboot_rep_explicit_part,
              log_rep_explicit, log_rep_inner,
              header_part_is_valid, txns_valid in *; 
              simpl in *; logic_clean.

              repeat match goal with 
              |[H: count (_ _) = _|- _] =>
                rewrite H in *
              end.

              rewrite <- H64, <- H70 in *; simpl in *.

              match goal with 
              |[H: Forall _ [_] |- _] =>
                inversion H; subst
              end.
              unfold txn_well_formed in *; logic_clean.
              match goal with 
              |[H: addr_count _ = _,
                H0: data_count _ = _,
                H1: addr_blocks _ = _ |- _] =>
                rewrite H, H0, H1 in *
              end.
              erewrite addr_list_to_blocks_length_eq in H19.
              2: apply map_length.

              repeat rewrite <- PeanoNat.Nat.add_assoc.
              repeat rewrite Minus.le_plus_minus_r by lia.
              unfold select_total_mem in *; simpl in *.
              repeat split; eauto.
              intros Hx.
              apply H21.
              rewrite Hx.
              edestruct H25; eauto.
            }
          }
          erewrite addr_list_to_blocks_length_eq; eauto.
          rewrite map_length; eauto.
        }
        {
          exists ([OpToken (LoggedDiskOperation log_length data_length) CrashAfter]::x1); simpl.
          repeat split; eauto; intros; try unify_execs; cleanup.
          eapply recovery_oracles_refine_length in H2; eauto.
          right.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          eexists; repeat split; eauto; try unify_execs; cleanup.
          right.
          eexists; right; repeat split; eauto.
          right.
          unfold cached_log_crash_rep; simpl.
          repeat split; eauto.
          unfold cached_log_rep in *; cleanup.
          right; do 2 eexists; repeat split; eauto;
          
          repeat rewrite <- sync_list_upd_batch_set in *.
          setoid_rewrite <- H12.
          setoid_rewrite <- H13.
          setoid_rewrite H0 in H20.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.

          setoid_rewrite <- H13.
          setoid_rewrite H0 in H20.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          {
            unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
            intuition eauto.
          }

          unfold cached_log_rep in *; cleanup.
          right; right; repeat split; eauto.
          unfold cached_log_reboot_rep_explicit_part.
          do 2 eexists; repeat split; eauto.
          simpl; eexists; repeat split; eauto.

          unfold log_rep, log_header_rep,
          log_reboot_rep_explicit_part, log_rep_general in *.
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
          setoid_rewrite <- H12; eauto.
          setoid_rewrite <- H13; eauto.
          setoid_rewrite H0 in H20.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.

          all: try apply sumbool_agree_addr_dec.
          all: try solve [eapply log_rep_forall2_txns_length_match; unfold log_rep, log_rep_general; eauto].
          intros; apply H14; lia.
          {
            unfold select_total_mem in *.
            setoid_rewrite H9.
            rewrite select_for_addr_not_1_latest; simpl; eauto.
          }
          {
            split_ors; cleanup.
            {
              unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
              left; intuition eauto.
              edestruct H23; eauto.
              erewrite <- H17.
              setoid_rewrite <- H19; fold Nat.add; try lia.
              unfold select_total_mem; simpl; eauto.

              unfold log_crash_rep, 
              log_reboot_rep_explicit_part, 
              log_rep_explicit, log_header_block_rep in *; logic_clean.
              simpl in *; rewrite H42 in H9; inversion H9.
              subst.
              repeat rewrite encode_decode_header in *.
              rewrite H4.

              unfold log_reboot_rep_explicit_part,
              log_rep_explicit, log_rep_inner,
              header_part_is_valid, txns_valid in *; 
              simpl in *; logic_clean.

              repeat match goal with 
              |[H: count (_ _) = _|- _] =>
                setoid_rewrite H
              end.

              repeat match goal with 
              |[H: map _ _ = records (_ _)|- _] =>
                setoid_rewrite <- H
              end.
              repeat rewrite map_map in *. 
              repeat rewrite map_app in *; simpl.
              setoid_rewrite fold_left_app; simpl.

              match goal with 
              |[H: Forall _ (_ ++ [_]) |- _] =>
                eapply forall_app_l in H;
                inversion H; subst
              end.
              unfold txn_well_formed in *; logic_clean.
              match goal with 
              |[H: addr_count _ = _,
                H0: data_count _ = _,
                H1: addr_blocks _ = _ |- _] =>
                rewrite H, H0, H1
              end.
              erewrite addr_list_to_blocks_length_eq.
              2: apply map_length.
              lia.
            }
            {
              unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
              right; intuition eauto.
              edestruct H23; eauto.
              erewrite <- H21.
              setoid_rewrite <- H19; fold Nat.add; try lia.
              unfold select_total_mem; simpl; eauto.

              unfold log_crash_rep, 
              log_reboot_rep_explicit_part, 
              log_rep_explicit, log_header_block_rep in *; logic_clean.
              simpl in *; rewrite H42 in H9; inversion H9.
              subst.
              repeat rewrite encode_decode_header in *.

              unfold log_reboot_rep_explicit_part,
              log_rep_explicit, log_rep_inner,
              header_part_is_valid, txns_valid in *; 
              simpl in *; logic_clean.

              repeat match goal with 
              |[H: count (_ _) = _|- _] =>
                setoid_rewrite H
              end.

              rewrite <- H59.
              simpl.

              match goal with 
              |[H: Forall _ [_] |- _] =>
                inversion H; subst
              end.
              unfold txn_well_formed in *; logic_clean.
              match goal with 
              |[H: addr_count _ = _,
                H0: data_count _ = _,
                H1: addr_blocks _ = _ |- _] =>
                rewrite H, H0, H1
              end.
              erewrite addr_list_to_blocks_length_eq.
              2: apply map_length.
              lia.


              unfold log_crash_rep, 
              log_reboot_rep_explicit_part, 
              log_rep_explicit, log_header_block_rep in *; logic_clean.
              simpl in *; rewrite H42 in H9; inversion H9.
              subst.
              repeat rewrite encode_decode_header in *.
              rewrite H4.

              unfold log_reboot_rep_explicit_part,
              log_rep_explicit, log_rep_inner,
              header_part_is_valid, txns_valid in *; 
              simpl in *; logic_clean.

              repeat match goal with 
              |[H: count (_ _) = _|- _] =>
                setoid_rewrite H
              end.

              rewrite <- H71.
              simpl; lia.
            }
          }
          erewrite addr_list_to_blocks_length_eq; eauto.
          rewrite map_length; eauto.
        }
        {
          edestruct H; eauto.
          do 2 eexists; intuition eauto.
        }
        all: eauto.
      }
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashAfter]::x1); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        eexists; repeat split; eauto; try unify_execs; cleanup.        
        right.
        eexists; right; repeat split; eauto.
        left.
        unfold cached_log_crash_rep in *; simpl; cleanup.
        repeat split; eauto.
        unfold cached_log_rep in *; cleanup.
        eexists; repeat split; eauto.
        repeat rewrite <- sync_list_upd_batch_set in *.
        setoid_rewrite <- H10.
        setoid_rewrite H0 in e.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.
        erewrite addr_list_to_blocks_length_eq; eauto.
        rewrite map_length; eauto.
        {
            unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
            intuition eauto.
        }
      }
      split_ors; cleanup.
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        eexists; repeat split; eauto.
        right.
        eexists; left; repeat split; eauto.
        {
          
          unfold cached_log_rep in *; cleanup.
          right; left; eauto.
          unfold cached_log_crash_rep in *;
          simpl in *; cleanup.
          repeat split; eauto.
          eexists; repeat split; eauto.
          cleanup.
          setoid_rewrite <- H13.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          eapply log_rep_forall2_txns_length_match; eauto.
          unfold log_rep; eauto.
          {
              unfold log_header_rep, log_rep_general, 
              log_rep_explicit, log_header_block_rep in *; cleanup.
              eauto.
          }

          {
              unfold log_header_rep, log_rep_general, 
              log_rep_explicit, log_header_block_rep in *; cleanup.
              eauto.
          }
        }
      }
      {
        exists ([OpToken (LoggedDiskOperation log_length data_length) CrashBefore]::x1); simpl.
        repeat split; eauto; intros; try unify_execs; cleanup.
        eapply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        eexists; repeat split; eauto.
        right.
        eexists; left; intuition eauto.
        unfold cached_log_rep in H12; cleanup.
        right; right; eauto.
        unfold cached_log_crash_rep in *;
        simpl in *; cleanup.
        eexists; intuition eauto.
        setoid_rewrite <- H12.
        repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        erewrite empty_mem_list_upd_batch_eq_list_upd_batch_total; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.
        eapply log_rep_forall2_txns_length_match; eauto.
        unfold log_rep; eauto.
        {
          unfold log_header_rep, log_rep_general, 
          log_rep_explicit, log_header_block_rep in *; cleanup.
          eauto.
        }
        unfold log_header_rep, log_rep_general, 
            log_rep_explicit, log_header_block_rep in *; cleanup.
        erewrite addr_list_to_blocks_length_eq; eauto.
      }
      {
        repeat split_ors.
        {
          unfold cached_log_rep in *; cleanup; eauto;
          try eapply log_rep_to_reboot_rep in H5;
          eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
          eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
        }
        {
          unfold cached_log_crash_rep in *; cleanup; eauto.
          split_ors; cleanup.
          split_ors; cleanup.
          {
            eapply crash_rep_log_write_to_reboot_rep in H2.
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
            eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
          }
          {
            eapply crash_rep_header_write_to_reboot_rep in H2.
            split_ors;
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
            eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
            edestruct H; eauto.
            do 2 eexists; intuition eauto.
          }
          split_ors; cleanup.
          {
            eapply log_rep_to_reboot_rep in H2.
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
            eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
          }
          split_ors; cleanup.
          {
            clear H10.
            split_ors.
            {
              cleanup.
            eapply crash_rep_apply_to_reboot_rep in H2.
            split_ors;
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
            eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
            }
                {
              eapply log_rep_to_reboot_rep in H2.
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
                eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
            }
          }
          {
            eapply log_rep_to_reboot_rep in H2.
            eexists; unfold refines_reboot, cached_log_reboot_rep; simpl;
            eexists; repeat split; eauto;
            eapply select_total_mem_synced; eauto.
          }
        }
      }
    }
Qed.

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
    
    (*
  Theorem abstract_oracles_exists_logged_disk:
    forall T (p_abs: abs.(prog) T) l_selector u l_o s1 s1',
      not_init p_abs ->
      (forall T p, 
      eq_dep _ _ T p _ (|Write l_a l_v|) ->
        non_colliding_selector_list
    u refines refines_reboot l_selector
    (refinement.(Simulation.Definitions.compile) p) 
    (refinement.(Simulation.Definitions.compile) (|Recover|))  
      l_o s1) ->
      abstract_oracles_exist_wrt_explicit refinement 
      refines u p_abs (|Recover|) 
      (cached_disk_reboot_list l_selector) l_o s1 s1'.
  Proof.
    unfold abstract_oracles_exist_wrt_explicit; induction p_abs;
    simpl; intros; cleanup_no_match.
    {(** OPS **)
      destruct o; intuition.
      eapply abstract_oracles_exist_wrt_read; eauto.
      eapply abstract_oracles_exist_wrt_write; eauto.
      eapply H0; eauto.
      eapply abstract_oracles_exist_wrt_recover'; eauto.
    }
    {
      repeat invert_exec; cleanup.
      {
        rewrite <- H3; simpl.
        exists [[Layer.Cont (LoggedDiskOperation log_length data_length)]]; simpl; intuition.
        left.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        eexists; repeat split; eauto; try unify_execs; cleanup.
      }
      {
        destruct l_selector; simpl in *; try congruence; cleanup.
        repeat invert_exec.
        invert_exec'' H10.
        eapply abstract_oracles_exist_wrt_recover in H12; eauto.
        cleanup.
        exists ([Layer.Crash (LoggedDiskOperation log_length data_length)]::x0);
        simpl; intuition eauto.
        apply recovery_oracles_refine_length in H2; eauto.
        right.
        eexists; repeat split; eauto; try unify_execs; cleanup.
        econstructor.
        left; eexists; intuition eauto.
        econstructor.
        unfold refines, cached_log_rep in *.
        cleanup.
        eapply log_rep_to_reboot_rep in H2.
        unfold refines_reboot, cached_log_reboot_rep.
        do 2 eexists; intuition eauto.
        eapply select_total_mem_synced in H3; eauto.
      }
    }
    {
      repeat invert_exec.
      {
        invert_exec'' H13.
        edestruct IHp_abs; eauto.
        instantiate (2:= []); simpl.
        eauto.
        eapply ExecFinished; eauto.
        edestruct H.
        eauto.
        {
          simpl in *.
          edestruct H1; eauto.
        }
        2: {
          instantiate (3:= []); simpl.
          eapply ExecFinished; eauto.
        }
        eapply exec_compiled_preserves_refinement_finished in H10; eauto.
        simpl in *; cleanup; try tauto.
        simpl in *.
        exists ([o0 ++ o]); split; eauto.
        repeat split_ors; cleanup;
        repeat unify_execs; cleanup.
        left.
        cleanup.
        do 2 eexists; repeat split; eauto.
        econstructor; eauto.
        right; simpl; repeat eexists; intuition eauto.
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
          exists ((o0 ++ o)::l); split; eauto.
          repeat split_ors; cleanup;
          repeat unify_execs; cleanup.  
          right.
          eexists; intuition eauto.
          econstructor; eauto.
          right; simpl; repeat eexists; intuition eauto.
        }
        {
          edestruct IHp_abs; eauto.
          instantiate (2:= t::l_selector); simpl.
          instantiate (1:= Recovered (extract_state_r ret)).
          econstructor; eauto.
          simpl in *; cleanup; try tauto.
          simpl in *.
          eexists (_::l); split; eauto.
          repeat split_ors;
            cleanup; repeat (unify_execs; cleanup).
            right.            
            eexists; intuition eauto.
            solve [econstructor; eauto].
        }
      }
    }
  Qed.
*)