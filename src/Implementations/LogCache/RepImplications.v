Require Import Lia Datatypes PeanoNat Compare_dec Framework TotalMem FSParameters Log Log.Specs.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer LogCache.
Require Import FunctionalExtensionality.

Lemma cached_log_reboot_rep_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_reboot_rep s_abs s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_reboot_rep; intros; cleanup.

eexists; intuition eauto.
eapply RepImplications.reboot_rep_to_reboot_rep; eauto.
simpl.
assert (A: map Log.addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map Log.addr_list x))). {
  repeat rewrite map_map.
  apply map_ext_in.
  intros.
  rewrite map_map.
  rewrite map_noop; eauto.
  intros.
  unfold Log.log_reboot_rep, Log.log_rep_general, Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; simpl in *; cleanup.
  eapply Forall_forall in H11; eauto.
  unfold Log.txn_well_formed in H11; simpl in *; logic_clean.
  eapply Forall_forall in H15; eauto; lia.
}
rewrite A at 2.
rewrite shift_list_upd_batch_set_comm.
rewrite shift_select_total_mem_synced; simpl; intuition eauto.
rewrite <- shift_list_upd_batch_set_comm.
rewrite map_map.
rewrite map_noop; eauto.
intros.
rewrite map_map.
rewrite map_noop; eauto.
intros.
apply in_map_iff in H0; logic_clean; subst.
unfold Log.log_reboot_rep, Log.log_rep_general, 
Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; 
simpl in *; logic_clean.
eapply Forall_forall in H11; eauto.
unfold Log.txn_well_formed in H11; simpl in *; logic_clean.
eapply Forall_forall in H16; eauto; lia.
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
{
  intros; apply H1; lia.
}
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
Qed.


Lemma cached_log_crash_rep_during_recovery_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_crash_rep (LogCache.During_Recovery s_abs) s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_crash_rep, LogCache.cached_log_reboot_rep; intros; cleanup.

eexists; intuition eauto.
eapply RepImplications.crash_rep_recover_to_reboot_rep; eauto.
simpl.
assert (A: map Log.addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map Log.addr_list x))). {
  repeat rewrite map_map.
  apply map_ext_in.
  intros.
  rewrite map_map.
  rewrite map_noop; eauto.
  intros.
  unfold Log.log_crash_rep, Log.log_rep_general, Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; simpl in *; cleanup.
  eapply Forall_forall in H12; eauto.
  unfold Log.txn_well_formed in H12; simpl in *; logic_clean.
  eapply Forall_forall in H17; eauto; lia.
}
rewrite A at 2.
rewrite shift_list_upd_batch_set_comm.
rewrite shift_select_total_mem_synced; simpl; intuition eauto.
rewrite <- shift_list_upd_batch_set_comm.
rewrite map_map.
rewrite map_noop; eauto.
intros.
rewrite map_map.
rewrite map_noop; eauto.
intros.
apply in_map_iff in H0; logic_clean; subst.
unfold Log.log_crash_rep, Log.log_rep_general, 
Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; 
simpl in *; logic_clean.
eapply Forall_forall in H12; eauto.
unfold Log.txn_well_formed in H12; simpl in *; logic_clean.
eapply Forall_forall in H17; eauto; lia.
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
{
  intros; apply H1; lia.
}
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
Qed.

Lemma cached_log_crash_rep_after_commit_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_crash_rep (LogCache.After_Commit s_abs) s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_crash_rep, LogCache.cached_log_reboot_rep; intros; cleanup.

eexists; intuition eauto.
eapply RepImplications.log_rep_to_reboot_rep; eauto.
simpl.
assert (A: map Log.addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map Log.addr_list x))). {
  repeat rewrite map_map.
  apply map_ext_in.
  intros.
  rewrite map_map.
  rewrite map_noop; eauto.
  intros.
  unfold Log.log_rep, Log.log_rep_general, Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; simpl in *; cleanup.
  eapply Forall_forall in H10; eauto.
  unfold Log.txn_well_formed in H10; simpl in *; logic_clean.
  eapply Forall_forall in H14; eauto; lia.
}
rewrite A at 2.
rewrite shift_list_upd_batch_set_comm.
rewrite shift_select_total_mem_synced; simpl; intuition eauto.
rewrite <- shift_list_upd_batch_set_comm.
rewrite map_map.
rewrite map_noop; eauto.
intros.
rewrite map_map.
rewrite map_noop; eauto.
intros.
apply in_map_iff in H0; logic_clean; subst.
unfold Log.log_rep, Log.log_rep_general, 
Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; 
simpl in *; logic_clean.
eapply Forall_forall in H10; eauto.
unfold Log.txn_well_formed in H10; simpl in *; logic_clean.
eapply Forall_forall in H15; eauto; lia.
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
{
  intros; apply H1; lia.
}
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
Qed.

Lemma cached_log_rep_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_rep s_abs s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_rep, LogCache.cached_log_reboot_rep; intros; cleanup.

eexists; intuition eauto.
eapply RepImplications.log_rep_to_reboot_rep; eauto.
simpl.
assert (A: map Log.addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map Log.addr_list x))). {
  repeat rewrite map_map.
  apply map_ext_in.
  intros.
  rewrite map_map.
  rewrite map_noop; eauto.
  intros.
  unfold Log.log_rep, Log.log_rep_general, Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; simpl in *; cleanup.
  eapply Forall_forall in H11; eauto.
  unfold Log.txn_well_formed in H11; simpl in *; logic_clean.
  eapply Forall_forall in H15; eauto; lia.
}
rewrite A at 2.
rewrite shift_list_upd_batch_set_comm.
rewrite shift_select_total_mem_synced; simpl; intuition eauto.
rewrite <- shift_list_upd_batch_set_comm.
rewrite map_map.
rewrite map_noop; eauto.
intros.
rewrite map_map.
rewrite map_noop; eauto.
intros.
apply in_map_iff in H1; logic_clean; subst.
unfold Log.log_rep, Log.log_rep_general, 
Log.log_rep_explicit, Log.log_rep_inner, Log.txns_valid in *; 
simpl in *; logic_clean.
eapply Forall_forall in H11; eauto.
unfold Log.txn_well_formed in H11; simpl in *; logic_clean.
eapply Forall_forall in H16; eauto; lia.
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
{
  intros; apply H2; lia.
}
{
  unfold sumbool_agree; intros; intuition eauto.
  destruct (addr_dec x0 y); subst.
  destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
  destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
}
Qed.

Lemma cached_log_crash_rep_during_apply_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_crash_rep (LogCache.During_Apply s_abs) s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_crash_rep, 
LogCache.cached_log_reboot_rep; intros; cleanup.

simpl; split_ors.
{
  cleanup.
  eapply RepImplications.crash_rep_apply_to_reboot_rep in H; eauto.
  split_ors.
  {
    eexists; intuition eauto.
    {
      unfold Log.log_reboot_rep, Log.log_rep_general in *.
      logic_clean.
      repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        extensionality index.
        unfold shift; simpl.
        destruct (list_list_in_EXM addr_dec (map Log.addr_list x) (data_start + index)); 
        try logic_clean.
        eapply list_upd_batch_in; eauto.
        eexists; split; eauto.
        apply in_seln; eauto.

        apply forall_forall2.
        apply Forall_forall; intros.
        rewrite <- combine_map in H7.
        apply in_map_iff in H7; logic_clean.
        unfold Log.log_rep_explicit, Log.log_rep_inner,
        Log.txns_valid in *; logic_clean.
        eapply Forall_forall in H16; eauto.
        unfold Log.txn_well_formed in H16; logic_clean; eauto.
        destruct x5; simpl in *.
        inversion H7; subst.
        rewrite H19, <- H23, firstn_length_l; eauto. 
        repeat rewrite map_length; eauto.
        
        repeat rewrite list_upd_batch_not_in; eauto.
        unfold total_mem_map, select_total_mem.
        rewrite select_for_addr_synced; simpl; eauto.
        eapply H1; eauto.
        lia.
        intros; cleanup.
        eapply H4; eauto.
        }
  }
  {
    eexists; intuition eauto; simpl.
    {
      setoid_rewrite H0.
    repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        extensionality index.
        unfold shift; simpl.

        unfold total_mem_map, select_total_mem.
        rewrite select_for_addr_synced; simpl; eauto.
        eapply H2; eauto.
        lia.
      }
  }
}
{
  eexists; intuition eauto; simpl.
  eapply RepImplications.log_rep_to_reboot_rep; eauto.
  unfold Log.log_rep, Log.log_rep_general in *.
  logic_clean.
  repeat rewrite total_mem_map_shift_comm.
    repeat rewrite total_mem_map_fst_list_upd_batch_set.
    extensionality index.
    unfold shift; simpl.
    destruct (list_list_in_EXM addr_dec (map Log.addr_list x) (data_start + index)); 
    try logic_clean.
    eapply list_upd_batch_in; eauto.
    eexists; split; eauto.
    apply in_seln; eauto.

    apply forall_forall2.
    apply Forall_forall; intros.
    rewrite <- combine_map in H4.
    apply in_map_iff in H4; logic_clean.
    unfold Log.log_rep_explicit, Log.log_rep_inner,
    Log.txns_valid in *; logic_clean.
    eapply Forall_forall in H13; eauto.
    unfold Log.txn_well_formed in H13; logic_clean; eauto.
    destruct x4; simpl in *.
    inversion H4; subst.
    rewrite H16, <- H20, firstn_length_l; eauto. 
    repeat rewrite map_length; eauto.
    
    repeat rewrite list_upd_batch_not_in; eauto.
    unfold total_mem_map, select_total_mem.
    rewrite select_for_addr_synced; simpl; eauto.
    eapply H1; eauto.
    lia.
    intros; cleanup.
    eapply H0; eauto.
  }
Qed.

Lemma cached_log_crash_rep_during_commit_to_reboot_rep:
forall s_abs1 s_abs2 s_imp a,
LogCache.cached_log_crash_rep (LogCache.During_Commit s_abs1 s_abs2) s_imp ->
non_colliding_selector a (snd s_imp) ->
LogCache.cached_log_reboot_rep s_abs1
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))) \/
LogCache.cached_log_reboot_rep s_abs2
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_crash_rep, LogCache.cached_log_reboot_rep; intros; cleanup.
split_ors; cleanup.
{
left; eexists; intuition eauto.
eapply RepImplications.crash_rep_log_write_to_reboot_rep; eauto.
simpl.
{
      unfold Log.log_crash_rep, Log.log_rep_general in *.
      logic_clean.
      repeat rewrite total_mem_map_shift_comm.
        repeat rewrite total_mem_map_fst_list_upd_batch_set.
        extensionality index.
        unfold shift; simpl.
        destruct (list_list_in_EXM addr_dec (map Log.addr_list x) (data_start + index)); 
        try logic_clean.
        eapply list_upd_batch_in; eauto.
        eexists; split; eauto.
        apply in_seln; eauto.

        apply forall_forall2.
        apply Forall_forall; intros.
        rewrite <- combine_map in H12.
        apply in_map_iff in H12; logic_clean.
        unfold Log.log_rep_explicit, Log.log_rep_inner,
        Log.txns_valid in *; logic_clean.
        eapply Forall_forall in H15; eauto.
        unfold Log.txn_well_formed in H15; logic_clean; eauto.
        destruct x4; simpl in *.
        inversion H12; subst.
        rewrite H18, <- H22, firstn_length_l; eauto. 
        repeat rewrite map_length; eauto.
        
        repeat rewrite list_upd_batch_not_in; eauto.
        unfold total_mem_map, select_total_mem.
        rewrite select_for_addr_synced; simpl; eauto.
        eapply H2; eauto.
        lia.
      }
}
{
  eapply RepImplications.crash_rep_header_write_to_reboot_rep in H.
  split_ors. 
  {
    left; eexists; intuition eauto; simpl.
    unfold Log.log_reboot_rep, Log.log_rep_general in *.
    logic_clean.
    repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      extensionality index.
      unfold shift; simpl.
      destruct (list_list_in_EXM addr_dec (map Log.addr_list x) (data_start + index)); 
      try logic_clean.
      eapply list_upd_batch_in; eauto.
      eexists; split; eauto.
      apply in_seln; eauto.

      apply forall_forall2.
      apply Forall_forall; intros.
      rewrite <- combine_map in H6.
      apply in_map_iff in H6; logic_clean.
      unfold Log.log_rep_explicit, Log.log_rep_inner,
      Log.txns_valid in *; logic_clean.
      eapply Forall_forall in H15; eauto.
      unfold Log.txn_well_formed in H15; logic_clean; eauto.
      destruct x6; simpl in *.
      inversion H6; subst.
      rewrite H18, <- H22, firstn_length_l; eauto. 
      repeat rewrite map_length; eauto.
      
      repeat rewrite list_upd_batch_not_in; eauto.
      unfold total_mem_map, select_total_mem.
      rewrite select_for_addr_synced; simpl; eauto.
      eapply H3; eauto.
      lia.
    }
    {
    right; eexists; intuition eauto; simpl.
    unfold Log.log_reboot_rep, Log.log_rep_general in *.
    logic_clean.
    repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      extensionality index.
      unfold shift; simpl.
      destruct (list_list_in_EXM addr_dec (map Log.addr_list x0) (data_start + index)); 
      try logic_clean.
      eapply list_upd_batch_in; eauto.
      eexists; split; eauto.
      apply in_seln; eauto.

      apply forall_forall2.
      apply Forall_forall; intros.
      rewrite <- combine_map in H6.
      apply in_map_iff in H6; logic_clean.
      unfold Log.log_rep_explicit, Log.log_rep_inner,
      Log.txns_valid in *; logic_clean.
      eapply Forall_forall in H15; eauto.
      unfold Log.txn_well_formed in H15; logic_clean; eauto.
      destruct x6; simpl in *.
      inversion H6; subst.
      rewrite H18, <- H22, firstn_length_l; eauto. 
      repeat rewrite map_length; eauto.
      
      repeat rewrite list_upd_batch_not_in; eauto.
      unfold total_mem_map, select_total_mem.
      rewrite select_for_addr_synced; simpl; eauto.
      eapply H3; eauto.
      lia.
    }
    eauto.
}
Qed.


Lemma cached_log_crash_rep_after_apply_to_reboot_rep:
forall s_abs s_imp a,
LogCache.cached_log_crash_rep (LogCache.After_Apply s_abs) s_imp ->
LogCache.cached_log_reboot_rep s_abs
(empty_mem, (fst (snd s_imp), select_total_mem a (snd (snd s_imp)))).
Proof.
unfold LogCache.cached_log_crash_rep, LogCache.cached_log_reboot_rep; intros; cleanup.

eexists; intuition eauto.
eapply RepImplications.log_rep_to_reboot_rep; eauto.
simpl.
repeat rewrite total_mem_map_shift_comm.
    repeat rewrite total_mem_map_fst_list_upd_batch_set.
    extensionality index.
    unfold shift; simpl.
    unfold total_mem_map, select_total_mem.
    rewrite select_for_addr_synced; simpl; eauto.
    eapply H1; eauto.
    lia.
Qed.



Lemma cached_log_rep_to_reboot_rep_same:
forall s_abs s_imp,
LogCache.cached_log_rep s_abs s_imp ->
LogCache.cached_log_reboot_rep s_abs s_imp.
Proof.
unfold LogCache.cached_log_rep, LogCache.cached_log_reboot_rep; intros; cleanup.
eexists; intuition eauto.
eapply RepImplications.log_rep_to_reboot_rep_same; eauto.
Qed.