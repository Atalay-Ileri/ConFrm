Require Import Lia Datatypes PeanoNat Compare_dec Framework FSParameters Log.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer.

(** Cache uses disk addresses but its functions take data region addresses 
    and converts them to disk addresses to use *)
Local Fixpoint write_batch_to_cache al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |CDCO| Write a v;
    _ <- write_batch_to_cache al' vl';
    Ret tt            
  | _, _ => Ret tt
 end.

(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
  if (NoDup_dec addr_l) then
    if (Nat.eq_dec (length addr_l) (length data_l)) then
      if (le_dec (length addr_l + length data_l) log_length) then
           
           committed <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
           _ <-
           if committed then
             Ret tt
           else
             _ <- |CDDP| apply_log;
             _ <- |CDCO| (Flush _ _);
             _ <- |CDDP| commit (addr_list_to_blocks (map (plus data_start) addr_l)) data_l;
             Ret tt;
      
            write_batch_to_cache (map (plus data_start) addr_l) data_l
      else
        Ret tt
    else
      Ret tt
  else
    Ret tt.


(* Takes a data region_address *)
Definition read a :=
  mv <- |CDCO| Read _ (data_start + a);
  match mv with
  | Some v =>
    Ret v
  | None =>
    |CDDP| |DO| DiskLayer.Read (data_start + a)
  end.

Local Fixpoint write_lists_to_cache l_al_vl :=
  match l_al_vl with
  | nil =>
    Ret tt
  | al_vl :: l =>
    _ <- write_batch_to_cache (fst al_vl) (snd al_vl);
    write_lists_to_cache l
  end.

Definition recover :=
  log <- |CDDP| recover;
  write_lists_to_cache log.

(** Representation Invariants **)


Definition cached_log_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    fst s = list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
    log_rep txns (snd s) /\
    merged_disk = sync (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))).

Definition cached_log_crash_rep old_merged_disk new_merged_disk (s: Language.state CachedDiskLang) :=
  exists old_txns txns,
    log_crash_rep old_txns txns (snd s) /\
    new_merged_disk = shift (plus data_start) (list_upd_batch (snd (snd s)) (map addr_list txns)
                      (map (fun txn => map (fun vs => (vs, [])) (data_blocks txn)) txns)) /\
    old_merged_disk = shift (plus data_start) (list_upd_batch (snd (snd s)) (map addr_list old_txns)
                       (map (fun txn => map (fun vs => (vs, [])) (data_blocks txn)) old_txns)).

Definition cached_log_reboot_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    fst s = empty_mem /\
    log_reboot_rep txns (snd s) /\
    merged_disk = sync (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))).

Theorem write_batch_to_cache_finished:
  forall al vl o s s' t,
    length al = length vl ->
    exec CachedDiskLang o s (write_batch_to_cache al vl) (Finished s' t) ->
    snd s' = snd s /\
    fst s' = upd_batch (fst s) al vl.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia.
  repeat invert_exec.
  edestruct IHal; eauto.
Qed.


Set Nested Proofs Allowed.
Lemma shift_select_mem_comm:
  forall A AEQ V (m: @mem A AEQ (V * list V)) f selector,
    select_mem (shift f selector) (shift f m) = shift f (select_mem selector m).
Proof.
  intros; unfold select_mem, select_for_addr, shift; eauto.
Qed.

Lemma sync_shift_comm:
  forall A AEQ V (m: @mem A AEQ (V * list V)) f,
    sync (shift f m) = shift f (sync m).
Proof.
  unfold shift, sync; intros; simpl; eauto.
Qed.

Require Import FunctionalExtensionality.
Lemma select_mem_upd_comm:
  forall A AEQ V (a: A) (vs: V * list V) selector (m: @mem A AEQ _),
    snd vs = [] ->
    select_mem selector (upd m a vs) =
    upd (select_mem selector m) a vs.
Proof.
  intros; unfold select_mem, select_for_addr, upd; simpl; intros.
  destruct vs; simpl in *; subst.
  extensionality x.
  
  destruct (AEQ x a); subst; eauto.
  destruct (selector a); simpl; eauto.
  destruct n; eauto.
Qed.

Lemma select_mem_upd_batch_comm:
  forall A AEQ V (l_a: list A) (l_vs: list (V * list V)) selector (m: @mem A AEQ _),
    Forall (fun vs => snd vs = []) l_vs ->
    
    select_mem selector (upd_batch m l_a l_vs) =
    upd_batch (select_mem selector m) l_a l_vs.
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_vs; simpl in *; eauto.
  rewrite IHl_a; eauto.
  rewrite select_mem_upd_comm; eauto.
  all: inversion H; intuition eauto.
Qed.

Lemma select_mem_list_upd_batch_comm:
  forall A AEQ V (l_l_a: list (list A)) (l_l_vs: list (list (V * list V))) selector (m: @mem A AEQ _),
    Forall (fun l_vs => Forall (fun vs => snd vs = []) l_vs) l_l_vs ->
    select_mem selector (list_upd_batch m l_l_a l_l_vs) =
    list_upd_batch (select_mem selector m) l_l_a l_l_vs.
Proof.
  induction l_l_a; simpl in *; intros; eauto.
  destruct l_l_vs; eauto.
  erewrite IHl_l_a.
  rewrite select_mem_upd_batch_comm; eauto.
  all: inversion H; intuition eauto.
Qed.

Lemma sync_select_mem_noop:
  forall A AEQ V selector (m: @mem A AEQ (V * list V)),
    sync (select_mem selector m) = select_mem selector m.
Proof.
  unfold sync, select_mem; intros; simpl; eauto.
  extensionality a.
  destruct (m a); simpl; eauto.
Qed.

Lemma crash_to_reboot_rep:
  forall old new s selector,
    cached_log_crash_rep old new s ->

    (** Non-colliding selector **)
    (forall (old_log_blocksets : list (value * list value)) (new_log_blocks : list value),
       length old_log_blocksets = length new_log_blocks ->
       length old_log_blocksets <= log_length ->
       (forall i : nat, i < length old_log_blocksets -> snd (snd s) (log_start + i) = selNopt old_log_blocksets i) ->
       (forall i : nat,
          i < length new_log_blocks ->
          select_mem selector (snd (snd s)) (log_start + i) =
          selNopt (map (fun v : value => (v, [])) new_log_blocks) i) ->
       rolling_hash hash0 (map fst old_log_blocksets) = rolling_hash hash0 new_log_blocks ->
       map fst old_log_blocksets = new_log_blocks) ->
    
    cached_log_reboot_rep (select_mem (shift (Init.Nat.add data_start) selector) old) (empty_mem, (fst (snd s), select_mem selector (snd (snd s)))) \/
    cached_log_reboot_rep (select_mem (shift (Init.Nat.add data_start) selector) new) (empty_mem, (fst (snd s), select_mem selector (snd (snd s)))).
Proof.
  unfold cached_log_crash_rep, cached_log_reboot_rep; intros.
  cleanup.
  eapply crash_rep_to_reboot_rep in H; eauto.
  split_ors; cleanup.
  {
    left; eexists; simpl; intuition eauto.    
    rewrite shift_select_mem_comm.    
    rewrite sync_shift_comm.
    rewrite sync_list_upd_batch_set.
    repeat rewrite map_map.
    rewrite select_mem_list_upd_batch_comm; eauto.
    rewrite sync_select_mem_noop; eauto.
    
    apply Forall_forall; intros.
    apply in_map_iff in H1; cleanup; eauto.
    apply Forall_forall; intros.
    apply in_map_iff in H1; cleanup; eauto.
    
    intros.
    unfold log_reboot_rep, log_rep_explicit, log_rep_inner, txns_valid  in *; cleanup.
    apply in_map_iff in H1; cleanup_no_match.
    eapply Forall_forall in H11; eauto.
    unfold txn_well_formed in *; logic_clean; simpl in *; eauto.
  }
  {
   right; eexists; simpl; intuition eauto.    
   rewrite shift_select_mem_comm.    
   rewrite sync_shift_comm.
   rewrite sync_list_upd_batch_set.
   repeat rewrite map_map.
   rewrite select_mem_list_upd_batch_comm; eauto.
   rewrite sync_select_mem_noop; eauto.
   
   apply Forall_forall; intros.
   apply in_map_iff in H1; cleanup; eauto.
   apply Forall_forall; intros.
   apply in_map_iff in H1; cleanup; eauto.
   
   intros.
   unfold log_reboot_rep, log_rep_explicit, log_rep_inner, txns_valid  in *; cleanup.
   apply in_map_iff in H1; cleanup_no_match.
   eapply Forall_forall in H11; eauto.
   unfold txn_well_formed in *; logic_clean; simpl in *; eauto. 
  }
Qed.


(*
Global Opaque Log.commit.

Theorem write_finished:
  forall merged_disk s o al vl s' t,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang o s (write al vl) (Finished s' t) ->
  cached_log_rep merged_disk s' \/
  cached_log_rep (upd_batch_set merged_disk al vl) s'.
Proof.
  unfold write; simpl; intros.
  repeat (cleanup; invert_exec; cleanup); eauto.
  {
    unfold cached_log_rep, log_rep in *; cleanup.
    eapply commit_finished in H3; unfold log_header_rep; eauto.
    cleanup; simpl in *.
    eapply write_batch_to_cache_finished in H1; eauto; simpl in *; cleanup.
    split_ors; cleanup; try congruence.
    right.
    eexists; intuition eauto.
    all: simpl in *; eauto.
    unfold log_rep, log_rep_inner, txns_valid in *; cleanup; simpl in *.
    inversion H16; simpl in *; cleanup.
    unfold txn_well_formed in *; cleanup.
    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H36.
    rewrite firstn_app2; eauto.
    rewrite map_length; eauto.
    admit.
    rewrite map_length; eauto.
    admit.
    
    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    rewrite map_length; eauto.

    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    
    apply Forall_forall; intros.
    apply in_map_iff in H5; cleanup.
    lia.
    rewrite map_length; eauto.

    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    intros. apply in_map_iff in H5; cleanup.
    admit.
    rewrite map_length; eauto.
  }
  {
    unfold cached_log_rep, log_rep in *; cleanup.
    eapply commit_finished in H3; unfold log_header_rep; eauto.
    cleanup; simpl in *.
    eapply write_batch_to_cache_finished in H1; eauto; simpl in *; cleanup.
    split_ors; cleanup; try congruence.
    right.
    eexists; intuition eauto.
    all: simpl in *; eauto.
    admit.
    admit.
    rewrite map_length; eauto.
    admit.
    
    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    rewrite map_length; eauto.

    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    
    apply Forall_forall; intros.
    apply in_map_iff in H5; cleanup.
    lia.
    rewrite map_length; eauto.

    destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
    rewrite H4.
    rewrite firstn_app2; eauto.
    intros.
    apply in_map_iff in H5; cleanup.
    admit.
    rewrite map_length; eauto.
  }
Admitted.
  *)

