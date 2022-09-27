Require Import Lia Datatypes PeanoNat Compare_dec Framework TotalMem FSParameters Log Log.Specs.
Require Import DiskLayer CryptoDiskLayer CacheLayer CachedDiskLayer.
Require Import FunctionalExtensionality.

(** Cache uses disk addresses but its functions take data region addresses 
    and converts them to disk addresses to use *)
Local Fixpoint write_batch_to_cache al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |CDCO| Write a v;
    write_batch_to_cache al' vl'           
  | _, _ => Ret tt
 end.

Definition Forall_dec {A} (P: A -> Prop) (P_dec: forall a: A, {P a}+{~P a}):
  forall l: list A, {Forall P l}+{~Forall P l}.
induction l; simpl; eauto.  
destruct (P_dec a), IHl;
eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
- right; intros.
  intros Hx; inversion Hx; eauto.
Defined.

(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
    if (Forall_dec (fun a => a < data_length) (fun a => lt_dec a data_length) addr_l) then
      if (NoDup_dec addr_l) then
        if (Nat.eq_dec (length addr_l) (length data_l)) then
          if (le_dec (length (addr_list_to_blocks (map (plus data_start) addr_l)) + length data_l) log_length) then
          if (lt_dec 0 (length addr_l)) then
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
        Ret tt
    else
      Ret tt
  else
    Ret tt.


(* Takes a data region_address *)
Definition read a :=
  if lt_dec a data_length then
    mv <- |CDCO| Read _ (data_start + a);
    match mv with
    | Some v =>
      Ret v
    | None =>
      |CDDP| |DO| DiskLayer.Read (data_start + a)
    end
  else
    Ret value0.

Local Fixpoint write_lists_to_cache l_al_vl :=
  match l_al_vl with
  | nil =>
    Ret tt
  | al_vl :: l =>
    _ <- write_batch_to_cache (fst al_vl) (snd al_vl);
    write_lists_to_cache l
  end.

Definition recover :=
  _ <- |CDCO| (Flush _ _);
  log <- |CDDP| recover;
  write_lists_to_cache log.

(** Convert l_a to data adress **)
Definition init l_av :=
  let l_a := map fst l_av in
  let l_v := map snd l_av in
  _ <- |CDCO| (Flush _ _);
  |CDDP| init (combine (map (Nat.add data_start) l_a) l_v).

(** Representation Invariants **) 
Inductive Cached_Log_Crash_State:=
| During_Commit (old_merged_disk new_merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| After_Commit (new_merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| During_Apply (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| After_Apply (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State
| During_Recovery (merged_disk : @total_mem addr addr_dec value) : Cached_Log_Crash_State.

Definition cached_log_rep merged_disk (s: LayerImplementation.state CachedDiskLang) :=
  exists txns,
    fst s = Mem.list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
    log_rep txns (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []).

Definition cached_log_crash_rep cached_log_crash_state (s: LayerImplementation.state CachedDiskLang) :=
  match cached_log_crash_state with
  | During_Commit old_merged_disk new_merged_disk =>
    (exists txns,
       log_crash_rep (During_Commit_Log_Write txns) (snd s) /\
       old_merged_disk = total_mem_map fst (shift (plus data_start)
       (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
       (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])) \/
    (exists old_txns txns,
       log_crash_rep (During_Commit_Header_Write old_txns txns) (snd s) /\

       new_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
           (map data_blocks txns))) /\

    old_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list old_txns)
                            (map data_blocks old_txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []))
      
  | After_Commit new_merged_disk =>
    exists txns,
    log_rep txns (snd s) /\
     new_merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                            (map data_blocks txns))) /\
     (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])

  | During_Apply merged_disk =>
    exists txns,
    ((log_crash_rep (Log.During_Apply txns) (snd s) /\
    total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                        (map data_blocks txns))) 
    = total_mem_map fst (shift (plus data_start) (snd (snd s))) /\
    (forall a, a >= data_start -> 
    snd ((snd (snd s)) a) = [])) \/
    log_rep txns (snd s)) /\
     merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                        (map data_blocks txns))) /\
      (forall a, a >= data_start -> 
      ~(exists l_a, In l_a (map addr_list txns) /\ In a l_a) -> 
      snd ((snd (snd s)) a) = [])

  | After_Apply merged_disk =>
    log_rep [] (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (snd (snd s))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])
   
  | During_Recovery merged_disk =>
    exists txns,
    log_crash_rep (Log.During_Recovery txns) (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                            (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])
    end.

Definition cached_log_reboot_rep merged_disk (s: LayerImplementation.state CachedDiskLang) :=
  exists txns,
    log_reboot_rep txns (snd s) /\
    merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s)) a) = []).

  Definition cached_log_reboot_rep_explicit_part hdr merged_disk valid_part (s: LayerImplementation.state CachedDiskLang) :=
      exists txns,
        log_reboot_rep_explicit_part hdr txns valid_part (snd s) /\
        merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
        (forall a, a >= data_start -> snd ((snd (snd s)) a) = []).


Set Nested Proofs Allowed.

(*** Lemmas ***)

    Lemma log_rep_forall2_txns_length_match:
    forall txns s,
      log_rep txns s ->
      Forall2 (fun l_a l_v => length l_a = length l_v)
              (map addr_list txns) (map data_blocks txns).
  Proof.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup.
    eapply forall_forall2.
    rewrite <- combine_map.
    apply Forall_forall; intros.
    apply in_map_iff in H; cleanup.
    simpl.
    eapply Forall_forall in H7; eauto.
    unfold txn_well_formed in *; cleanup; eauto.
    rewrite firstn_length_l; eauto.
    repeat rewrite map_length; eauto.
  Qed.


(*** SPECS ***)
Definition write_batch_to_cache_finished_oracle_is len :=
  (repeat (OpToken
  (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token1 (CacheOperation addr_dec value) CryptoDiskOperation Cont)) len) ++ 
  [LayerImplementation.Cont CachedDiskOperation].

Global Opaque Log.commit Log.apply_log.
Theorem write_batch_to_cache_finished_oracle:
  forall al vl o s s' t u,
    length al = length vl ->
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Finished s' t) ->
    snd s' = snd s /\
    fst s' = Mem.upd_batch (fst s) al vl /\
    o = write_batch_to_cache_finished_oracle_is (length al).
Proof.
  unfold write_batch_to_cache_finished_oracle_is;
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia.
  repeat invert_exec.
  edestruct IHal; cleanup; intuition eauto.
  simpl in *; rewrite H3; eauto.
Qed.


Definition write_batch_to_cache_crashed_oracle_is o n :=
  o = (repeat (OpToken (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token1 (CacheOperation addr_dec value) CryptoDiskOperation Cont)) n) ++ 
  [LayerImplementation.Crash CachedDiskOperation] \/ 
  o = (repeat (OpToken (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token1 (CacheOperation addr_dec value) CryptoDiskOperation Cont)) n) ++ 
  [OpToken (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token1 (CacheOperation addr_dec value) CryptoDiskOperation Crash)].

Theorem write_batch_to_cache_crashed_oracle:
  forall al vl o s s' u,
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Crashed s') ->
    snd s' = snd s /\
    (exists n, write_batch_to_cache_crashed_oracle_is o n).
Proof.
  unfold write_batch_to_cache_crashed_oracle_is;
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia;
  repeat invert_exec; eauto.
  
  intuition; eauto.
  exists 0; intuition eauto.
  intuition; eauto.
  exists 0; intuition eauto.

  split_ors; cleanup; repeat invert_exec; eauto.
  intuition; eauto.
  exists 0; intuition eauto.

  eapply IHal in H1; cleanup; eauto.
  simpl; intuition eauto; cleanup.
  exists (S x); simpl; intuition.
  exists (S x); simpl; intuition.
Qed.

Theorem write_batch_to_cache_finished:
  forall al vl o s s' t u,
    length al = length vl ->
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Finished s' t) ->
    snd s' = snd s /\
    fst s' = Mem.upd_batch (fst s) al vl.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia.
  repeat invert_exec.
  edestruct IHal; eauto.
Qed.


Theorem write_batch_to_cache_crashed:
  forall al vl o s s' u,
    exec CachedDiskLang u o s (write_batch_to_cache al vl) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia;
  invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec; eauto.
  eapply IHal in H1; cleanup; eauto.
Qed.

Definition write_lists_to_cache_finished_oracle_is {T} (ll: list (list T)) :=
  fold_right (@app _) [LayerImplementation.Cont CachedDiskOperation]  (map (fun l => write_batch_to_cache_finished_oracle_is (length l)) ll).

Theorem write_lists_to_cache_finished_oracle:
  forall l_la_lv s o s' t u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Finished s' t) ->
    fst s' = Mem.list_upd_batch (fst s) (map fst l_la_lv) (map snd l_la_lv) /\
    snd s' = snd s /\
    o = write_lists_to_cache_finished_oracle_is (map fst l_la_lv).
Proof.
  unfold write_lists_to_cache_finished_oracle_is;
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  inversion H; cleanup.
  apply write_batch_to_cache_finished_oracle in H0; eauto.
  cleanup.
  apply IHl_la_lv in H1; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.  

Definition write_lists_to_cache_crashed_oracle_is {T1 T2} o (l_la_lv: list (list T1 * list T2)) :=
(exists n o', o = fold_right (@app _) o' (map write_batch_to_cache_finished_oracle_is (map (fun l => length (fst l)) (firstn n l_la_lv))) /\
    (o' = [LayerImplementation.Crash CachedDiskOperation] \/ 
    (exists m, write_batch_to_cache_crashed_oracle_is o' m))).

Theorem write_lists_to_cache_crashed_oracle:
  forall l_la_lv s o s' u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Crashed s') ->
    snd s' = snd s /\
    write_lists_to_cache_crashed_oracle_is o l_la_lv.
Proof.
  unfold write_lists_to_cache_crashed_oracle_is;
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  setoid_rewrite firstn_nil; simpl; intuition eauto.
  exists 0; eauto.

  split_ors; cleanup; repeat invert_exec.
  apply write_batch_to_cache_crashed_oracle in H0; eauto.
  cleanup; intuition eauto.
  exists 0; simpl; intuition eauto.

  inversion H; cleanup.
  apply write_batch_to_cache_finished_oracle in H1; eauto.
  apply IHl_la_lv in H2; eauto.
  cleanup; repeat cleanup_pairs; eauto.
  cleanup; intuition eauto; cleanup.

  eexists (S x3), _; simpl; intuition eauto.
  rewrite H4; eauto.
  
  eexists (S x3), _; simpl; split.
  2: right; intuition eauto.
  rewrite H4; eauto.
Qed.

Theorem write_lists_to_cache_finished:
  forall l_la_lv s o s' t u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Finished s' t) ->
    fst s' = Mem.list_upd_batch (fst s) (map fst l_la_lv) (map snd l_la_lv) /\
    snd s' = snd s.
Proof.
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  inversion H; cleanup.
  apply write_batch_to_cache_finished in H0; eauto.
  cleanup.
  apply IHl_la_lv in H1; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.  
  

Theorem write_lists_to_cache_crashed:
  forall l_la_lv s o s' u,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang u o s (write_lists_to_cache l_la_lv) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec.
  apply write_batch_to_cache_crashed in H0; eauto.

  inversion H; cleanup.
  apply write_batch_to_cache_finished in H1; eauto.
  apply IHl_la_lv in H2; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.

Global Opaque Log.init.

Theorem init_finished:
  forall s o s' t u l_av,
    let l_a := map fst l_av in
    let l_v := map snd l_av in
    exec CachedDiskLang u o s (init l_av) (Finished s' t) ->
    cached_log_rep (total_mem_map fst (shift (Init.Nat.add data_start) (upd_batch_set (snd (snd s)) (map (Nat.add data_start) l_a) l_v))) s'.
Proof.
  unfold init; simpl; intros; repeat invert_exec; eauto.
  eapply init_finished in H1; eauto; cleanup. 
  unfold cached_log_rep; simpl.
  exists []; simpl; intuition eauto.
  {
    setoid_rewrite H1.
    rewrite map_fst_combine, map_snd_combine; simpl.
    repeat rewrite total_mem_map_shift_comm.
    rewrite total_mem_map_fst_sync_noop.
    repeat rewrite total_mem_map_fst_upd_batch_set.
    repeat rewrite <- shift_upd_batch_comm.
    rewrite total_mem_map_fst_upd_set.
    rewrite shift_upd_noop; simpl; eauto.
    intros.
    pose proof hdr_before_log.
    pose proof data_start_where_log_ends.
    lia.
    {
      unfold sumbool_agree; intros.
      destruct (addr_dec x0 y);
      destruct (addr_dec (data_start + x0) (data_start + y)); eauto.
      lia.
    }
    {
      unfold sumbool_agree; intros.
      destruct (addr_dec x0 y);
      destruct (addr_dec (data_start + x0) (data_start + y)); eauto.
      lia.
    }
    all: repeat rewrite map_length; eauto.
  }
  {
    eapply equal_f in H1.
    setoid_rewrite H1; simpl; eauto.
  }
  {
    intros a Hx.
    apply in_map_iff in Hx; cleanup.
    destruct x0; simpl in *.
    apply in_combine_l in H2.
    apply in_map_iff in H2; cleanup.
    apply in_map_iff in H2; cleanup.
    lia.
  }
Qed.

Theorem read_finished:
  forall merged_disk a s o s' t u,
    cached_log_rep merged_disk s ->
    exec CachedDiskLang u o s (read a) (Finished s' t) ->
    ((exists v, 
    merged_disk a = v /\
    t = v /\
    a < data_length)  \/ 
    (a >= data_length /\ t = value0)) /\
    s' = s.
Proof.
  unfold read; simpl; intros; repeat invert_exec; eauto.
  cleanup; repeat invert_exec; eauto.
  {
    unfold cached_log_rep in *; cleanup.
    
    eapply equal_f in H.
    rewrite H in H7.
    intuition eauto.
    left; eexists.
    rewrite total_mem_map_shift_comm.
    rewrite shift_some.
    rewrite total_mem_map_fst_list_upd_batch_set.
    intuition eauto.
    {
      intuition eauto.
      rewrite list_upd_batch_to_upd_batch in H7.
      rewrite list_upd_batch_to_upd_batch_total.
      rewrite upd_batch_dedup_by_fst in H7.
      rewrite upd_batch_dedup_by_fst_total.
      
      symmetry; eapply upd_batch_in_some_total_mem; eauto.
      apply NoDup_map_fst_dedup_by_fst.
      all: try apply flatten_length_eq.
      all: eapply log_rep_forall2_txns_length_match; eauto.
    }
    {
      destruct s; simpl in *; eauto.
    }
  }
  {
    simpl in *.
    unfold cached_log_rep in *; cleanup.
    eapply equal_f in H.
    setoid_rewrite H7 in H.
    symmetry in H; eapply list_upd_batch_none in H.
    logic_clean.
    intuition eauto.
    left; eexists.
    rewrite total_mem_map_shift_comm.
    rewrite shift_some.
    rewrite total_mem_map_fst_list_upd_batch_set.
    rewrite list_upd_batch_not_in; eauto.
    repeat cleanup_pairs; eauto.
    simpl.
    {
    eapply forall_forall2.
    apply Forall_forall; intros.
    rewrite <- combine_map in H1.
    apply in_map_iff in H1; cleanup; simpl.

     unfold log_rep, log_rep_general, log_rep_explicit in *;
     simpl in *; logic_clean.
     unfold log_rep_inner, txns_valid in *; logic_clean.
     
     eapply Forall_forall in H12; eauto.
     unfold txn_well_formed in H12; logic_clean.
     rewrite H15 in *.
     apply firstn_length_l; eauto; lia.
     repeat rewrite map_length; eauto.
    }
  }
  intuition eauto.
  right; intuition eauto; try lia.
Qed.

Theorem read_crashed:
  forall a s o s' u,
    exec CachedDiskLang u o s (read a) (Crashed s') ->
    s' = s.
Proof. 
  unfold read; simpl; intros; cleanup; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec.
  destruct s; eauto.
  cleanup; repeat invert_exec;
  repeat cleanup_pairs; eauto.
  destruct s1; eauto.
Qed.

Lemma recover_finished:  
  forall merged_disk s o s' t u,
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang u o s recover (Finished s' t) ->
  cached_log_rep merged_disk s'.
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  eapply recover_finished in H6; eauto.
  apply write_lists_to_cache_finished in H4.
  repeat cleanup_pairs.
  unfold cached_log_rep; simpl; eexists; intuition eauto.
  rewrite map_fst_combine, map_snd_combine by (repeat rewrite map_length; eauto); eauto.
  assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite map_noop; eauto.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H12; eauto.
    unfold txn_well_formed in H12; simpl in *; cleanup.
    eapply Forall_forall in H16; eauto; lia.
  }
  rewrite A at 2.
  rewrite shift_list_upd_batch_set_comm.
  rewrite shift_eq_after with (m1:=s2)(m2:=sync s3).
  rewrite <- shift_list_upd_batch_set_comm.
  rewrite <- A.

  repeat (rewrite total_mem_map_shift_comm, total_mem_map_fst_list_upd_batch_set);
  rewrite total_mem_map_fst_sync_noop; eauto.
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    intros; lia.
  }
  {
    intros; apply H8; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    rewrite H8; simpl; eauto.
  }
  {
    cleanup.
    rewrite Forall_forall; intros.
    rewrite <- combine_map in H1.
    apply in_map_iff in H1; cleanup; simpl.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H15; eauto.
    unfold txn_well_formed in H15; simpl in *; cleanup.
    apply firstn_length_l; eauto.
  }
Qed.

Lemma recover_crashed:  
  forall merged_disk s o s' u,
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang u o s recover (Crashed s') ->
  (cached_log_reboot_rep merged_disk s' \/
  cached_log_crash_rep (During_Recovery merged_disk) s' \/
  cached_log_crash_rep (After_Commit merged_disk) s') /\
  ((forall a, a >= data_start -> snd (snd s') a = snd (snd s) a) \/
     (forall a, a >= data_start -> snd (snd s') a = sync (snd (snd s)) a)) .
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  split_ors; cleanup; repeat invert_exec.
  repeat cleanup_pairs; eauto.
  intuition eauto.
  split_ors; cleanup; repeat invert_exec.
  {
    eapply recover_crashed in H5; eauto.
    repeat cleanup_pairs.
    split_ors; cleanup.
    {
      intuition eauto.
      left; eexists; intuition eauto.
      assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite map_noop; eauto.
    intros.
    unfold log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H22; eauto.
    unfold txn_well_formed in H22; simpl in *; cleanup_no_match.
    eapply Forall_forall in H25; eauto; lia.
      }
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s2)(m2:=s3).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
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
      {
        rewrite H1; eauto.
      }
    }
    split_ors; cleanup.
    {
      intuition eauto.
      right; left; eexists; intuition eauto.
      assert (A: map addr_list x =
                 map (map (Init.Nat.add data_start))
                     (map (map (fun a => a - data_start)) (map addr_list x))). {
        repeat rewrite map_map.
        apply map_ext_in.
        intros.
        rewrite map_map.
        rewrite map_noop; eauto.
        intros.
        unfold log_reboot_rep, log_rep_general, log_rep_explicit,
        log_rep_inner, txns_valid in *; simpl in *; cleanup.
        eapply Forall_forall in H13; eauto.
        unfold txn_well_formed in H13; simpl in *; cleanup_no_match.
        eapply Forall_forall in H17; eauto; lia.
      }
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s2)(m2:=s3).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
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
      {
        rewrite H1; eauto.
      }
    }
    intuition eauto.
    left; eexists; intuition eauto.
    {
      unfold log_rep, log_rep_general, log_reboot_rep in *.
      cleanup.
      do 4 eexists; intuition eauto; congruence.
    }
    assert (A: map addr_list x =
               map (map (Init.Nat.add data_start))
                   (map (map (fun a => a - data_start)) (map addr_list x))). {
      repeat rewrite map_map.
      apply map_ext_in.
      intros.
      rewrite map_map.
      rewrite map_noop; eauto.
      intros.
      unfold log_rep, log_rep_general, log_rep_explicit,
      log_rep_inner, txns_valid in *; simpl in *; cleanup.
      eapply Forall_forall in H12; eauto.
      unfold txn_well_formed in H12; simpl in *; cleanup_no_match.
      eapply Forall_forall in H16; eauto; lia.
    }
    
    rewrite A at 2.
    rewrite shift_list_upd_batch_set_comm.
    rewrite shift_eq_after with (m1:=s2)(m2:=sync s3).
    rewrite <- shift_list_upd_batch_set_comm.
    rewrite <- A; eauto.
    repeat rewrite total_mem_map_shift_comm.
    repeat rewrite total_mem_map_fst_list_upd_batch_set.
    rewrite total_mem_map_fst_sync_noop; eauto.
    
    {
      unfold sumbool_agree; intros; intuition eauto.
      destruct (addr_dec x0 y); subst.
      destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
      destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
    }
    {
      intros; lia.
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
    {
      rewrite H1; simpl; eauto.
    }
  }
  {
    eapply Log.Specs.recover_finished in H6; eauto; cleanup.
    apply write_lists_to_cache_crashed in H5; cleanup.
    repeat cleanup_pairs.
    {
      intuition eauto.
      right; right; eexists; intuition eauto.
    {
      unfold log_rep, log_rep_general, log_reboot_rep in *.
      cleanup.
      assert (A: map addr_list x =
                 map (map (Init.Nat.add data_start))
                     (map (map (fun a => a - data_start)) (map addr_list x))). {
        repeat rewrite map_map.
        apply map_ext_in.
        intros.
        rewrite map_map.
        rewrite map_noop; eauto.
        intros.
        unfold log_rep, log_rep_general, log_rep_explicit,
        log_rep_inner, txns_valid in *; simpl in *; cleanup_no_match.
        eapply Forall_forall in H13; eauto.
        unfold txn_well_formed in H13; simpl in *; cleanup_no_match.
        eapply Forall_forall in H24; eauto; lia.
      }
    
      rewrite A at 2.
      rewrite shift_list_upd_batch_set_comm.
      rewrite shift_eq_after with (m1:=s3)(m2:=sync s4).
      rewrite <- shift_list_upd_batch_set_comm.
      rewrite <- A; eauto.
      repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite total_mem_map_fst_sync_noop; eauto.
      
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x9 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x9) (data_start + y)); eauto; lia.
      }
      {
        intros; lia.
      }
      {
        intros; apply H8; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x9 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x9) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H8; simpl; eauto.
    }
    }
    {
      apply Forall_forall; intros.
      rewrite <- combine_map in H3.
      apply in_map_iff in H3; cleanup; simpl.
      unfold log_reboot_rep, log_rep_explicit, log_rep_inner, txns_valid in H;
      simpl in *; logic_clean.
      eapply Forall_forall in H16; eauto.
      unfold txn_well_formed in H16; logic_clean.
      rewrite H19.
      apply firstn_length_l; eauto.
      lia.
    }
  }
Qed.

  
Theorem write_finished:
  forall merged_disk s o al vl s' t u,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang u o s (write al vl) (Finished s' t) ->
  (cached_log_rep merged_disk s' /\
   (~Forall (fun a => a < data_length) al \/
    ~NoDup al \/
    length al <> length vl \/
    length (addr_list_to_blocks (map (plus data_start) al)) + length vl > log_length)) \/
  (cached_log_rep (upd_batch merged_disk al vl) s' /\
   Forall (fun a => a < data_length) al /\
   NoDup al /\
   length al = length vl /\
   length (addr_list_to_blocks (map (plus data_start) al)) + length vl <= log_length).
Proof.
  unfold write; simpl; intros.
  cleanup; simpl in *; invert_exec_no_match; simpl in *; cleanup_no_match; simpl in *; eauto.
  invert_exec.
  unfold cached_log_rep in *; logic_clean.
  destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
  unfold log_rep in *; logic_clean.
  eapply commit_finished in H3; eauto.
  all: try rewrite H6.
  split_ors; cleanup_no_match.
  {(** initial commit is success **)
    right.
    repeat invert_exec.
    apply write_batch_to_cache_finished in H1; eauto; cleanup.
    repeat cleanup_pairs.
    split; eauto.
    exists (x4++[x7]).
    simpl.
    repeat rewrite map_app; simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *.
    eapply_fresh forall_app_l in H12. 
    inversion Hx; simpl in *; cleanup.
    unfold txn_well_formed in H21; cleanup.
    rewrite firstn_app2; eauto.
    simpl; intuition eauto.
    {
      rewrite Mem.list_upd_batch_app; eauto.
      repeat rewrite map_length; eauto.
    }
    {
      do 3 eexists; intuition eauto.
    }
    {
      assert (A: map addr_list x4 ++ [map (Init.Nat.add data_start) al] =
                 map (map (Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x4) ++ [al])). {
        repeat rewrite map_map; simpl.
        rewrite map_app; simpl.
        repeat rewrite map_map.
        setoid_rewrite map_ext_in at 3.
        eauto.
        intros.
        rewrite map_map.        
        setoid_rewrite map_ext_in.
        apply map_id.
        intros; simpl.
        eapply Forall_forall in H12; eauto.
        unfold txn_well_formed in H12; logic_clean.
        eapply Forall_forall in H37; eauto; lia.        
      }
      setoid_rewrite A.
      rewrite shift_list_upd_batch_set_comm; eauto.
      setoid_rewrite shift_eq_after with (m1:= s0) (m2:= sync s3); intros; try lia.
      rewrite <- shift_list_upd_batch_set_comm; eauto.      
      rewrite <- A.

      repeat rewrite total_mem_map_shift_comm.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite total_mem_map_fst_sync_noop.
      rewrite list_upd_batch_app; simpl.
      rewrite shift_upd_batch_comm; eauto.
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
      {
        repeat rewrite map_length; eauto.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
      {
        apply H11; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H11; simpl; eauto.
    }
    rewrite map_length; eauto.
    rewrite map_length; eauto.
  }
  {(** First commit failed. Time to apply the log **)
    repeat invert_exec.
    simpl in *.
    repeat cleanup_pairs; simpl in *.
    eapply apply_log_finished in H10; eauto.
    logic_clean.
    apply write_batch_to_cache_finished in H1.
    logic_clean.
    unfold log_rep in *; logic_clean.
    eapply commit_finished in H11; eauto.
    all: try rewrite H7.
    split_ors; cleanup_no_match.
    {(** second commit is success **)
    right.
    repeat cleanup_pairs.
    split; eauto.
    exists ([x1]).
    simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *. 
    inversion H16; simpl in *; cleanup.
    unfold txn_well_formed in H3; cleanup.
    rewrite firstn_app2; eauto.
    unfold log_header_block_rep in *; simpl in *; cleanup.
    simpl; intuition eauto.
    {
      do 3 eexists; intuition eauto.
    }
    {
      rewrite shift_upd_batch_set_comm.
      setoid_rewrite shift_eq_after with (m1:= s1) (m2:= sync
          (sync
             (upd_set (list_upd_batch_set s4 (map addr_list x4) (map data_blocks x4)) hdr_block_num
                      (encode_header (update_hdr (decode_header (fst (s4 hdr_block_num))) header_part0))))); intros; try lia.
      rewrite sync_idempotent.
      rewrite total_mem_map_fst_upd_batch_set.
      repeat rewrite total_mem_map_shift_comm.
      rewrite total_mem_map_fst_sync_noop.
      rewrite total_mem_map_fst_upd_set.
      repeat rewrite total_mem_map_fst_list_upd_batch_set.
      rewrite shift_upd_noop; eauto.

      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
      }
      {
        eapply H14; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
    }
    {
      rewrite H14; simpl; eauto.
    }
    rewrite map_length; eauto.
    }
    {
      rewrite app_length in H12.
      repeat cleanup_pairs.
      unfold log_rep, log_rep_general, log_rep_explicit,
      log_rep_inner, header_part_is_valid, txns_valid in *;
      simpl in *; cleanup; simpl in *. 
          
      rewrite <- H13 in *; simpl in *.
      lia.
    }
    {
      rewrite firstn_app2; eauto.
      apply FinFun.Injective_map_NoDup; eauto.
      unfold FinFun.Injective; intros; lia.
      rewrite map_length; eauto.
    }
    {
      rewrite firstn_app2; eauto.    
      apply Forall_forall; intros.
      apply in_map_iff in H10; cleanup.
      eapply_fresh Forall_forall in f; eauto.
      pose proof data_fits_in_disk.
      split; try lia.
      rewrite map_length; eauto.
    }    
    {
      rewrite app_length, map_length; lia.
    }
    {
      erewrite addr_list_to_blocks_length_eq.
      eapply addr_list_to_blocks_length_nonzero; eauto.
      rewrite map_length; eauto.
    }
    {
      lia.
    }
    {
      rewrite map_length; eauto.
    }
  } 
  {
    rewrite H7.
    rewrite firstn_app2; eauto.
    apply FinFun.Injective_map_NoDup; eauto.
    unfold FinFun.Injective; intros; lia.
    rewrite map_length; eauto.
  }
  {
    rewrite H7.
    rewrite firstn_app2; eauto.    
    apply Forall_forall; intros.
    apply in_map_iff in H8; cleanup_no_match.
    eapply_fresh Forall_forall in f; eauto.
    pose proof data_fits_in_disk.
    split; try lia.
    rewrite map_length; eauto.
  }
  {
    rewrite H7.
    rewrite app_length, map_length; lia.
  }
  {
    erewrite addr_list_to_blocks_length_eq.
    eapply addr_list_to_blocks_length_nonzero; eauto.
    rewrite map_length; eauto.
  }
  {
    lia.
  }
  {
    assert(A: length al = 0) by lia.
    apply length_zero_iff_nil in A.
    subst; simpl.
    right; intuition eauto; lia.
  }
  {
    left; intuition eauto; lia.
  }
  {
    left; intuition eauto; lia.
  }
Qed.
(**************)

Definition transform_token := 
  (fun o : LayerImplementation.token' CryptoDiskOperation =>
match o with
| OpToken _ o1 =>
    OpToken
      (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
      (Token2 (CacheOperation addr_dec value) CryptoDiskOperation o1)
| LayerImplementation.Crash _ =>
    LayerImplementation.Crash
      (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
| LayerImplementation.Cont _ =>
    LayerImplementation.Cont
      (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
end).


Definition write_crashed_oracle_is_1 o hdr len :=
  ((exists o', 
  o = OpToken
  (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
     (Token2 CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size))
        DiskLayer.Cont))
:: LayerImplementation.Cont
     (HorizontalComposition (CacheOperation addr_dec value)
        CryptoDiskOperation)
   :: LayerImplementation.Cont
        (HorizontalComposition (CacheOperation addr_dec value)
           CryptoDiskOperation) 
        :: map transform_token o' /\
  (read_encrypted_log_crashed_oracle_is o' hdr Current_Part \/
   apply_log_crashed_oracle_is_2 o' hdr)) 
  \/
  (exists o', o = OpToken
  (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
  (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
     (Token2 CryptoOperation
        (DiskOperation addr_dec value (fun a : addr => a < disk_size))
        DiskLayer.Cont))
:: LayerImplementation.Cont
     (HorizontalComposition (CacheOperation addr_dec value)
        CryptoDiskOperation)
   :: LayerImplementation.Cont
        (HorizontalComposition (CacheOperation addr_dec value)
           CryptoDiskOperation)
      :: OpToken
           (HorizontalComposition (CacheOperation addr_dec value)
              CryptoDiskOperation)
           (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
              (Token2 CryptoOperation
                 (DiskOperation addr_dec value
                    (fun a : addr => a < disk_size)) DiskLayer.Cont))
         :: LayerImplementation.Cont
              (HorizontalComposition (CacheOperation addr_dec value)
                 CryptoDiskOperation)
            :: map
                 (fun o : LayerImplementation.token' CryptoDiskOperation =>
                  match o with
                  | OpToken _ o1 =>
                      OpToken
                        (HorizontalComposition
                           (CacheOperation addr_dec value)
                           CryptoDiskOperation)
                        (Token2 (CacheOperation addr_dec value)
                           CryptoDiskOperation o1)
                  | LayerImplementation.Crash _ =>
                      LayerImplementation.Crash
                        (HorizontalComposition
                           (CacheOperation addr_dec value)
                           CryptoDiskOperation)
                  | LayerImplementation.Cont _ =>
                      LayerImplementation.Cont
                        (HorizontalComposition
                           (CacheOperation addr_dec value)
                           CryptoDiskOperation)
                  end)
                 ((BatchOperations.rec_oracle_finished_disk
                     (count (current_part hdr)) ++
                   (BatchOperations.rec_oracle_finished_crypto
                      (count (current_part hdr)) ++
                    [LayerImplementation.Cont
                       (HorizontalComposition CryptoOperation
                          (DiskOperation addr_dec value
                             (fun a : addr => a < disk_size)))]) ++
                   [LayerImplementation.Cont
                      (HorizontalComposition CryptoOperation
                         (DiskOperation addr_dec value
                            (fun a : addr => a < disk_size)))]) ++
                  flush_txns_finished_oracle_is (records (current_part hdr))) ++
               OpToken
                 (HorizontalComposition (CacheOperation addr_dec value)
                    CryptoDiskOperation)
                 (Token1 (CacheOperation addr_dec value) CryptoDiskOperation
                    Cont)
               :: map transform_token o' /\
        commit_crashed_oracle_is_1 o' len)
).


Definition write_crashed_oracle_is_2 o hdr len :=
(exists o', o = OpToken
        (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
        (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
           (Token2 CryptoOperation
              (DiskOperation addr_dec value (fun a : addr => a < disk_size))
              DiskLayer.Cont))
      :: LayerImplementation.Cont
           (HorizontalComposition (CacheOperation addr_dec value)
              CryptoDiskOperation)
         :: LayerImplementation.Cont
              (HorizontalComposition (CacheOperation addr_dec value)
                 CryptoDiskOperation)
            :: OpToken
                 (HorizontalComposition (CacheOperation addr_dec value)
                    CryptoDiskOperation)
                 (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
                    (Token2 CryptoOperation
                       (DiskOperation addr_dec value
                          (fun a : addr => a < disk_size)) DiskLayer.Cont))
               :: LayerImplementation.Cont
                    (HorizontalComposition (CacheOperation addr_dec value)
                       CryptoDiskOperation)
                  :: map
                       (fun o : LayerImplementation.token' CryptoDiskOperation =>
                        match o with
                        | OpToken _ o1 =>
                            OpToken
                              (HorizontalComposition
                                 (CacheOperation addr_dec value)
                                 CryptoDiskOperation)
                              (Token2 (CacheOperation addr_dec value)
                                 CryptoDiskOperation o1)
                        | LayerImplementation.Crash _ =>
                            LayerImplementation.Crash
                              (HorizontalComposition
                                 (CacheOperation addr_dec value)
                                 CryptoDiskOperation)
                        | LayerImplementation.Cont _ =>
                            LayerImplementation.Cont
                              (HorizontalComposition
                                 (CacheOperation addr_dec value)
                                 CryptoDiskOperation)
                        end)
                       ((BatchOperations.rec_oracle_finished_disk
                           (count (current_part hdr)) ++
                         (BatchOperations.rec_oracle_finished_crypto
                            (count (current_part hdr)) ++
                          [LayerImplementation.Cont
                             (HorizontalComposition CryptoOperation
                                (DiskOperation addr_dec value
                                   (fun a : addr => a < disk_size)))]) ++
                         [LayerImplementation.Cont
                            (HorizontalComposition CryptoOperation
                               (DiskOperation addr_dec value
                                  (fun a : addr => a < disk_size)))]) ++
                        flush_txns_finished_oracle_is (records (current_part hdr))) ++
                     OpToken
                       (HorizontalComposition (CacheOperation addr_dec value)
                          CryptoDiskOperation)
                       (Token1 (CacheOperation addr_dec value) CryptoDiskOperation
                          Cont)
                     :: map transform_token o' /\ 
                     commit_crashed_oracle_is_2 o' len).

Definition write_crashed_oracle_is_3 o hdr len :=
(exists o', o = OpToken
(HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
(Token2 (CacheOperation addr_dec value) CryptoDiskOperation
  (Token2 CryptoOperation
      (DiskOperation addr_dec value (fun a : addr => a < disk_size))
      DiskLayer.Cont))
:: LayerImplementation.Cont
  (HorizontalComposition (CacheOperation addr_dec value)
      CryptoDiskOperation)
:: LayerImplementation.Cont
      (HorizontalComposition (CacheOperation addr_dec value)
        CryptoDiskOperation)
    :: OpToken
        (HorizontalComposition (CacheOperation addr_dec value)
            CryptoDiskOperation)
        (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
            (Token2 CryptoOperation
              (DiskOperation addr_dec value
                  (fun a : addr => a < disk_size)) DiskLayer.Cont))
      :: LayerImplementation.Cont
            (HorizontalComposition (CacheOperation addr_dec value)
              CryptoDiskOperation)
          :: map
              (fun o : LayerImplementation.token' CryptoDiskOperation =>
                match o with
                | OpToken _ o1 =>
                    OpToken
                      (HorizontalComposition
                        (CacheOperation addr_dec value)
                        CryptoDiskOperation)
                      (Token2 (CacheOperation addr_dec value)
                        CryptoDiskOperation o1)
                | LayerImplementation.Crash _ =>
                    LayerImplementation.Crash
                      (HorizontalComposition
                        (CacheOperation addr_dec value)
                        CryptoDiskOperation)
                | LayerImplementation.Cont _ =>
                    LayerImplementation.Cont
                      (HorizontalComposition
                        (CacheOperation addr_dec value)
                        CryptoDiskOperation)
                end)
              ((BatchOperations.rec_oracle_finished_disk
                  (count (current_part hdr)) ++
                (BatchOperations.rec_oracle_finished_crypto
                    (count (current_part hdr)) ++
                  [LayerImplementation.Cont
                    (HorizontalComposition CryptoOperation
                        (DiskOperation addr_dec value
                          (fun a : addr => a < disk_size)))]) ++
                [LayerImplementation.Cont
                    (HorizontalComposition CryptoOperation
                      (DiskOperation addr_dec value
                          (fun a : addr => a < disk_size)))]) ++
                flush_txns_finished_oracle_is (records (current_part hdr))) ++
            OpToken
              (HorizontalComposition (CacheOperation addr_dec value)
                  CryptoDiskOperation)
              (Token1 (CacheOperation addr_dec value) CryptoDiskOperation
                  Cont)
            :: map transform_token o' /\ 
            commit_crashed_oracle_is_3 o' len).
            

Definition write_crashed_oracle_is_4 o hdr len :=
            ((exists o', o = OpToken
            (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
            (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
               (Token2 CryptoOperation
                  (DiskOperation addr_dec value (fun a : addr => a < disk_size))
                  DiskLayer.Cont))
          :: LayerImplementation.Cont
               (HorizontalComposition (CacheOperation addr_dec value)
                  CryptoDiskOperation)
             :: LayerImplementation.Cont
                  (HorizontalComposition (CacheOperation addr_dec value)
                     CryptoDiskOperation)
                :: OpToken
                     (HorizontalComposition (CacheOperation addr_dec value)
                        CryptoDiskOperation)
                     (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
                        (Token2 CryptoOperation
                           (DiskOperation addr_dec value
                              (fun a : addr => a < disk_size)) DiskLayer.Cont))
                   :: LayerImplementation.Cont
                        (HorizontalComposition (CacheOperation addr_dec value)
                           CryptoDiskOperation)
                      :: map
                           (fun o : LayerImplementation.token' CryptoDiskOperation =>
                            match o with
                            | OpToken _ o1 =>
                                OpToken
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                                  (Token2 (CacheOperation addr_dec value)
                                     CryptoDiskOperation o1)
                            | LayerImplementation.Crash _ =>
                                LayerImplementation.Crash
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                            | LayerImplementation.Cont _ =>
                                LayerImplementation.Cont
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                            end)
                           ((BatchOperations.rec_oracle_finished_disk
                               (count (current_part hdr)) ++
                             (BatchOperations.rec_oracle_finished_crypto
                                (count (current_part hdr)) ++
                              [LayerImplementation.Cont
                                 (HorizontalComposition CryptoOperation
                                    (DiskOperation addr_dec value
                                       (fun a : addr => a < disk_size)))]) ++
                             [LayerImplementation.Cont
                                (HorizontalComposition CryptoOperation
                                   (DiskOperation addr_dec value
                                      (fun a : addr => a < disk_size)))]) ++
                            flush_txns_finished_oracle_is (records (current_part hdr))) ++
                         OpToken
                           (HorizontalComposition (CacheOperation addr_dec value)
                              CryptoDiskOperation)
                           (Token1 (CacheOperation addr_dec value) CryptoDiskOperation
                              Cont)
                         :: map transform_token o' /\
            commit_crashed_oracle_is_4 o' len) \/
            (exists o', o = OpToken
            (HorizontalComposition (CacheOperation addr_dec value)
               CryptoDiskOperation)
            (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
               (Token2 CryptoOperation
                  (DiskOperation addr_dec value (fun a : addr => a < disk_size))
                  DiskLayer.Cont))
          :: LayerImplementation.Cont
               (HorizontalComposition (CacheOperation addr_dec value)
                  CryptoDiskOperation)
             :: LayerImplementation.Cont
                  (HorizontalComposition (CacheOperation addr_dec value)
                     CryptoDiskOperation)
                :: OpToken
                     (HorizontalComposition (CacheOperation addr_dec value)
                        CryptoDiskOperation)
                     (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
                        (Token2 CryptoOperation
                           (DiskOperation addr_dec value
                              (fun a : addr => a < disk_size)) DiskLayer.Cont))
                   :: LayerImplementation.Cont
                        (HorizontalComposition (CacheOperation addr_dec value)
                           CryptoDiskOperation)
                      :: map
                           (fun o : LayerImplementation.token' CryptoDiskOperation =>
                            match o with
                            | OpToken _ o1 =>
                                OpToken
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                                  (Token2 (CacheOperation addr_dec value)
                                     CryptoDiskOperation o1)
                            | LayerImplementation.Crash _ =>
                                LayerImplementation.Crash
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                            | LayerImplementation.Cont _ =>
                                LayerImplementation.Cont
                                  (HorizontalComposition
                                     (CacheOperation addr_dec value)
                                     CryptoDiskOperation)
                            end)
                           ((BatchOperations.rec_oracle_finished_disk
                               (count (current_part hdr)) ++
                             (BatchOperations.rec_oracle_finished_crypto
                                (count (current_part hdr)) ++
                              [LayerImplementation.Cont
                                 (HorizontalComposition CryptoOperation
                                    (DiskOperation addr_dec value
                                       (fun a : addr => a < disk_size)))]) ++
                             [LayerImplementation.Cont
                                (HorizontalComposition CryptoOperation
                                   (DiskOperation addr_dec value
                                      (fun a : addr => a < disk_size)))]) ++
                            flush_txns_finished_oracle_is
                              (records (current_part hdr))) ++
                         OpToken
                           (HorizontalComposition (CacheOperation addr_dec value)
                              CryptoDiskOperation)
                           (Token1 (CacheOperation addr_dec value)
                              CryptoDiskOperation Cont)
                         :: map transform_token o' ++
                            [LayerImplementation.Crash
                               (HorizontalComposition (CacheOperation addr_dec value)
                                  CryptoDiskOperation)] /\
                  commit_finished_oracle_is_true o' len) \/
                (exists o1 o2, o = OpToken
                (HorizontalComposition
                   (CacheOperation addr_dec value)
                   CryptoDiskOperation)
                (Token2 (CacheOperation addr_dec value)
                   CryptoDiskOperation
                   (Token2 CryptoOperation
                      (DiskOperation addr_dec value
                         (fun a : addr => a < disk_size))
                      DiskLayer.Cont))
              :: LayerImplementation.Cont
                   (HorizontalComposition
                      (CacheOperation addr_dec value)
                      CryptoDiskOperation)
                 :: LayerImplementation.Cont
                      (HorizontalComposition
                         (CacheOperation addr_dec value)
                         CryptoDiskOperation)
                    :: OpToken
                         (HorizontalComposition
                            (CacheOperation addr_dec value)
                            CryptoDiskOperation)
                         (Token2 (CacheOperation addr_dec value)
                            CryptoDiskOperation
                            (Token2 CryptoOperation
                               (DiskOperation addr_dec value
                                  (fun a : addr => a < disk_size))
                               DiskLayer.Cont))
                       :: LayerImplementation.Cont
                            (HorizontalComposition
                               (CacheOperation addr_dec value)
                               CryptoDiskOperation)
                          :: (map
                                (fun
                                   o : LayerImplementation.token'
                                         CryptoDiskOperation =>
                                 match o with
                                 | OpToken _ o1 =>
                                     OpToken
                                       (HorizontalComposition
                                          (CacheOperation addr_dec
                                             value)
                                          CryptoDiskOperation)
                                       (Token2
                                          (CacheOperation addr_dec
                                             value)
                                          CryptoDiskOperation o1)
                                 | LayerImplementation.Crash _ =>
                                     LayerImplementation.Crash
                                       (HorizontalComposition
                                          (CacheOperation addr_dec
                                             value)
                                          CryptoDiskOperation)
                                 | LayerImplementation.Cont _ =>
                                     LayerImplementation.Cont
                                       (HorizontalComposition
                                          (CacheOperation addr_dec
                                             value)
                                          CryptoDiskOperation)
                                 end)
                                ((BatchOperations.rec_oracle_finished_disk
                                    (count (current_part hdr)) ++
                                  (BatchOperations.rec_oracle_finished_crypto
                                     (count (current_part hdr)) ++
                                   [LayerImplementation.Cont
                                      (HorizontalComposition
                                         CryptoOperation
                                         (DiskOperation addr_dec
                                            value
                                            (fun a : addr =>
                                             a < disk_size)))]) ++
                                  [LayerImplementation.Cont
                                     (HorizontalComposition
                                        CryptoOperation
                                        (DiskOperation addr_dec value
                                           (fun a : addr =>
                                            a < disk_size)))]) ++
                                 flush_txns_finished_oracle_is
                                   (records (current_part hdr))) ++
                              OpToken
                                (HorizontalComposition
                                   (CacheOperation addr_dec value)
                                   CryptoDiskOperation)
                                (Token1
                                   (CacheOperation addr_dec value)
                                   CryptoDiskOperation Cont)
                              :: map
                                   (fun
                                      o : LayerImplementation.token'
                                            CryptoDiskOperation =>
                                    match o with
                                    | OpToken _ o1 =>
                                        OpToken
                                          (HorizontalComposition
                                             (CacheOperation addr_dec
                                                value)
                                             CryptoDiskOperation)
                                          (Token2
                                             (CacheOperation addr_dec
                                                value)
                                             CryptoDiskOperation o1)
                                    | LayerImplementation.Crash _ =>
                                        LayerImplementation.Crash
                                          (HorizontalComposition
                                             (CacheOperation addr_dec
                                                value)
                                             CryptoDiskOperation)
                                    | LayerImplementation.Cont _ =>
                                        LayerImplementation.Cont
                                          (HorizontalComposition
                                             (CacheOperation addr_dec
                                                value)
                                             CryptoDiskOperation)
                                    end) o1 ++
                                 [LayerImplementation.Cont
                                    (HorizontalComposition
                                       (CacheOperation addr_dec value)
                                       CryptoDiskOperation)]) ++ o2 /\
                                       commit_finished_oracle_is_true o1 len /\
                                       (exists n, write_batch_to_cache_crashed_oracle_is o2 n))).

Definition write_crashed_oracle_is_5 o hdr :=
(o = OpToken
    (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
    (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
       (Token2 CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size))
          DiskLayer.Cont))
  :: LayerImplementation.Cont
       (HorizontalComposition (CacheOperation addr_dec value)
          CryptoDiskOperation)
     :: LayerImplementation.Cont
          (HorizontalComposition (CacheOperation addr_dec value)
             CryptoDiskOperation)
        :: OpToken
             (HorizontalComposition (CacheOperation addr_dec value)
                CryptoDiskOperation)
             (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
                (Token2 CryptoOperation
                   (DiskOperation addr_dec value
                      (fun a : addr => a < disk_size)) DiskLayer.Cont))
           :: LayerImplementation.Cont
                (HorizontalComposition (CacheOperation addr_dec value)
                   CryptoDiskOperation)
              :: map
                   (fun o : LayerImplementation.token' CryptoDiskOperation =>
                    match o with
                    | OpToken _ o1 =>
                        OpToken
                          (HorizontalComposition
                             (CacheOperation addr_dec value)
                             CryptoDiskOperation)
                          (Token2 (CacheOperation addr_dec value)
                             CryptoDiskOperation o1)
                    | LayerImplementation.Crash _ =>
                        LayerImplementation.Crash
                          (HorizontalComposition
                             (CacheOperation addr_dec value)
                             CryptoDiskOperation)
                    | LayerImplementation.Cont _ =>
                        LayerImplementation.Cont
                          (HorizontalComposition
                             (CacheOperation addr_dec value)
                             CryptoDiskOperation)
                    end)
                   ((BatchOperations.rec_oracle_finished_disk
                       (count (current_part hdr)) ++
                     (BatchOperations.rec_oracle_finished_crypto
                        (count (current_part hdr)) ++
                      [LayerImplementation.Cont
                         (HorizontalComposition CryptoOperation
                            (DiskOperation addr_dec value
                               (fun a : addr => a < disk_size)))]) ++
                     [LayerImplementation.Cont
                        (HorizontalComposition CryptoOperation
                           (DiskOperation addr_dec value
                              (fun a : addr => a < disk_size)))]) ++
                    flush_txns_finished_oracle_is (records (current_part hdr))) ++
                 [OpToken
                    (HorizontalComposition (CacheOperation addr_dec value)
                       CryptoDiskOperation)
                    (Token1 (CacheOperation addr_dec value) CryptoDiskOperation
                       Crash)]).

Theorem write_crashed_oracle:
  forall merged_disk s o al vl s' u hdr txns,
  let c1 := length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl) in
  let c2 := count (current_part hdr) in
  let c3 := fold_left Nat.add (map (fun txnr => (addr_count txnr) * 2 + (data_count txnr) * 4 + 3) (records (current_part hdr))) 0 in
  (fst s = Mem.list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
  log_header_rep hdr txns (snd s) /\
  merged_disk = total_mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))) /\
  (forall a, a >= data_start -> snd ((snd (snd s)) a) = [])) ->
  exec CachedDiskLang u o s (write al vl) (Crashed s') ->
  (cached_log_rep merged_disk s' /\ 
    (
      o = [LayerImplementation.Crash CachedDiskOperation] \/ 

      (exists o', 
      o = map transform_token o' /\
      commit_crashed_oracle_is_1 o' (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
  
      (count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length /\
        write_crashed_oracle_is_1 o hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))
      )
    )
  ) \/
  ((
    ((exists txns,
      log_crash_rep (During_Commit_Log_Write txns) (snd s') /\
    merged_disk = total_mem_map fst (shift (plus data_start)
    (list_upd_batch_set (snd (snd s')) (map addr_list txns) (map data_blocks txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s')) a) = []) /\
    (
        ((exists o', 
        o = map transform_token o' /\
        commit_crashed_oracle_is_2 o'
         (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
        count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl <= log_length) \/
    
        (write_crashed_oracle_is_2 o hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
        count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length)
      )) \/

 (exists old_txns new_txn old_hdr new_hdr,
   let txns := old_txns ++ [new_txn] in
    log_crash_rep (During_Commit_Header_Write old_txns txns) (snd s') /\
    (snd (snd s')) hdr_block_num =
    (Log.encode_header new_hdr, [Log.encode_header old_hdr]) /\
    new_hdr <> old_hdr /\
    (upd_batch merged_disk al vl) = total_mem_map fst (shift (plus data_start)
     (list_upd_batch_set (snd (snd s')) (map addr_list txns)
        (map data_blocks txns))) /\

    merged_disk = total_mem_map fst (shift (plus data_start)
     (list_upd_batch_set (snd (snd s')) (map addr_list old_txns)
                         (map data_blocks old_txns))) /\
    (forall a, a >= data_start -> snd ((snd (snd s')) a) = []) /\
    addr_blocks new_txn = addr_list_to_blocks (map (Init.Nat.add data_start) al) /\ data_blocks new_txn = vl /\
    (
        ((exists o', 
        o = map transform_token o' /\
        commit_crashed_oracle_is_3 o'
         (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) /\
        count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl <= log_length /\
        (forall i : nat,
          i < length (addr_list_to_blocks al) + length vl ->
          fst (snd (snd s') (log_start + Log.count (Log.current_part hdr) + i)) =
          seln (map (encrypt (Log.key (Log.record new_txn)))
          (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) i value0 /\
          length (snd (snd (snd s') (log_start + Log.count (Log.current_part hdr) + i))) = 1) /\
          old_hdr = hdr) \/

        (write_crashed_oracle_is_3 o hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
        count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length /\
        (forall i : nat,
          i < length (addr_list_to_blocks al) + length vl ->
          fst (snd (snd s') (log_start + i)) =
          seln (map (encrypt (Log.key (Log.record new_txn)))
          (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))
            i value0 /\ length (snd (snd (snd s') (log_start + i))) = 1) /\
            old_txns = [])
      ))
    ) \/
  
    (cached_log_crash_rep (After_Commit (upd_batch merged_disk al vl)) s' /\
     ((((exists o', 
     o = map transform_token o' /\
     commit_crashed_oracle_is_4 o'
    (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
    (exists o', 
     o = map transform_token o' ++  [LayerImplementation.Crash
     (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)] /\
     commit_finished_oracle_is_true o'
    (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl))) \/
    (exists o1 o2 n, 
     o = map transform_token o1 ++  LayerImplementation.Cont
     (HorizontalComposition (CacheOperation addr_dec value)
        CryptoDiskOperation) :: o2 /\
     commit_finished_oracle_is_true o1
    (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
    write_batch_to_cache_crashed_oracle_is o2 n)) /\
      count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl <= log_length) \/
      
      (write_crashed_oracle_is_4 o hdr (length (addr_list_to_blocks (map (Init.Nat.add data_start) al) ++ vl)) /\
      count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length))) \/
    
    (cached_log_crash_rep (During_Apply merged_disk) s' /\
    ((exists o', 
    o = OpToken
    (HorizontalComposition (CacheOperation addr_dec value) CryptoDiskOperation)
    (Token2 (CacheOperation addr_dec value) CryptoDiskOperation
       (Token2 CryptoOperation
          (DiskOperation addr_dec value (fun a : addr => a < disk_size))
          DiskLayer.Cont))
  :: LayerImplementation.Cont
       (HorizontalComposition (CacheOperation addr_dec value)
          CryptoDiskOperation)
     :: LayerImplementation.Cont
          (HorizontalComposition (CacheOperation addr_dec value)
             CryptoDiskOperation)
        :: map transform_token o' /\
    (apply_log_crashed_oracle_is_3 o' hdr \/ exists n, apply_log_crashed_oracle_is_1 o' hdr n))) /\
    count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length) \/
    
    (cached_log_crash_rep (After_Apply merged_disk) s' /\ 
    write_crashed_oracle_is_5 o hdr /\
    count (current_part hdr) + length (addr_list_to_blocks 
        (map (Init.Nat.add data_start) al)) + length vl > log_length)
   ) /\
  
   Forall (fun a => a < data_length) al /\
   NoDup al /\
   length al = length vl /\
   length (addr_list_to_blocks (map (plus data_start) al)) + length vl <= log_length).
Proof.
  unfold write_crashed_oracle_is_1, 
  write_crashed_oracle_is_2, 
  write_crashed_oracle_is_3, 
  write_crashed_oracle_is_4, 
  write_crashed_oracle_is_5, 
  cached_log_rep, write; simpl; intros.
  cleanup; invert_exec.
  {
    split_ors; cleanup; repeat invert_exec.
    {
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_crashed_oracle in H4; eauto.
      {
        repeat (split_ors; cleanup);
        repeat cleanup_pairs; eauto.
        {
          left; eexists; intuition eauto.
        }
        {
          right; repeat (split; eauto).
          left; unfold cached_log_crash_rep; simpl.
          intuition eauto.
          left; eexists; intuition eauto.

          assert (A: map addr_list txns =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start)) (map addr_list txns))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H16; eauto.
            unfold txn_well_formed, record_is_valid in H16; logic_clean.
            eapply Forall_forall in H21; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          {
            apply shift_eq_after.
            intros; lia.
            intros; apply H4; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x1 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x1) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x1 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x1) (data_start + y)); eauto; lia.
          }
          {
            rewrite H4; eauto.
          }
        }
        {
          right; intuition eauto.
          left; unfold cached_log_crash_rep; simpl.
          intuition eauto.
          right; do 4 eexists; intuition eauto.
          {
            clear H7 H12.
            assert (A: map addr_list (txns++[x1]) =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list (txns++[x1])))). {
              repeat rewrite map_map; simpl.
              setoid_rewrite map_ext_in at 2.
              eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H25; eauto.
            unfold txn_well_formed, record_is_valid in H25; logic_clean.
            eapply Forall_forall in H30; eauto; lia.
          }
          assert (A0: map addr_list txns =
                      map (map (Init.Nat.add data_start))
                          (map (map (fun a => a - data_start))
                               (map addr_list txns))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H25; eauto.
            unfold txn_well_formed, record_is_valid in H25; logic_clean.
            eapply Forall_forall in H30; eauto; lia.
          }
          rewrite A, A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite total_mem_map_fst_upd_batch_set.
          unfold log_crash_rep in *; simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in H16; logic_clean.
          eapply forall_app_l in H21.
          simpl in *.
          inversion H21; subst.
          unfold txn_well_formed in H24; logic_clean.
          rewrite H26, H0, H5 in *.
          rewrite firstn_app2.
          replace (map (fun a : nat => a - data_start) (map (Init.Nat.add data_start) al)) with al; eauto.

          {
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            rewrite map_id; eauto.
            intros; simpl.
            lia.
          }
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          apply shift_eq_after.
          intros; lia.
          intros; apply H8; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x3 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x3 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
          }
        }
          {
           clear H7 H12.
           assert (A0: map addr_list txns =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list txns))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H25; eauto.
            unfold txn_well_formed, record_is_valid in H25; logic_clean.
            eapply Forall_forall in H30; eauto; lia.
          }
          rewrite A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.

          apply shift_eq_after.
          intros; lia.
          intros; apply H8; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x3 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x3 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
          }
          }
          {
            rewrite H8; eauto.
          }
          {
            clear H7 H12.
            left.
            repeat (split; eauto).
            edestruct H11.
            erewrite addr_list_to_blocks_length_eq; eauto.
            rewrite map_length; eauto.
            eauto.
            edestruct H11.
            erewrite addr_list_to_blocks_length_eq; eauto.
            rewrite map_length; eauto.
            eauto.
          }
        }
        {
          right; intuition eauto.
          right; left; unfold cached_log_crash_rep; simpl.
          intuition eauto.
          eexists; intuition eauto.
          
          assert (A: map addr_list (txns++[x1]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (txns++[x1])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H16; eauto.
            unfold txn_well_formed, record_is_valid in H16; logic_clean.
            eapply Forall_forall in H20; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H14.
          simpl in *.
          inversion H14; subst.
          unfold txn_well_formed in H17; logic_clean.
          rewrite H17, H0, H5 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H7; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            rewrite H7; simpl; eauto.
          }
        }
      }
      all: try rewrite H5, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H6; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H5, app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        apply map_length.
      }
    }
    {
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_finished_oracle in H5; eauto.
      split_ors; cleanup; try congruence.
      {
        split_ors; cleanup; repeat invert_exec;
        repeat cleanup_pairs.
        {
          right; intuition eauto;
          right; left; unfold cached_log_crash_rep; simpl.
          intuition eauto.
          eexists; intuition eauto.
          
          assert (A: map addr_list (txns++[x1]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (txns++[x1])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H16; eauto.
            unfold txn_well_formed, record_is_valid in H16; logic_clean.
            eapply Forall_forall in H20; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) 
          with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H14.
          simpl in *.
          inversion H14; subst.
          unfold txn_well_formed in H17; logic_clean.
          rewrite H17 in *.
          rewrite H6, H0 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H9; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
          }
          {
            rewrite H9; simpl; eauto.
          }
          {
            left; intuition eauto.
            rewrite app_length in *; lia.
          }
        }
        {
          eapply write_batch_to_cache_crashed_oracle in H7.
          simpl in *; cleanup.
          right; intuition eauto.
          right; left; unfold cached_log_crash_rep; simpl.
          intuition eauto.
          eexists; intuition eauto.
          
          assert (A: map addr_list (txns++[x1]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (txns++[x1])))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H18; eauto.
            unfold txn_well_formed, record_is_valid in H18; logic_clean.
            eapply Forall_forall in H22; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- total_mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          repeat rewrite total_mem_map_shift_comm.
          repeat rewrite total_mem_map_fst_upd_batch_set.
          repeat rewrite total_mem_map_fst_list_upd_batch_set.
          rewrite total_mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H16.
          simpl in *.
          inversion H16; subst.
          unfold txn_well_formed in H19; logic_clean.
          rewrite H19, H6, H0 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H9; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            rewrite H9; simpl; eauto.
          }
          {
            simpl.
            left; intuition.
            right; right; 
            do 3 eexists; intuition eauto.
            rewrite app_length in *; lia.
          }
        }
      }
      all: try rewrite H0, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H6; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H0, app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        apply map_length.
      }
    }
    {
      eapply commit_finished_oracle in H5; eauto.
      {
        split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        split_ors; cleanup; repeat invert_exec.
        {
          split_ors; cleanup; repeat invert_exec.
          {(** Apply log crahed **)
            simpl in *;
            eapply apply_log_crashed_oracle in H2; eauto.
            cleanup; split_ors; cleanup; repeat cleanup_pairs.
             {
               left; unfold cached_log_rep; simpl.
               eexists; intuition eauto.
               right; right; split; eauto.
               rewrite app_length in *; lia.
             }
             {               
               split_ors; cleanup.
               {
                 right; intuition eauto.
                 right; right; left; intuition eauto.
                 eexists; intuition eauto.
                 unfold log_rep, log_header_rep, log_rep_general, 
                 log_rep_explicit, log_crash_rep,
                 log_rep_inner, txns_valid, header_part_is_valid in *; 
                 simpl in *; logic_clean.
                 rewrite <- H24.
                 repeat erewrite RepImplications.bimap_get_addr_list; eauto.
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 repeat rewrite total_mem_map_fst_upd_batch_set.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 extensionality a.
                 unfold shift; simpl.
                 destruct (list_list_in_EXM addr_dec (map addr_list txns) (data_start + a)); 
                 try logic_clean.
                 eapply list_upd_batch_in; eauto.
                 eexists; split; eauto.
                 apply in_seln; eauto.

                 apply forall_forall2.
                 apply Forall_forall; intros.
                 rewrite <- combine_map in H33.
                 apply in_map_iff in H33; logic_clean.
                 eapply Forall_forall in H13; eauto.
                 unfold txn_well_formed in H13; logic_clean; eauto.
                 destruct x8; simpl in *.
                 inversion H33; subst.
                 simpl. 
                 rewrite H37, <- H41, firstn_length_l; eauto. 
                 repeat rewrite map_length; eauto.
                 
                 repeat rewrite list_upd_batch_not_in; eauto.
                 rewrite upd_batch_ne.
                 rewrite list_upd_batch_not_in; eauto.
                 intros.
                 apply in_firstn_in in H31; eauto.
                 intros Hx.
                 apply in_firstn_in in Hx; eauto.
                 eapply H30; eauto.
                 apply in_seln; eauto.
                 destruct (lt_dec x0 (length (map addr_list txns))); eauto.
                 rewrite seln_oob in Hx; eauto.
                 simpl in *; intuition.
                 lia.
                 rewrite map_length; eauto.

                 unfold log_rep, log_header_rep, log_rep_general, 
                 log_rep_explicit, log_crash_rep,
                 log_rep_inner, txns_valid, header_part_is_valid in *; 
                 simpl in *; logic_clean.
                 rewrite <- H26.
                 erewrite RepImplications.bimap_get_addr_list; eauto.
                 rewrite upd_batch_set_ne; eauto.
                 rewrite list_upd_batch_set_not_in; eauto.
                 intros.
                 apply in_firstn_in in H32; eauto.
                 intros Hx.
                 apply in_firstn_in in Hx; eauto.
                 eapply H7; eauto.
                 eexists; split; eauto. 
                 apply in_seln; eauto.
                 destruct (lt_dec x0 (length (map addr_list txns))); eauto.
                 rewrite seln_oob in Hx; eauto.
                 simpl in *; intuition.
                 lia.
                 repeat rewrite map_length; eauto.
                 {
                   rewrite app_length in *; lia.
                 }
               }
               split_ors; cleanup.
               {
                 left; intuition eauto.
                 unfold cached_log_rep; simpl.
                 eexists; intuition eauto.
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite total_mem_map_fst_sync_noop.
                 rewrite total_mem_map_fst_list_upd_batch_set.
                 unfold log_header_rep, log_rep_general, 
                 log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H12.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite TotalMem.list_upd_batch_noop; eauto.
                 eapply log_rep_forall2_txns_length_match; eauto.
                 eapply log_rep_forall2_txns_length_match; eauto.
                 eauto.
                 rewrite map_length; eauto.
                 {
                  repeat rewrite app_length;
                  repeat rewrite map_length.
                  right; right; intuition eauto.
                  rewrite app_length in *; lia.
                 }
               }
               {
                 simpl in *.
                 cleanup; simpl in *.
                 right; intuition eauto.
                 right; right; left; unfold cached_log_rep; simpl in *.
                 intuition eauto.
                 eexists; intuition eauto.
                 left; intuition eauto.
                 {
                  assert (A: Forall2
                  (fun (l_a : list addr) (l_v : list value) =>
                   length l_a = length l_v) (map addr_list txns) 
                  (map data_blocks txns)). {
                    eapply log_rep_forall2_txns_length_match; eauto.
                    unfold log_rep; eauto.
                  }
                  unfold log_header_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                  rewrite <- H12.
                  erewrite RepImplications.bimap_get_addr_list.
                  4: eauto.
                   repeat rewrite total_mem_map_shift_comm.
                    repeat rewrite total_mem_map_fst_list_upd_batch_set.
                    repeat rewrite total_mem_map_fst_upd_set.
                    rewrite total_mem_map_fst_sync_noop.
                    rewrite total_mem_map_fst_list_upd_batch_set.
                    rewrite list_upd_batch_upd_comm.
                    rewrite TotalMem.list_upd_batch_noop; eauto.
                    unfold not; intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   apply in_map_iff in H14; cleanup.
                   eapply Forall_forall in H13; eauto.
                   unfold txn_well_formed in H13; cleanup.
                   eapply Forall_forall in H21; eauto.
                   lia.
                    eauto.
                    rewrite map_length; eauto.
                 }
                 {
                   rewrite upd_set_ne; simpl; eauto.
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
                 repeat rewrite total_mem_map_shift_comm.
                 repeat rewrite total_mem_map_fst_list_upd_batch_set.
                 rewrite total_mem_map_fst_upd_set.
                 rewrite total_mem_map_fst_sync_noop.
                 rewrite total_mem_map_fst_list_upd_batch_set.
                 setoid_rewrite <- shift_upd_noop at 6.
                 rewrite upd_list_upd_batch_upd_noop.
                 setoid_rewrite shift_upd_noop.
                 unfold log_header_rep, log_rep_general, log_rep_explicit,
                 log_rep_inner, txns_valid in *; simpl in *; logic_clean.
                 rewrite <- H12.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite TotalMem.list_upd_batch_noop; eauto.
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H14.
                   apply in_map_iff in H14; cleanup.
                   simpl.
                   eapply Forall_forall in H15; eauto.
                   unfold txn_well_formed in H15; logic_clean.
                   rewrite H16.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H14.
                   apply in_map_iff in H14; cleanup.
                   simpl.
                   eapply Forall_forall in H15; eauto.
                   unfold txn_well_formed in H15; logic_clean.
                   rewrite H16.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 eauto.
                 rewrite map_length; eauto.
                 {
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
                 {                   
                   unfold log_header_rep, log_rep_general, log_rep_explicit,
                   log_rep_inner, txns_valid in *; logic_clean.
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H14.
                   apply in_map_iff in H14; cleanup.
                   simpl.
                   eapply Forall_forall in H15; eauto.
                   unfold txn_well_formed in H15; logic_clean.
                   rewrite H16.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
                 {
                   rewrite upd_set_ne.
                   simpl; eauto.
                   intros; pose proof hdr_before_log.
                   pose proof data_start_where_log_ends.
                   lia.
                 }
                 {
                  rewrite app_length in *; lia.
                 }
               }
             }
          }
          eapply apply_log_finished_oracle in H4; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs.
          split_ors; cleanup.
          {(** Flush Crashed **)
            repeat invert_exec.            
             {
               right; intuition eauto.
               right; right; right; unfold cached_log_rep; simpl.
               intuition eauto.
               rewrite <- sync_shift_comm.
               rewrite shift_upd_set_noop.
               rewrite total_mem_map_fst_sync_noop; eauto.
               {
                 intros; pose proof hdr_before_log.
                 pose proof data_start_where_log_ends.
                 lia.
               }
               {
                 rewrite app_length in *; try lia.
               }
             }
          }
          repeat invert_exec.
          split_ors; cleanup; repeat invert_exec.
          { (** Second commit crashed **)
            simpl in *.
            unfold log_rep in *; cleanup.
            destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
            eapply commit_crashed_oracle in H2; eauto.
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              left; intuition eauto.
              eexists; intuition eauto.
              simpl; eauto.
              simpl.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              {
                repeat rewrite app_length;
                repeat rewrite map_length.
                right; right; intuition eauto.
                rewrite app_length in *; lia.
                right; simpl.
                rewrite app_length in *;
                repeat rewrite map_length.
                intuition eauto; try lia.
              }
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; intuition eauto.
              left; intuition eauto.
              left; eexists; intuition eauto.
              simpl.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
                  (encode_header (update_hdr hdr header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H2; lia.
              rewrite H2; simpl; eauto.
              {
                repeat rewrite app_length in *;
                simpl in *; 
                repeat rewrite map_length in *;
                simpl in *.
                right; intuition eauto; try lia.
              }
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; intuition eauto.
              left; intuition eauto.
              right; do 4 eexists; intuition eauto.
              instantiate (2:= []).
              simpl; eauto.
              simpl.
              replace (addr_list x2) with (map (Init.Nat.add data_start) al).           
              rewrite shift_upd_batch_set_comm.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
            (encode_header (update_hdr hdr header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H10; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x4 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
              }
              {
                unfold log_crash_rep in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H22; cleanup.
                inversion H27; cleanup.
                unfold txn_well_formed in H30; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              {
                simpl.
                rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
            (encode_header (update_hdr hdr header_part0)))).
                rewrite <- sync_shift_comm.
                rewrite shift_upd_set_noop.
                repeat rewrite total_mem_map_fst_sync_noop; eauto.
                {
                  intros; pose proof hdr_before_log.
                  pose proof data_start_where_log_ends.
                  lia.
                }
                intros; lia.
                intros; apply H10; lia.
              }
              rewrite H10; simpl; eauto.
              {
                repeat rewrite app_length in *;
                simpl in *; 
                repeat rewrite map_length in *;
                simpl in *.
                unfold log_rep_general, 
                log_rep_explicit, log_rep_inner,
                txns_valid,
                header_part_is_valid in H7;
                cleanup; simpl in *.
                rewrite <- H20 in *; simpl in *.
                repeat rewrite Nat.add_0_r in *.
                right; intuition eauto; try lia.
                edestruct H13.
                erewrite addr_list_to_blocks_length_eq; eauto.
                rewrite map_length; eauto.
                eauto.
                edestruct H13.
                erewrite addr_list_to_blocks_length_eq; eauto.
                rewrite map_length; eauto.
                eauto.
              }
             }
            {
              right; intuition eauto.
              right; left; intuition eauto.
              eexists; intuition eauto.
              simpl.
              replace (addr_list x2) with (map (Init.Nat.add data_start) al).
              rewrite shift_upd_batch_set_comm.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
                     (encode_header (update_hdr hdr header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H9; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x3 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H16; cleanup.
                inversion H16; cleanup.
                unfold txn_well_formed in H25; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H9; simpl; eauto.
              {
                repeat rewrite app_length in *;
                simpl in *; 
                repeat rewrite map_length in *;
                simpl in *.
                right; intuition eauto; try lia.
              }
            }
            all: try rewrite H, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H8; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H, app_length, map_length; lia.
            }
            {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        apply map_length.
      }
          }
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          eapply commit_finished_oracle in H2; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H0.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list txns) 
            (map data_blocks txns) hdr_block_num); simpl in *.
            destruct x; simpl in *; cleanup.
            rewrite encode_decode_header, app_length in H2; simpl in *;
            lia.
          }
          {
            right; intuition eauto.
            right; left; unfold cached_log_crash_rep; simpl.
            intuition eauto.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x1) with 
            (map (Init.Nat.add data_start) al).
            rewrite shift_upd_batch_set_comm.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
                     (encode_header (update_hdr hdr header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H10; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x0 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H16; cleanup.
                inversion H16; cleanup.
                unfold txn_well_formed in H25; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H10; simpl; eauto.
              {
                repeat (repeat rewrite app_length in *;
                simpl in *; 
                repeat rewrite map_length in *;
                simpl in * ).
                right; intuition eauto; try lia.
              }
            }
            all: try rewrite H8, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H9; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H8, app_length, map_length; lia.
            }
            {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        apply map_length.
      }
        }
        {(** write_batch_to_cache_crashed **)
          eapply apply_log_finished_oracle in H5; eauto.
          simpl in *; cleanup.
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          simpl in *; repeat cleanup_pairs; simpl in *.
          eapply commit_finished_oracle in H7; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H0.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns) hdr_block_num); simpl in *;
            destruct x; simpl in *; cleanup.
            rewrite encode_decode_header, app_length in H5; simpl in *;
            lia.
          }
          eapply write_batch_to_cache_crashed_oracle in H2; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs; simpl in *.
          {
            right; intuition eauto.
            right; left; unfold cached_log_crash_rep; simpl.
            intuition eauto.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x) with (map (Init.Nat.add data_start) al).
            rewrite shift_upd_batch_set_comm.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list txns) (map data_blocks txns)) hdr_block_num
                     (encode_header (update_hdr hdr header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite total_mem_map_fst_upd_batch_set.
              repeat rewrite total_mem_map_fst_sync_noop; eauto.              
              
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H11; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x5 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x5) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H17; cleanup.
                inversion H17; cleanup.
                unfold txn_well_formed in H26; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              rewrite H11; simpl; eauto.
              {
                right; simpl.
                repeat (repeat rewrite app_length in *;
                simpl in *; 
                repeat rewrite map_length in *;
                simpl in * ).
                intuition eauto; try lia.
                right; right.
                do 2 eexists; intuition eauto.
              }
            }
            all: try rewrite H10, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H0; cleanup_no_match.
              eapply_fresh Forall_forall in f; eauto.
              pose proof data_fits_in_disk.
              split; try lia.
            }
            {
              rewrite H10, app_length, map_length; lia.
            }
            {
              erewrite addr_list_to_blocks_length_eq.
              eapply addr_list_to_blocks_length_nonzero; eauto.
              apply map_length.
            }
        }
      }
      all: destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      all: try rewrite H0, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H6; cleanup_no_match.
        eapply_fresh Forall_forall in f; eauto.
        pose proof data_fits_in_disk.
        split; try lia.
      }
      {
        rewrite H0, app_length, map_length; lia.
      }
      {
        erewrite addr_list_to_blocks_length_eq.
        eapply addr_list_to_blocks_length_nonzero; eauto.
        apply map_length.
      }
    }
  }
  all:left; simpl; intuition eauto; try lia;
    unfold log_rep; eexists; intuition eauto.
  Unshelve.
  apply value0.
Qed.

Theorem write_crashed:
  forall merged_disk s o al vl s' u,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang u o s (write al vl) (Crashed s') ->
  cached_log_rep merged_disk s' \/
  ((cached_log_crash_rep (During_Commit merged_disk (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (After_Commit (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (During_Apply merged_disk) s' \/
  cached_log_crash_rep (After_Apply merged_disk) s') /\
   Forall (fun a => a < data_length) al /\
   NoDup al /\
   length al = length vl /\
   length (addr_list_to_blocks (map (plus data_start) al)) + length vl <= log_length).
Proof.
  unfold cached_log_rep, log_rep; intros; logic_clean.
  eapply write_crashed_oracle in H0; unfold log_header_rep; eauto.
  cleanup; intuition eauto.
  right. intuition eauto. left.
  unfold cached_log_crash_rep; intuition eauto.
  left. cleanup; eauto.
  right. intuition eauto. left.
  unfold cached_log_crash_rep; intuition eauto.
  right. cleanup; do 2 eexists; eauto.
Qed.

