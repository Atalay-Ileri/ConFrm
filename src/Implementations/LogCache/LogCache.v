Require Import Lia Datatypes PeanoNat Compare_dec Framework FSParameters Log Log.Specs.
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

(* Converts to disk address before writing to log *)
Definition write  addr_l (data_l: list value) :=
  if (NoDup_dec addr_l) then
    if (Nat.eq_dec (length addr_l) (length data_l)) then
      if (le_dec (length (addr_list_to_blocks (map (plus data_start) addr_l)) + length data_l) log_length) then
           
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
Inductive Cached_Log_Crash_State:=
| During_Commit (old_merged_disk new_merged_disk : disk value) : Cached_Log_Crash_State
| After_Commit (new_merged_disk : disk value) : Cached_Log_Crash_State
| During_Apply (merged_disk : disk value) : Cached_Log_Crash_State
| After_Apply (merged_disk : disk value) : Cached_Log_Crash_State
| During_Recovery (merged_disk : disk value) : Cached_Log_Crash_State.

Definition cached_log_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    fst s = list_upd_batch empty_mem (map addr_list txns) (map data_blocks txns) /\
    log_rep txns (snd s) /\
    merged_disk = mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))).

Definition cached_log_crash_rep cached_log_crash_state (s: Language.state CachedDiskLang) :=
  match cached_log_crash_state with
  | During_Commit old_merged_disk new_merged_disk =>
    (exists txns,
       log_crash_rep (During_Commit_Log_Write txns) (snd s) /\
       old_merged_disk = mem_map fst (shift (plus data_start)
       (list_upd_batch (sync (snd (snd s))) (map addr_list txns)
                       (map (map (fun vs => (vs, []))) (map data_blocks txns))))) \/
    (exists old_txns txns,
       log_crash_rep (During_Commit_Header_Write old_txns txns) (snd s) /\
       new_merged_disk = mem_map fst (shift (plus data_start)
        (list_upd_batch (sync (snd (snd s))) (map addr_list txns)
          (map (map (fun vs => (vs, []))) (map data_blocks txns)))) /\
       old_merged_disk = mem_map fst (shift (plus data_start)
        (list_upd_batch (sync (snd (snd s))) (map addr_list old_txns)
                        (map (map (fun vs => (vs, []))) (map data_blocks old_txns)))))
  | After_Commit new_merged_disk =>
    exists txns,
    log_rep txns (snd s) /\
     new_merged_disk = mem_map fst (shift (plus data_start)
        (list_upd_batch (sync (snd (snd s))) (map addr_list txns)
                        (map (map (fun vs => (vs, []))) (map data_blocks txns))))

  | During_Apply merged_disk =>
    exists txns,
    log_crash_rep (Log.During_Apply txns) (snd s) /\
     merged_disk = mem_map fst (shift (plus data_start)
        (list_upd_batch (sync (snd (snd s))) (map addr_list txns)
                        (map (map (fun vs => (vs, []))) (map data_blocks txns))))

  | After_Apply merged_disk =>
    log_rep [] (snd s) /\
      merged_disk = mem_map fst (shift (plus data_start) (snd (snd s)))
   
  | During_Recovery merged_disk =>
    exists txns,
    log_crash_rep (Log.During_Recovery txns) (snd s) /\
    merged_disk = mem_map fst (shift (plus data_start)
        (list_upd_batch_set (snd (snd s)) (map addr_list txns)
                            (map data_blocks txns)))

     
    end.

Definition cached_log_reboot_rep merged_disk (s: Language.state CachedDiskLang) :=
  exists txns,
    fst s = empty_mem /\
    log_reboot_rep txns (snd s) /\
    merged_disk = mem_map fst (shift (plus data_start) (list_upd_batch_set (snd (snd s)) (map addr_list txns) (map data_blocks txns))).




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

(*
Lemma crash_to_reboot_rep:
  forall new s selector,
    cached_log_crash_rep new s ->

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
*)


Lemma list_upd_batch_app:
      forall A AEQ V l1 l2 l3 l4 (m: @mem A AEQ V),
        length l1 = length l3 ->
        list_upd_batch m (l1++l2) (l3++l4) = list_upd_batch (list_upd_batch m l1 l3) l2 l4.
Proof.
  induction l1; destruct l3; simpl; intros; eauto; lia.
Qed.

Lemma list_upd_batch_set_app:
  forall A AEQ V l1 l2 l3 l4 (m: @mem A AEQ (V * list V)),
    length l1 = length l3 ->
    list_upd_batch_set m (l1++l2) (l3++l4) = list_upd_batch_set (list_upd_batch_set m l1 l3) l2 l4.
Proof.
  induction l1; destruct l3; simpl; intros; eauto; lia.
Qed.

Lemma shift_upd_batch_comm:
  forall A AEQ V f l1 l2 (m: @mem A AEQ V),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    upd_batch (shift f m) l1 l2 = shift f (upd_batch m (map f l1) l2).
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite upd_shift_comm; eauto.
Qed.

Lemma shift_eq_after:
  forall V (m1 m2: @mem addr addr_dec V) f,
    (forall a, f a >= f 0)  ->
    (forall a, a >= f 0 -> m1 a = m2 a) ->
    shift f m1 = shift f m2.
Proof.
  unfold shift; intros; extensionality x; eauto.
Qed.


Lemma shift_upd_set_comm:
  forall A AEQ V f a v (m: @mem A AEQ (V * list V)),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (upd_set m (f a) v) =
    upd_set (shift f m) a v.
Proof.
  unfold sumbool_agree, upd_set, shift; simpl; intros; eauto.
  extensionality x; simpl.
  specialize (H x a).
  destruct (AEQ x a); subst.
  destruct (AEQ (f a) (f a)); subst; intuition eauto.        
  destruct (AEQ (f x) (f a)); intuition eauto.
Qed.

Lemma shift_upd_batch_set_comm:
  forall A AEQ V f l1 l2 (m: @mem A AEQ (V * list V)),
    
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (upd_batch_set m (map f l1) l2) =
    upd_batch_set (shift f m) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite IHl1; eauto.
  rewrite shift_upd_set_comm; eauto.
Qed.

Lemma shift_list_upd_batch_set_comm:
  forall A AEQ V f l1 l2 (m: @mem A AEQ (V * list V)),
    (forall x y : A, sumbool_agree (AEQ x y) (AEQ (f x) (f y))) ->
    shift f (list_upd_batch_set m (map (map f) l1) l2) =
    list_upd_batch_set (shift f m) l1 l2.
Proof.
  induction l1; destruct l2; simpl; intros; eauto.
  rewrite IHl1; eauto.
  rewrite shift_upd_batch_set_comm; eauto.
Qed.

Lemma shift_upd_noop:
  forall A AEQ V f (m: @mem A AEQ V) a v,
    (forall a', f a' <> a) ->
    shift f (upd m a v) = shift f m.
Proof.
  unfold shift, upd; intros.
  extensionality x.
  destruct (AEQ (f x) a); eauto; congruence.
Qed.

Lemma shift_upd_set_noop:
  forall A AEQ V f (m: @mem A AEQ (V * list V)) a v,
    (forall a', f a' <> a) ->
    shift f (upd_set m a v) = shift f m.
Proof.
  unfold shift, upd_set; intros.
  extensionality x.
  destruct (AEQ (f x) a); eauto; congruence.
Qed.

Lemma mem_map_shift_comm:
  forall A AEQ V1 V2 (f: V1 -> V2) s (m: @mem A AEQ V1),
    mem_map f (shift s m) = shift s (mem_map f m).
Proof.
  unfold mem_map, shift; intros; extensionality a.
  eauto.
Qed.

Lemma mem_map_fst_upd_set:
  forall A AEQ V a v (m: @mem A AEQ (V * list V)),
    mem_map fst (upd_set m a v) = upd (mem_map fst m) a v.
Proof.
  unfold upd_set, upd, mem_map; intros; simpl.
  extensionality x.
  destruct (AEQ x a); subst; eauto.
  destruct (m a); eauto.
Qed.

Lemma mem_map_fst_upd_batch_set:
  forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)),
    mem_map fst (upd_batch_set m l_a l_v) = upd_batch (mem_map fst m) l_a l_v.
Proof.
  induction l_a; intros; simpl; eauto.
  destruct l_v; eauto.
  rewrite IHl_a.
  rewrite mem_map_fst_upd_set; eauto.
Qed.

Lemma mem_map_fst_list_upd_batch_set:
  forall A AEQ V l_a l_v (m: @mem A AEQ (V * list V)),
    mem_map fst (list_upd_batch_set m l_a l_v) = list_upd_batch (mem_map fst m) l_a l_v.
Proof.
  induction l_a; intros; simpl; eauto.
  destruct l_v; eauto.
  rewrite IHl_a.
  rewrite mem_map_fst_upd_batch_set; eauto.
Qed.

Lemma mem_map_fst_sync_noop:
  forall A AEQ V (m: @mem A AEQ (V * list V)),
    mem_map fst (sync m) = mem_map fst m.
Proof.
  unfold mem_map, sync; simpl; intros; eauto.
  extensionality x.
  destruct (m x); eauto.
Qed.


Lemma upd_batch_list_upd_batch_app_rev:
  forall A AEQ V (m: @mem A AEQ V) l_l_a l_l_v l_a l_v,
    length l_l_a = length l_l_v ->
    upd_batch (list_upd_batch m l_l_a l_l_v) l_a l_v =
    list_upd_batch m (l_l_a ++ [l_a]) (l_l_v ++ [l_v]).
Proof.
  intros; rewrite list_upd_batch_app ; simpl; eauto.
Qed.

Lemma rev_cons_app:
  forall A (l l': list A) a,
    rev l = a::l' ->
    l = rev l' ++ [a].
Proof.
  induction l; simpl;
  intros; try congruence.

  destruct_fresh (rev l').
  {
    rewrite <- rev_involutive with (l:= l') in H.
    rewrite D in H.
    simpl in *.
    destruct l; simpl in *; eauto.
    assert (AX: length ((rev l ++ [a1]) ++ [a]) = length [a0]). {
      rewrite H; eauto.
    }
    repeat rewrite app_length in *; simpl in *; lia.
  }
  {                         
    rewrite <- rev_involutive with (l:= l') in H.
    rewrite D in H.
    simpl in *.
    rewrite app_comm_cons in H.
    apply app_inj_tail in H; cleanup.
    erewrite IHl.
    rewrite rev_involutive; eauto.
    eauto.
  }
Qed.

Lemma in_split_first:
  forall T (TEQ : forall t t' : T, {t = t'} + {t <> t'})
    (l : list T) (t : T), In t l -> exists l1 l2 : list T, l = l1 ++ t :: l2 /\ ~ In t l1.
  induction l; simpl; intuition.
  subst.
  exists nil, l; simpl; eauto.
  destruct (TEQ a t); subst.
  exists nil, l; simpl; eauto.
  edestruct IHl; eauto; cleanup.
  exists (a::x), x0; simpl; split; eauto.
  intros; intuition eauto.
Qed.

Lemma upd_batch_upd_in_noop:
  forall A AEQ V l_a l_v (m: @mem A AEQ V) a v,
    In a l_a ->
    length l_a = length l_v ->
    upd_batch (upd m a v) l_a l_v =
    upd_batch m l_a l_v.
Proof.
  intros.
  apply in_split_first in H; eauto; cleanup.
  rewrite app_length in *; simpl in *.
  rewrite <- firstn_skipn with (l:= l_v) (n:= length x).
  repeat rewrite upd_batch_app.
  destruct_fresh (skipn (length x) l_v).
  { (** Impossible **)
    apply length_zero_iff_nil in D.
    rewrite skipn_length in D; lia.
  }
  {
    simpl.
    setoid_rewrite upd_batch_upd at 2; eauto.
    rewrite upd_repeat; eauto.
  }
  all: rewrite firstn_length_l; lia.
Qed.

Lemma upd_batch_in_cons_noop:
  forall A AEQ V l_a l_v a v (m: @mem A AEQ V),
    In a l_a ->
    length l_a = length l_v ->
    upd_batch m (a::l_a) (v::l_v) =
    upd_batch m l_a l_v.
Proof.
  induction l_a; simpl; intuition eauto.
  {
    subst; destruct l_v; simpl in *; try lia.
    rewrite upd_repeat; eauto.
  }
  {                           
    subst; destruct l_v; simpl in *; try lia.
    destruct (AEQ a a0); subst.
    rewrite upd_repeat; eauto.
    rewrite upd_comm; eauto.
  }
Qed.

Lemma upd_batch_upd_batch_noop:
  forall A AEQ V l_a l_v1 l_v2 (m: @mem A AEQ V),
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (upd_batch m l_a l_v1) l_a l_v2 =
    upd_batch m l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2; try lia; eauto.
  simpl in *; lia.
  
  destruct (in_dec AEQ a l_a).
  repeat rewrite upd_batch_in_cons_noop; eauto.
  simpl.
  rewrite <- upd_batch_upd; eauto.
  rewrite IHl_a; eauto.
  rewrite upd_repeat; eauto.
Qed.

Lemma upd_upd_batch_app_rev:
  forall A AEQ V (m: @mem A AEQ V) a v l_a l_v,
    length l_a = length l_v ->
    upd (upd_batch m l_a l_v) a v =
    upd_batch m (l_a ++ [a]) (l_v ++ [v]).
Proof.
  intros; rewrite upd_batch_app ; simpl; eauto.
Qed.

Lemma upd_batch_firstn_noop:
  forall A AEQ V l_a l_v (s: @mem A AEQ V) n,
    length l_a = length l_v ->
    upd_batch (upd_batch s (firstn n l_a) (firstn n l_v)) l_a l_v =
    upd_batch s l_a l_v.
Proof.
  intros A AEQ V l_a.
  eapply rev_ind with
      (P:= fun l_a =>
             forall (l_v : list V) (s : mem) (n : nat),
               length l_a = length l_v ->
               upd_batch (upd_batch s (firstn n l_a) (firstn n l_v))
                         l_a l_v = upd_batch s l_a l_v).

  simpl; intros.
  repeat rewrite firstn_nil; simpl; eauto.

  simpl; intros.
  destruct_fresh (rev l_v); simpl; eauto.
  {
    destruct l_v; simpl in *; try congruence.
    repeat rewrite firstn_nil; simpl; eauto.
    destruct (l ++ [x]); simpl.
    destruct (firstn n []); simpl; eauto.
    destruct (firstn n (a :: l0)); simpl; eauto.
    apply app_eq_nil in D; intuition; congruence.
  }
  {                     
    apply rev_cons_app in D.
    cleanup.
    repeat rewrite app_length in *; simpl in *.
    repeat rewrite upd_batch_app by lia; simpl.
    destruct (le_dec n (length l)).
    repeat rewrite firstn_app_l by lia.
    rewrite H by lia; eauto.
    repeat rewrite firstn_oob by (rewrite app_length; simpl; lia).
    repeat rewrite upd_upd_batch_app_rev by lia.
    rewrite upd_batch_upd_batch_noop; eauto.
    repeat rewrite app_length; simpl; eauto.
    repeat rewrite app_length; simpl; eauto.
  }
Qed.

Lemma upd_to_upd_batch_singleton:
  forall A AEQ V (m: @mem A AEQ V) a v,
    upd m a v = upd_batch m [a] [v].
Proof.
  eauto.
Qed.

Lemma upd_batch_to_list_upd_batch_singleton:
  forall A AEQ V (m: @mem A AEQ V) l_a l_v,
    upd_batch m l_a l_v = list_upd_batch m [l_a] [l_v].
Proof.
  eauto.
Qed.

Lemma upd_list_upd_batch_upd_noop:
  forall A AEQ V  l_l_a l_l_v a v1 v2 (s: @mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    upd (list_upd_batch (upd s a v1) l_l_a l_l_v) a v2 =
    upd (list_upd_batch s l_l_a l_l_v) a v2.
Proof.
  induction l_l_a; intros; eauto.
  apply upd_repeat; eauto.
  eapply_fresh forall2_length in H.
  destruct l_l_v;
  try solve [simpl in *; lia].
  simpl.
  destruct (in_dec AEQ a0 a).
  rewrite upd_batch_upd_in_noop; eauto.
  inversion H; lia.
  rewrite upd_batch_upd; eauto.
  rewrite IHl_l_a; eauto.
  inversion H; eauto.
Qed.

Lemma upd_batch_list_upd_batch_upd_batch_noop:
  forall A AEQ V l_a l_v1 l_v2 l_l_a l_l_v (s: @mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (list_upd_batch (upd_batch s l_a l_v1) l_l_a l_l_v) l_a l_v2 =
    upd_batch (list_upd_batch s l_l_a l_l_v) l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  destruct (in_dec AEQ a l_a).
  repeat rewrite upd_batch_in_cons_noop; eauto.

  simpl.
  repeat rewrite upd_batch_upd; eauto.
  setoid_rewrite upd_to_upd_batch_singleton at 2.
  setoid_rewrite upd_batch_to_list_upd_batch_singleton at 2.
  rewrite <- list_upd_batch_app.
  rewrite IHl_a; eauto.
  simpl.
  rewrite <- upd_batch_upd; eauto.
  rewrite upd_list_upd_batch_upd_noop; eauto.
  rewrite upd_batch_upd; eauto.
  apply Forall2_app; simpl; eauto.
  simpl; eauto.
Qed.

Lemma upd_batch_list_upd_batch_upd_batch_firstn_noop:
  forall A AEQ V l_a l_v1 l_v2 l_l_a l_l_v (s: @mem A AEQ V) n,
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    length l_a = length l_v1 ->
    length l_a = length l_v2 ->
    upd_batch (list_upd_batch (upd_batch s (firstn n l_a) (firstn n l_v1)) l_l_a l_l_v) l_a l_v2 =
    upd_batch (list_upd_batch s l_l_a l_l_v) l_a l_v2.
Proof.
  induction l_a; intros; eauto.
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  repeat rewrite firstn_nil; simpl; eauto.
  
  destruct l_v1, l_v2;
  try solve [simpl in *; lia].
  destruct n.
  simpl; eauto.
  destruct (in_dec AEQ a (firstn n l_a)).

  {
    simpl firstn.
    repeat rewrite upd_batch_in_cons_noop; eauto.
    eapply in_firstn_in; eauto.
    repeat rewrite firstn_length; simpl in *; lia.
    eapply in_firstn_in; eauto.
  }
  {
    simpl firstn.
    simpl upd_batch at 2.
    rewrite upd_batch_upd; eauto.
    simpl.
    rewrite upd_list_upd_batch_upd_noop; eauto.
    
    destruct (in_dec AEQ a l_a).
    repeat rewrite upd_batch_upd_in_noop; eauto.
    repeat rewrite upd_batch_upd; eauto.
    rewrite IHl_a; eauto.
  }
Qed.

Lemma Forall2_app_split:
  forall A B (l1 l2: list A) (l3 l4: list B) P,
    Forall2 P (l1++l2) (l3++l4) ->
    length l1 = length l3 ->
    Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  induction l1; intros; destruct l3;
  simpl in *; try lia; eauto.
  inversion H; cleanup.
  apply IHl1 in H6; try lia.
  intuition eauto.
Qed.

Lemma list_upd_batch_noop:
  forall A AEQ V l_l_a l_l_v1 l_l_v2 (s: @mem A AEQ V),
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v1 ->
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v2 ->
    list_upd_batch (list_upd_batch s l_l_a l_l_v1) l_l_a l_l_v2 =
    list_upd_batch s l_l_a l_l_v2.
Proof.
  intros A AEQ V l_l_a.
  eapply rev_ind with
      (P:= fun l_l_a =>
             forall (l_l_v1 l_l_v2 : list (list V)) (s : mem),
               Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v1 ->
               Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v2 ->
               list_upd_batch (list_upd_batch s l_l_a l_l_v1) l_l_a l_l_v2 =
               list_upd_batch s l_l_a l_l_v2).
  {
    simpl; intros; eauto.
  }
  {
    intros. 
    eapply_fresh forall2_length in H0;
    eapply_fresh forall2_length in H1.
    repeat rewrite app_length in *.
    destruct (nil_or_app l_l_v1);
    cleanup; try solve [simpl in *; lia].
    destruct (nil_or_app l_l_v2);
    cleanup; try solve [simpl in *; lia].

    repeat rewrite app_length in *.
    repeat rewrite list_upd_batch_app.
    simpl.                    
    rewrite upd_batch_list_upd_batch_upd_batch_noop; eauto.
    rewrite H; eauto.

    

    apply Forall2_app_split in H0; intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1;
    intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1; intuition eauto.
    simpl in *; lia.
    apply Forall2_app_split in H0; intuition eauto.
    inversion H3; eauto.
    simpl in *; lia.
    apply Forall2_app_split in H1; intuition eauto.
    inversion H3; eauto.
    all: simpl in *; lia.
  }
Qed.

Lemma list_upd_batch_firstn_noop:
  forall A AEQ V l_l_a l_l_v (s: @mem A AEQ V) n m,
    Forall2 (fun l_a l_v => length l_a = length l_v) l_l_a l_l_v ->
    list_upd_batch (list_upd_batch s (firstn n l_l_a ++ [firstn m (selN l_l_a n [])]) (firstn n l_l_v ++ [firstn m (selN l_l_v n [])])) l_l_a l_l_v =
    list_upd_batch s l_l_a l_l_v.
Proof.
  
  intros A AEQ V l_l_a.
  eapply rev_ind with
      (P:= fun l_l_a =>
             forall (l_l_v : list (list V)) (s : mem) (n m : nat),
               Forall2 (fun (l_a : list A) (l_v : list V) => length l_a = length l_v) l_l_a l_l_v ->
               list_upd_batch
                 (list_upd_batch s (firstn n l_l_a ++ [firstn m (selN l_l_a n [])])
                                 (firstn n l_l_v ++ [firstn m (selN l_l_v n [])])) l_l_a l_l_v = list_upd_batch s l_l_a l_l_v).
  {
    simpl; intros; eauto.
    repeat rewrite firstn_nil; simpl; eauto.
    destruct (firstn n l_l_v ++ [firstn m (selN l_l_v n [])]);
    eauto.
  }
  {
    intros.
    eapply_fresh forall2_length in H0.
    rewrite app_length in *.
    destruct (nil_or_app l_l_v); cleanup;
    try solve [simpl in *; lia].
    rewrite app_length in *.
    {
      repeat rewrite list_upd_batch_app by (simpl in *; lia); simpl.
      destruct (le_dec n (length l)).
      {
        repeat rewrite firstn_app_l by (simpl in *; lia).
        simpl in *.
        apply Forall2_app_split in H0; cleanup.
        inversion H1; cleanup.
        inversion l0; subst.
        {
          rewrite firstn_oob.
          repeat rewrite selN_last by (simpl in *; lia).
          setoid_rewrite firstn_oob at 2.
          repeat rewrite list_upd_batch_app by lia; eauto; simpl.
          rewrite upd_batch_list_upd_batch_upd_batch_firstn_noop; eauto.
          rewrite list_upd_batch_noop; eauto.
          lia.
          eauto.
        }
        {
          repeat rewrite selN_app by lia.
          rewrite H; eauto.
          rewrite list_upd_batch_app; eauto.
          lia.
        }
        lia.
      }
      {
        repeat rewrite selN_oob.
        repeat rewrite firstn_nil.
        repeat rewrite firstn_oob.
        rewrite list_upd_batch_app; simpl; eauto.
        rewrite upd_batch_to_list_upd_batch_singleton.
        rewrite <- list_upd_batch_app; eauto.
        rewrite list_upd_batch_noop; eauto.
        all: try repeat rewrite app_length; simpl in *; try lia.
      }
    }
  }
Qed.


(*** SPECS ***)
Global Opaque Log.commit Log.apply_log.
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


Theorem write_batch_to_cache_crashed:
  forall al vl o s s',
    exec CachedDiskLang o s (write_batch_to_cache al vl) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction al; simpl; intros;
  repeat invert_exec; cleanup;
  eauto; simpl in *; try lia;
  invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec; eauto.
  eapply IHal in H0; cleanup; eauto.
Qed.

Theorem write_lists_to_cache_finished:
  forall l_la_lv s o s' t,
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang o s (write_lists_to_cache l_la_lv) (Finished s' t) ->
    fst s' = list_upd_batch (fst s) (map fst l_la_lv) (map snd l_la_lv) /\
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
  forall l_la_lv s o s',
    Forall (fun la_lv => length (fst la_lv) = length (snd la_lv)) l_la_lv ->
    exec CachedDiskLang o s (write_lists_to_cache l_la_lv) (Crashed s') ->
    snd s' = snd s.
Proof.
  induction l_la_lv; simpl; intros; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec.
  apply write_batch_to_cache_crashed in H0; eauto.

  inversion H; cleanup.
  apply write_batch_to_cache_finished in H0; eauto.
  apply IHl_la_lv in H1; eauto.
  cleanup; repeat cleanup_pairs; eauto.
Qed.  

Lemma recover_finished:  
  forall merged_disk s o s' t,
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang o s recover (Finished s' t) ->
  cached_log_rep merged_disk s'.
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  eapply recover_finished in H4; eauto.
  apply write_lists_to_cache_finished in H2.
  repeat cleanup_pairs.
  unfold cached_log_rep; simpl; eexists; intuition eauto.
  rewrite map_fst_combine, map_snd_combine by (repeat rewrite map_length; eauto); eauto.
  assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite RepImplications.map_noop; eauto.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H11; eauto.
    unfold txn_well_formed in H11; simpl in *; cleanup.
    eapply Forall_forall in H15; eauto; lia.
  }
  rewrite A at 2.
  rewrite shift_list_upd_batch_set_comm.
  rewrite shift_eq_after with (m1:=s0)(m2:=sync s3).
  rewrite <- shift_list_upd_batch_set_comm.
  rewrite <- A.

  repeat (rewrite mem_map_shift_comm, mem_map_fst_list_upd_batch_set);
  rewrite mem_map_fst_sync_noop; eauto.
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
    intros; apply H6; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    cleanup.
    rewrite Forall_forall; intros.
    rewrite <- combine_map in H0.
    apply in_map_iff in H0; cleanup; simpl.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H13; eauto.
    unfold txn_well_formed in H13; simpl in *; cleanup.
    apply firstn_length_l; eauto.
  }
Qed.

Lemma recover_crashed:  
  forall merged_disk s o s',
  cached_log_reboot_rep merged_disk s ->
  exec CachedDiskLang o s recover (Crashed s') ->
  cached_log_reboot_rep merged_disk s' \/
  cached_log_crash_rep (During_Recovery merged_disk) s'.
Proof.
  unfold recover, cached_log_reboot_rep; intros; cleanup.
  repeat invert_exec.
  split_ors; cleanup; repeat invert_exec.
  {
    eapply recover_crashed in H3; eauto.
    repeat cleanup_pairs.
    split_ors; cleanup.
    {
      left; eexists; intuition eauto.
      assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite RepImplications.map_noop; eauto.
    intros.
    unfold log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H21; eauto.
    unfold txn_well_formed in H21; simpl in *; cleanup_no_match.
    eapply Forall_forall in H24; eauto; lia.
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
    intros; apply H0; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
    }
    split_ors; cleanup.
    {
      right; eexists; intuition eauto.
      assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite RepImplications.map_noop; eauto.
    intros.
    unfold log_reboot_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H12; eauto.
    unfold txn_well_formed in H12; simpl in *; cleanup_no_match.
    eapply Forall_forall in H16; eauto; lia.
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
    intros; apply H0; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
    }

    left; eexists; intuition eauto.
    {
      unfold log_rep, log_rep_general, log_reboot_rep in *.
      cleanup.
      do 4 eexists; intuition eauto; congruence.
    }
      assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite RepImplications.map_noop; eauto.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H11; eauto.
    unfold txn_well_formed in H11; simpl in *; cleanup_no_match.
    eapply Forall_forall in H15; eauto; lia.
      }
     
  rewrite A at 2.
  rewrite shift_list_upd_batch_set_comm.
  rewrite shift_eq_after with (m1:=s2)(m2:=sync s3).
  rewrite <- shift_list_upd_batch_set_comm.
  rewrite <- A; eauto.
  repeat rewrite mem_map_shift_comm.
  repeat rewrite mem_map_fst_list_upd_batch_set.
  rewrite mem_map_fst_sync_noop; eauto.

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
    intros; apply H0; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  }
  {
    eapply Log.Specs.recover_finished in H4; eauto; cleanup.
    apply write_lists_to_cache_crashed in H2; cleanup.
    repeat cleanup_pairs.
    {
      XXXXXX
    
    
    
  
      unfold log_reboot_rep.
      unfold cached_log_crash_rep.
      
  eapply recovery_finished in H4; eauto.
  apply write_lists_to_cache_finished in H2.
  repeat cleanup_pairs.
  unfold cached_log_rep; simpl; eexists; intuition eauto.
  rewrite map_fst_combine, map_snd_combine by (repeat rewrite map_length; eauto); eauto.
  assert (A: map addr_list x = map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
    repeat rewrite map_map.
    apply map_ext_in.
    intros.
    rewrite map_map.
    rewrite RepImplications.map_noop; eauto.
    intros.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H11; eauto.
    unfold txn_well_formed in H11; simpl in *; cleanup.
    eapply Forall_forall in H15; eauto; lia.
  }
  rewrite A at 2.
  rewrite shift_list_upd_batch_set_comm.
  rewrite shift_eq_after with (m1:=s0)(m2:=sync s3).
  rewrite <- shift_list_upd_batch_set_comm.
  rewrite <- A.

  repeat (rewrite mem_map_shift_comm, mem_map_fst_list_upd_batch_set);
  rewrite mem_map_fst_sync_noop; eauto.
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
    intros; apply H6; lia.
  }
  {
    unfold sumbool_agree; intros; intuition eauto.
    destruct (addr_dec x0 y); subst.
    destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
    destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
  }
  {
    cleanup.
    rewrite Forall_forall; intros.
    rewrite <- combine_map in H0.
    apply in_map_iff in H0; cleanup; simpl.
    unfold log_rep, log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; cleanup.
    eapply Forall_forall in H13; eauto.
    unfold txn_well_formed in H13; simpl in *; cleanup.
    apply firstn_length_l; eauto.
  }
Qed.

  
Theorem write_finished:
  forall merged_disk s o al vl s' t,
  cached_log_rep merged_disk s ->
  exec CachedDiskLang o s (write al vl) (Finished s' t) ->
  cached_log_rep merged_disk s' \/
  cached_log_rep (upd_batch merged_disk al vl) s'.
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
    exists (x4++[x7]).
    simpl.
    repeat rewrite map_app; simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *.
    eapply_fresh forall_app_l in H11. 
    inversion Hx; simpl in *; cleanup.
    unfold txn_well_formed in H20; cleanup.
    rewrite firstn_app2; eauto.
    simpl; intuition eauto.
    {
      rewrite list_upd_batch_app; eauto.
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
        eapply Forall_forall in H19; eauto.
        unfold txn_well_formed in H19; logic_clean.
        eapply Forall_forall in H35; eauto; lia.
      }
      setoid_rewrite A.
      rewrite shift_list_upd_batch_set_comm; eauto.
      setoid_rewrite shift_eq_after with (m1:= s0) (m2:= sync s3); intros; try lia.
      rewrite <- shift_list_upd_batch_set_comm; eauto.      
      rewrite <- A.

      repeat rewrite mem_map_shift_comm.
      repeat rewrite mem_map_fst_list_upd_batch_set.
      rewrite mem_map_fst_sync_noop.
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
        apply H10; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x) (data_start + y)); eauto; lia.
      }
    }
    rewrite map_length; eauto.
    rewrite map_length; eauto.
  }
  {(** First commit failed. Time to apply the log **)
    repeat invert_exec.
    simpl in *.
    eapply apply_log_finished in H9; eauto.
    logic_clean.
    apply write_batch_to_cache_finished in H1.
    logic_clean.
    unfold log_rep in *; logic_clean.
    eapply commit_finished in H10; eauto.
    all: try rewrite H6.
    split_ors; cleanup_no_match.
    {(** second commit is success **)
    right.
    repeat cleanup_pairs.
    exists ([x9]).
    simpl.
    
    unfold log_rep, log_rep_general, log_rep_explicit,
    log_rep_inner, txns_valid in *; cleanup; simpl in *. 
    inversion H12; simpl in *; cleanup.
    unfold txn_well_formed in H1; cleanup.
    rewrite firstn_app2; eauto.
    simpl; intuition eauto.
    {
      do 3 eexists; intuition eauto.
    }
    {
      rewrite shift_upd_batch_set_comm.
      setoid_rewrite shift_eq_after with (m1:= s0) (m2:= sync
          (sync
             (upd_set (list_upd_batch_set s1 (map addr_list x4) (map data_blocks x4)) hdr_block_num
                      (encode_header (update_hdr (decode_header (fst x11)) header_part0))))); intros; try lia.
      rewrite sync_idempotent.
      rewrite mem_map_fst_upd_batch_set.
      repeat rewrite mem_map_shift_comm.
      rewrite mem_map_fst_sync_noop.
      rewrite mem_map_fst_upd_set.
      repeat rewrite mem_map_fst_list_upd_batch_set.
      rewrite shift_upd_noop; eauto.

      {
        pose proof data_start_where_log_ends.
        pose proof hdr_before_log.
        lia.
      }
      {
        apply H18; lia.
      }
      {
        unfold sumbool_agree; intros; intuition eauto.
        destruct (addr_dec x0 y); subst.
        destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
        destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
      }
    }
    rewrite map_length; eauto.
    }
    {
      rewrite app_length in H16.
      repeat cleanup_pairs.
      unfold log_rep, log_rep_general, log_rep_explicit,
      log_rep_inner, header_part_is_valid, txns_valid in *;
      simpl in *; cleanup; simpl in *. 
          
      rewrite <- H9 in *; simpl in *.
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
      apply in_map_iff in H15; cleanup.
      lia.
      rewrite map_length; eauto.
    }
    {
      rewrite firstn_app2; eauto.
      intros.
      apply in_map_iff in H15; cleanup.
      admit.
      rewrite map_length; eauto.
    }
    rewrite app_length, map_length; lia.
    rewrite map_length; eauto.
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
    apply in_map_iff in H7; cleanup_no_match.
    lia.
    rewrite map_length; eauto.
  }
  {
    rewrite firstn_app2; eauto.
    intros.
    apply in_map_iff in H7; cleanup_no_match.
    admit.
    rewrite map_length; eauto.
  }  
  rewrite app_length, map_length; lia.
Admitted.


Theorem write_crashed:
  forall merged_disk s o al vl s',
  cached_log_rep merged_disk s ->
  exec CachedDiskLang o s (write al vl) (Crashed s') ->
  cached_log_rep merged_disk s' \/
  cached_log_crash_rep (During_Commit merged_disk (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (After_Commit (upd_batch merged_disk al vl)) s' \/
  cached_log_crash_rep (During_Apply merged_disk) s' \/
  cached_log_crash_rep (After_Apply merged_disk) s'.
Proof.
  unfold cached_log_rep, write; simpl; intros.
  cleanup; invert_exec.
  {
    split_ors; cleanup; repeat invert_exec.
    {
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_crashed in H3; eauto.
      {
        repeat (split_ors; cleanup);
        repeat cleanup_pairs; eauto.
        {
          right; left; unfold cached_log_crash_rep; simpl.
          left; eexists; intuition eauto.
          rewrite <- sync_list_upd_batch_set.
          rewrite <- sync_shift_comm.
          
          assert (A: map addr_list x =
                     map (map (Init.Nat.add data_start)) (map (map (fun a => a - data_start)) (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed, record_is_valid in H13; logic_clean.
            eapply Forall_forall in H18; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          rewrite mem_map_fst_sync_noop; eauto.
          apply shift_eq_after.
          intros; lia.
          intros; apply H3; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x0 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x0 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x0) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed in H13; logic_clean; eauto.
          }
        }
        {
          right; left; unfold cached_log_crash_rep; simpl.
          right; do 2 eexists; intuition eauto.
          {
            rewrite <- sync_list_upd_batch_set.
            rewrite <- sync_shift_comm.
            
            assert (A: map addr_list (x++[x0]) =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list (x++[x0])))). {
              repeat rewrite map_map; simpl.
              setoid_rewrite map_ext_in at 2.
              eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H19; eauto.
            unfold txn_well_formed, record_is_valid in H19; logic_clean.
            eapply Forall_forall in H24; eauto; lia.
          }
          assert (A0: map addr_list x =
                      map (map (Init.Nat.add data_start))
                          (map (map (fun a => a - data_start))
                               (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H19; eauto.
            unfold txn_well_formed, record_is_valid in H19; logic_clean.
            eapply Forall_forall in H24; eauto; lia.
          }
          rewrite A, A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite mem_map_fst_sync_noop.
          rewrite mem_map_fst_upd_batch_set.
          unfold log_crash_rep in *; simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in H12; logic_clean.
          eapply forall_app_l in H15.
          simpl in *.
          inversion H15; subst.
          unfold txn_well_formed in H18; logic_clean.
          rewrite H20, H0, H4 in *.
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
          intros; apply H6; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H19; eauto.
            unfold txn_well_formed in H19; logic_clean; eauto.
          }
          }
          {
           rewrite <- sync_list_upd_batch_set.
           rewrite <- sync_shift_comm.
           
           assert (A0: map addr_list x =
                       map (map (Init.Nat.add data_start))
                           (map (map (fun a => a - data_start))
                                (map addr_list x))). {
            repeat rewrite map_map; simpl.
            setoid_rewrite map_ext_in at 2.
            eauto.
            intros.
            rewrite map_map.        
            setoid_rewrite map_ext_in.
            apply map_id.
            intros; simpl.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            
            eapply Forall_forall in H19; eauto.
            unfold txn_well_formed, record_is_valid in H19; logic_clean.
            eapply Forall_forall in H24; eauto; lia.
          }
          rewrite A0.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s3) with (shift (Init.Nat.add data_start) s2); eauto.
          
          repeat rewrite map_app.
          rewrite mem_map_fst_sync_noop; eauto.

          apply shift_eq_after.
          intros; lia.
          intros; apply H6; lia.
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_crash_rep, log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H19; eauto.
            unfold txn_well_formed in H19; logic_clean; eauto.
          }
          }
        }

        {
          right; right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          rewrite <- sync_list_upd_batch_set.
          rewrite <- sync_shift_comm.
          
          assert (A: map addr_list (x++[x0]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x0])))). {
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
            
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed, record_is_valid in H13; logic_clean.
            eapply Forall_forall in H24; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite mem_map_fst_sync_noop.
          repeat rewrite mem_map_shift_comm.
          repeat rewrite mem_map_fst_upd_batch_set.
          repeat rewrite mem_map_fst_list_upd_batch_set.
          rewrite mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H17.
          simpl in *.
          inversion H17; subst.
          unfold txn_well_formed in H22; logic_clean.
          rewrite H21, H0, H4 in *.
          rewrite firstn_app2; eauto.
          rewrite map_length; eauto.
          repeat rewrite map_length; eauto.
          
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }          
          {
            apply shift_eq_after.
            intros; lia.
            intros; rewrite H6; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x4 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x4) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed in H13; logic_clean; eauto.
          }
        }
      }
      all: try rewrite H4, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H5; cleanup_no_match.
        lia.
      }
      {
        intros.
        apply in_map_iff in H5; cleanup_no_match.
        admit.
      }
      {
        rewrite H4, app_length, map_length; lia.
      }
    }
    {
      unfold log_rep in *; logic_clean.
      destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      eapply commit_finished in H4; eauto.
      split_ors; cleanup; try congruence.
      {
        split_ors; cleanup; repeat invert_exec;
        repeat cleanup_pairs.
        {
          right; right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          rewrite <- sync_list_upd_batch_set.
          rewrite <- sync_shift_comm.
          
          assert (A: map addr_list (x++[x3]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x3])))). {
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
            
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed, record_is_valid in H13; logic_clean.
            eapply Forall_forall in H24; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite mem_map_fst_sync_noop.
          repeat rewrite mem_map_shift_comm.
          repeat rewrite mem_map_fst_upd_batch_set.
          repeat rewrite mem_map_fst_list_upd_batch_set.
          rewrite mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H17.
          simpl in *.
          inversion H17; subst.
          unfold txn_well_formed in H22; logic_clean.
          rewrite H21, H4, H1 in *.
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
            intros; rewrite H8; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H13; eauto.
            unfold txn_well_formed in H13; logic_clean; eauto.
          }
        }
        {
          eapply write_batch_to_cache_crashed in H5.
          simpl in *; cleanup.
          right; right; left; unfold cached_log_crash_rep; simpl.
          eexists; intuition eauto.
          
          rewrite <- sync_list_upd_batch_set.
          rewrite <- sync_shift_comm.
          
          assert (A: map addr_list (x++[x3]) =
                     map (map (Init.Nat.add data_start))
                         (map (map (fun a => a - data_start))
                              (map addr_list (x++[x3])))). {
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
            
            eapply Forall_forall in H14; eauto.
            unfold txn_well_formed, record_is_valid in H14; logic_clean.
            eapply Forall_forall in H25; eauto; lia.
          }
          rewrite A.
          repeat rewrite shift_list_upd_batch_set_comm.
          replace (shift (Init.Nat.add data_start) s2) with (shift (Init.Nat.add data_start) (sync s3)); eauto.

          rewrite <- shift_list_upd_batch_set_comm, <- A.
          rewrite <- mem_map_fst_upd_batch_set.
          rewrite <- shift_upd_batch_set_comm.
          
          repeat rewrite map_app.
          rewrite list_upd_batch_set_app; simpl.
          rewrite mem_map_fst_sync_noop.
          repeat rewrite mem_map_shift_comm.
          repeat rewrite mem_map_fst_upd_batch_set.
          repeat rewrite mem_map_fst_list_upd_batch_set.
          rewrite mem_map_fst_sync_noop; eauto.
          
          unfold log_rep, log_rep_general, log_rep_explicit in *;
          simpl in *; logic_clean.
          unfold log_rep_inner, txns_valid in *; logic_clean.
          eapply forall_app_l in H18.
          simpl in *.
          inversion H18; subst.
          unfold txn_well_formed in H23; logic_clean.
          rewrite H22, H4, H1 in *.
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
            intros; rewrite H8; eauto; lia.
          }
          {
            unfold sumbool_agree; intros; intuition eauto.
            destruct (addr_dec x2 y); subst.
            destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
            destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
          }
          {
            intros.
            apply in_map_iff in H; cleanup.
            unfold log_rep, log_rep_general, log_rep_explicit,
            log_rep_inner, txns_valid in *; cleanup.
            eapply Forall_forall in H14; eauto.
            unfold txn_well_formed in H14; logic_clean; eauto.
          }
        }
      }
      all: try rewrite H1, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H2; cleanup_no_match.
        lia.
      }
      {
        intros.
        apply in_map_iff in H2; cleanup_no_match.
        admit.
      }
      {
        rewrite H1, app_length, map_length; lia.
      }
    }
    {
      unfold log_rep in *; logic_clean.
      eapply commit_finished in H4; eauto.
      {
        split_ors; cleanup; try congruence.
        repeat cleanup_pairs.
        split_ors; cleanup; repeat invert_exec.
        {
          split_ors; cleanup; repeat invert_exec.
          {(** Apply log crahed **)
            simpl in *;
            eapply apply_log_crashed in H2; eauto.
            cleanup; split_ors; cleanup; repeat cleanup_pairs.
             {
               left; unfold cached_log_rep; simpl.
               eexists; intuition eauto.
             }
             {               
               split_ors; cleanup.
               {
                 left; unfold cached_log_rep; simpl.
                 eexists; intuition eauto.
                 repeat rewrite mem_map_shift_comm.
                 repeat rewrite mem_map_fst_list_upd_batch_set.
                 rewrite mem_map_fst_upd_batch_set.
                 rewrite mem_map_fst_list_upd_batch_set.
                 rewrite upd_batch_to_list_upd_batch_singleton.
                 setoid_rewrite <- list_upd_batch_app at 2.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H9.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite list_upd_batch_firstn_noop; eauto.
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 eauto.
                 rewrite map_length; eauto.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H9.                 
                 erewrite RepImplications.bimap_get_addr_list.
                 repeat rewrite firstn_length, map_length; eauto.
                 3: eauto.
                 eauto.
                 rewrite map_length; eauto.
               }
               split_ors; cleanup.
               {
                 left; unfold cached_log_rep; simpl.
                 eexists; intuition eauto.
                 repeat rewrite mem_map_shift_comm.
                 repeat rewrite mem_map_fst_list_upd_batch_set.
                 rewrite mem_map_fst_sync_noop.
                 rewrite mem_map_fst_list_upd_batch_set.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                 rewrite <- H9.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite list_upd_batch_noop; eauto.
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 eauto.
                 rewrite map_length; eauto.
               }
               {
                 simpl in *.
                 cleanup; simpl in *.
                 right; right; right; left; unfold cached_log_rep; simpl in *.
                 eexists; intuition eauto.
                 
                 repeat rewrite mem_map_shift_comm.
                 rewrite <- sync_list_upd_batch_set.
                 rewrite mem_map_fst_sync_noop.
                 repeat rewrite mem_map_fst_list_upd_batch_set.
                 rewrite mem_map_fst_upd_set.
                 rewrite mem_map_fst_sync_noop.
                 rewrite mem_map_fst_list_upd_batch_set.
                 setoid_rewrite <- shift_upd_noop at 4.
                 rewrite upd_list_upd_batch_upd_noop.
                 setoid_rewrite shift_upd_noop.
                 unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; simpl in *; logic_clean.
                 rewrite <- H9.
                 erewrite RepImplications.bimap_get_addr_list.
                 4: eauto.
                 rewrite list_upd_batch_noop; eauto.

                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
                   apply firstn_length_l; eauto.
                   lia.
                   repeat rewrite map_length; eauto.
                 }
                 {
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
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
                   unfold log_rep_general, log_rep_explicit, log_rep_inner, txns_valid in *; logic_clean.
                   apply forall_forall2.
                   apply Forall_forall; intros.
                   rewrite <- combine_map in H11.
                   apply in_map_iff in H11; cleanup.
                   simpl.
                   eapply Forall_forall in H10; eauto.
                   unfold txn_well_formed in H10; logic_clean.
                   rewrite H13.
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
                   unfold log_crash_rep, log_rep_inner, log_rep_inner, txns_valid in *; simpl in *; logic_clean.
                   intros.
                   apply in_map_iff in H7; cleanup.
                   eapply Forall_forall in H6; eauto.
                   unfold txn_well_formed in H6; simpl in *; logic_clean; eauto.
                 }
               }
             }
          }
          eapply apply_log_finished in H3; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs.
          split_ors; cleanup.
          {(** Flush Crashed **)
            repeat invert_exec.            
             {
               right; right; right; right; unfold cached_log_rep; simpl.
               intuition eauto.
               rewrite <- sync_shift_comm.
               rewrite shift_upd_set_noop.
               rewrite mem_map_fst_sync_noop; eauto.
               {
                 intros; pose proof hdr_before_log.
                 pose proof data_start_where_log_ends.
                 lia.
               }
             }
          }
          repeat invert_exec.
          split_ors; cleanup; repeat invert_exec.
          { (** Second commit crashed **)
            simpl in *.
            destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
            eapply commit_crashed in H5; eauto.
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              left.
              eexists; intuition eauto.
              simpl; eauto.
              simpl.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; left; left; eexists; intuition eauto.
              simpl.
              rewrite <- sync_shift_comm; simpl.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                  (encode_header (update_hdr x0 header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              repeat rewrite mem_map_fst_sync_noop; eauto.
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H2; lia.
            }
            split_ors; cleanup; 
            simpl in *; repeat cleanup_pairs.
            {
              right; left; right; do 2 eexists; intuition eauto.
              simpl.
              replace (addr_list x1) with (map (Init.Nat.add data_start) al).
              rewrite <- shift_upd_batch_comm.
              rewrite <- sync_shift_comm; simpl.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
            (encode_header (update_hdr x0 header_part0)))).
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite <- mem_map_fst_upd_batch_set.
              rewrite sync_idempotent.
              repeat rewrite <- sync_upd_batch_set_comm.
              repeat rewrite mem_map_fst_sync_noop; eauto.
              
              {
                admit.
              }
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H7; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x3 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
              }
              {
                unfold log_crash_rep in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H15; cleanup.
                inversion H18; cleanup.
                unfold txn_well_formed in H21; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
              {
                simpl.
                rewrite <- sync_shift_comm; simpl.
                rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
            (encode_header (update_hdr x0 header_part0)))).
                rewrite <- sync_shift_comm.
                rewrite shift_upd_set_noop.
                repeat rewrite mem_map_fst_sync_noop; eauto.
                {
                  intros; pose proof hdr_before_log.
                  pose proof data_start_where_log_ends.
                  lia.
                }
                intros; lia.
                intros; apply H7; lia.
              }
             }
            {
              right; right; left; eexists; intuition eauto.
              simpl.
              replace (addr_list x1) with (map (Init.Nat.add data_start) al).
              rewrite <- shift_upd_batch_comm.
              rewrite <- sync_shift_comm; simpl.
              rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite <- mem_map_fst_upd_batch_set.
              rewrite sync_idempotent.
              repeat rewrite <- sync_upd_batch_set_comm.
              repeat rewrite mem_map_fst_sync_noop; eauto.              
              {
                admit.
              }
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H7; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x3 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x3) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H12; cleanup.
                inversion H3; cleanup.
                unfold txn_well_formed in H26; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
            }
            all: try rewrite H6, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H7; cleanup_no_match.
              lia.
            }
            {
              intros.
              apply in_map_iff in H7; cleanup_no_match.
              admit.
            }
            {
              rewrite H6, app_length, map_length; lia.
            }
          }
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          eapply commit_finished in H5; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H2.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list x) (map data_blocks x) hdr_block_num); simpl in *;
            destruct x1; simpl in *; cleanup;
            rewrite encode_decode_header, app_length in H5; simpl in *;
            lia.
          }
          {
            right; right; left; unfold cached_log_crash_rep; simpl.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x1) with (map (Init.Nat.add data_start) al).
            rewrite <- shift_upd_batch_comm.
            rewrite <- sync_shift_comm; simpl.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite <- mem_map_fst_upd_batch_set.
              rewrite sync_idempotent.
              repeat rewrite <- sync_upd_batch_set_comm.
              repeat rewrite mem_map_fst_sync_noop; eauto.              
              {
                admit.
              }
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H8; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x2 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x2) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H12; cleanup.
                inversion H3; cleanup.
                unfold txn_well_formed in H26; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
              }
            }
            all: try rewrite H6, firstn_app2.
            all: try rewrite app_length;
            try rewrite map_length; try lia.
            {
              apply FinFun.Injective_map_NoDup; eauto.
              unfold FinFun.Injective; intros; lia.
            }
            {
              apply Forall_forall; intros.
              apply in_map_iff in H7; cleanup_no_match.
              lia.
            }
            {
              intros.
              apply in_map_iff in H7; cleanup_no_match.
              admit.
            }
            {
              rewrite H6, app_length, map_length; lia.
            }
        }
        {(** write_batch_to_cache_crashed **)
          eapply apply_log_finished in H5; eauto.
          simpl in *; cleanup.
          unfold log_rep in *; logic_clean.
          destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
          simpl in *; repeat cleanup_pairs; simpl in *.
          eapply commit_finished in H6; eauto.
          simpl in *; repeat cleanup_pairs; simpl in *.
          split_ors; cleanup; try congruence; try lia.
          2: {
            unfold log_rep_general, log_rep_explicit, log_header_block_rep in *; simpl in *; logic_clean.
            unfold sync, upd_set in H2.
            destruct (addr_dec hdr_block_num hdr_block_num); try lia.
            destruct (list_upd_batch_set s1 (map addr_list x) (map data_blocks x) hdr_block_num); simpl in *;
            destruct x1; simpl in *; cleanup;
            rewrite encode_decode_header, app_length in H5; simpl in *;
            lia.
          }
          eapply write_batch_to_cache_crashed in H1; eauto.
          simpl in *; cleanup.
          repeat cleanup_pairs; simpl in *.
          {
            right; right; left; unfold cached_log_crash_rep; simpl.
            eexists; intuition eauto.
            simpl.
            replace (addr_list x1) with (map (Init.Nat.add data_start) al).
            rewrite <- shift_upd_batch_comm.
            rewrite <- sync_shift_comm; simpl.
            rewrite shift_eq_after with (m1:= s2) (m2:= sync
         (sync
            (upd_set (list_upd_batch_set s1 (map addr_list x) (map data_blocks x)) hdr_block_num
                     (encode_header (update_hdr x0 header_part0))))).
              rewrite sync_idempotent.
              rewrite <- sync_shift_comm.
              rewrite shift_upd_set_noop.
              rewrite <- mem_map_fst_upd_batch_set.
              rewrite sync_idempotent.
              repeat rewrite <- sync_upd_batch_set_comm.
              repeat rewrite mem_map_fst_sync_noop; eauto.              
              {
                admit.
              }
              {
                intros; pose proof hdr_before_log.
                pose proof data_start_where_log_ends.
                lia.
              }
              intros; lia.
              intros; apply H9; lia.
              {
                unfold sumbool_agree; intros; intuition eauto.
                destruct (addr_dec x5 y); subst.
                destruct (addr_dec (data_start + y) (data_start + y)); eauto; congruence.
                destruct (addr_dec (data_start + x5) (data_start + y)); eauto; lia.
              }
              {
                unfold log_rep, log_rep_general, log_rep_explicit in *; cleanup.
                simpl in *.
                unfold log_rep_inner, txns_valid in H12; cleanup.
                inversion H1; cleanup.
                unfold txn_well_formed in H26; simpl in *; cleanup.
                rewrite firstn_app2; eauto.
                rewrite map_length; eauto.
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
              apply in_map_iff in H2; cleanup_no_match.
              lia.
            }
            {
              intros.
              apply in_map_iff in H2; cleanup_no_match.
              admit.
            }
            {
              rewrite H8, app_length, map_length; lia.
            }
        }
      }
      all: destruct (addr_list_to_blocks_to_addr_list (map (Init.Nat.add data_start) al)).
      all: try rewrite H1, firstn_app2.
      all: try rewrite app_length;
      try rewrite map_length; try lia.
      {
        apply FinFun.Injective_map_NoDup; eauto.
        unfold FinFun.Injective; intros; lia.
      }
      {
        apply Forall_forall; intros.
        apply in_map_iff in H2; cleanup_no_match.
        lia.
      }
      {
        intros.
        apply in_map_iff in H2; cleanup_no_match.
        admit.
      }
      {
        rewrite H1, app_length, map_length; lia.
      }
    }
  }
  all: try solve [left; eexists; intuition eauto].
  Unshelve.
  apply value0.
Admitted.


  
  
