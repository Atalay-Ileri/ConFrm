Require Import Compare_dec Lia Framework TotalMem FSParameters TransactionCacheLayer.

Fixpoint get_first (txn: list (addr * value)) a :=
  match txn  with
  | ad :: txn' =>
    if addr_eq_dec a (fst ad) then
      Some (snd ad)
    else
      get_first txn' a
  | [] =>
    None
  end.

Definition abort :=
  _ <- |TCCO| Delete _;
  Ret tt.

Definition commit :=
  txn <- |TCCO| Get _;
  let al := map fst txn in
  let vl := map snd txn in
  let dedup_al := dedup_last addr_dec (rev al) in
  let dedup_vl := dedup_by_list addr_dec (rev al) (rev vl) in
  _ <- |TCDO| Write dedup_al dedup_vl;
  _ <- |TCCO| Delete _;
  Ret tt.

(* Definition abort := start. *)

(* if you read out of bounds, you get 0 block *)
Definition read a :=
  if lt_dec a data_length then
    txn <- |TCCO| Get _;
    match get_first txn a with
    | Some v =>
      Ret v
    | None =>
      v <- |TCDO| Read a;
      Ret v
    end
  else
    Ret value0.

(* if you write out of bounds, nothing happens *)
Definition write a v :=
  if lt_dec a data_length then
    txn <- |TCCO| Get _;
    if lt_dec (length txn) log_length then
      _ <- |TCCO| Put (a, v);
      Ret tt
    else
      Ret tt
  else
    Ret tt.

Definition recover :=
  _ <- |TCDO| Recover;
  Ret tt.

Definition transaction_rep (tcd: TransactionCacheLang.(state)) (td: (@total_mem addr addr_dec value) * (@total_mem addr addr_dec value)):=
  let al := map fst (fst tcd) in
  let vl := map snd (fst tcd) in
  fst td = upd_batch (snd tcd) (rev al) (rev vl) /\
  snd td = snd tcd.
  

Definition transaction_reboot_rep (tcd: TransactionCacheLang.(state)) (td: (@total_mem addr addr_dec value) * (@total_mem addr addr_dec value)):=
  fst tcd = [] /\
  snd td = snd tcd.

Theorem abort_finished:
  forall u s o s' r,
    exec TransactionCacheLang u o s abort (Finished s' r) ->
    fst s' = [] /\ snd s' = snd s.
Proof.
  unfold abort; intros; repeat invert_exec; eauto.
Qed.

Theorem abort_crashed:
  forall u s o s',
    exec TransactionCacheLang u o s abort (Crashed s') ->
    snd s' = snd s.
Proof.
  unfold abort; intros; repeat invert_exec; eauto.
  split_ors; cleanup; repeat invert_exec; eauto.
Qed.

(*
Definition abort_finished := start_finished.
Definition abort_crashed := start_crashed.
 *)

Lemma upd_batch_dedup_last_dedup_by_list:
  forall A AEQ V l_a l_v (tm: @total_mem A AEQ V),
    length l_a = length l_v ->
    upd_batch tm l_a l_v =
    upd_batch tm (dedup_last AEQ l_a) (dedup_by_list AEQ l_a l_v).
Proof.
  induction l_a; simpl; intros; eauto.
  destruct l_v; simpl in *; try congruence; eauto.
  destruct (in_dec AEQ a l_a).
  rewrite upd_batch_upd_in_noop; eauto.
  simpl; eauto.
Qed.

Set Nested Proofs Allowed.

Theorem commit_finished :
  forall u s o s' r td,
    transaction_rep s td ->
    exec TransactionCacheLang u o s commit (Finished s' r) ->
    transaction_rep s' (fst td, fst td) \/
    transaction_rep s' (snd td, snd td).
Proof.
  unfold commit, transaction_rep; simpl; intros.
  repeat invert_exec; simpl in *; cleanup;
  repeat cleanup_pairs.
  {
    left; simpl; split;
    apply upd_batch_dedup_last_dedup_by_list; eauto;
    repeat rewrite rev_length, map_length; eauto.    
  }
  right; eauto.
Qed.

Theorem commit_crashed :
  forall u s o s' td,
    transaction_rep s td ->
    exec TransactionCacheLang u o s commit (Crashed s') ->
    snd s' = snd td \/ snd s' = fst td.
Proof.
  unfold commit, transaction_rep; simpl; intros.
  repeat invert_exec; simpl in *; cleanup;
  repeat cleanup_pairs.
  repeat (match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
  repeat invert_exec; simpl in *;
  try solve [ left; eauto ];
  try solve [
    right; setoid_rewrite upd_batch_dedup_last_dedup_by_list at 2; eauto;
    repeat rewrite rev_length, map_length; eauto ]).
Qed.

Lemma get_first_some_upd_batch:
  forall l tm a v,
    get_first l a = Some v ->
    upd_batch tm (rev (map fst l)) (rev (map snd l)) a = v.
Proof.
  induction l; simpl; intros; try congruence.
  rewrite upd_batch_app; simpl.
  cleanup.
  rewrite upd_eq; eauto.
  rewrite upd_ne; eauto.
  repeat rewrite rev_length, map_length; eauto.
Qed.

Lemma get_first_none_not_in:
  forall l a,
    get_first l a = None ->
    ~In a (map fst l).
Proof.
  induction l; simpl in *; intuition.
  simpl in *; cleanup; try congruence.
  simpl in *; destruct (addr_eq_dec a a0);
  try congruence; eauto.
Qed.

Definition read_finished :
  forall u s o s' r td a,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (read a) (Finished s' r) ->
    transaction_rep s' td /\
    ((a < data_length /\ r = (fst td) a) \/
     (a >= data_length /\ r = value0)).
Proof.
  unfold read, transaction_rep; intros; cleanup;
  repeat invert_exec; cleanup;
  repeat cleanup_pairs; split; eauto.
  {
    left; split; eauto.
    erewrite get_first_some_upd_batch; eauto.
  }
  {
    left; split; eauto.
    rewrite upd_batch_ne; eauto.

    intros Hx.
    apply in_rev in Hx; eauto.
    apply get_first_none_not_in in Hx; eauto.
  }
  {
    right; split; eauto; lia.
  }
Qed.

Definition read_crashed :
  forall u s o s' td a,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (read a) (Crashed s') ->
    transaction_rep s' td.
Proof.
  unfold read, transaction_rep; simpl; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  repeat cleanup_pairs;
  repeat (
      match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
      repeat invert_exec; cleanup;
      simpl in *; eauto).
  invert_exec; simpl; eauto.
  invert_exec; simpl; eauto.
  repeat (
      match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
      repeat invert_exec; cleanup;
      simpl in *; eauto).
  eauto.
Qed.


Definition write_finished :
  forall u s o s' r td a v,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (write a v) (Finished s' r) ->
    (a < data_length /\
     length (fst s) < log_length /\
     transaction_rep s' (upd (fst td) a v, snd td)) \/
    ((a >= data_length \/
      length (fst s) >= log_length) /\
     transaction_rep s' td).
Proof.
  unfold write, transaction_rep; intros; cleanup;
  repeat invert_exec; cleanup; simpl in *;
  repeat cleanup_pairs; eauto.
  {
    left; split; eauto.
    erewrite upd_batch_app; simpl; eauto.
    repeat rewrite rev_length, map_length; eauto.
  }
  {
    right; split; eauto; lia.
  }
  {
    right; split; eauto; lia.
  }
Qed.

Definition write_crashed :
  forall u s o s' td a v,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (write a v) (Crashed s') ->
    transaction_rep s' (upd (fst td) a v, snd td) \/
    transaction_rep s' td.
Proof.
  unfold write, transaction_rep; simpl; intros.
  cleanup; repeat invert_exec; simpl in *; cleanup;
  repeat cleanup_pairs;
  repeat (
      match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
      repeat invert_exec; cleanup;
      simpl in *; eauto).
  invert_exec; simpl; eauto.
  repeat (
      match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
      repeat invert_exec; cleanup;
      simpl in *; eauto).
  {
    left; split; eauto.
    erewrite upd_batch_app; simpl; eauto.
    repeat rewrite rev_length, map_length; eauto.
  }
  {
    invert_exec.
    right; split; eauto; lia.
  }
  {
    right; split; eauto; lia.
  }
Qed.

Definition recover_finished :
  forall u s o s' r td,
    transaction_reboot_rep s td ->
    exec TransactionCacheLang u o s recover (Finished s' r) ->
    transaction_rep s' (snd td, snd td).
Proof.
  unfold recover, transaction_reboot_rep, transaction_rep; intros.
  repeat invert_exec; cleanup; repeat cleanup_pairs; simpl; eauto.
Qed.

Definition recover_crashed :
  forall u s o s' td,
    transaction_reboot_rep s td ->
    exec TransactionCacheLang u o s recover (Crashed s') ->
    snd s' = snd s.
Proof.
  unfold recover, transaction_reboot_rep, transaction_rep; intros.
  repeat invert_exec; cleanup; repeat cleanup_pairs; simpl; eauto.
  split_ors; cleanup; repeat invert_exec; eauto.
Qed.
