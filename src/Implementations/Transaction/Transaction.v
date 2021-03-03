Require Import Compare_dec Lia Framework TotalMem FSParameters TransactionCacheLayer.
Set Nested Proofs Allowed.

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

(** Reverses before writing back **)
Definition commit :=
  txn <- |TCCO| Get _;
  let al := map fst txn in
  let vl := map snd txn in
  let dedup_al := dedup_last addr_dec (rev al) in
  let dedup_vl := dedup_by_list addr_dec (rev al) (rev vl) in
  _ <- |TCDO| Write dedup_al dedup_vl;
  _ <- |TCCO| Delete _;
  Ret tt.

(** If you read out of bounds, you get 0 block *)
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

(** If you write out of bounds, nothing happens *)
Definition write a v :=
  if lt_dec a data_length then
    txn <- |TCCO| Get _;
  if le_dec (length (addr_list_to_blocks (map fst txn ++ [a])) +
             length ((map snd txn) ++ [v])) log_length then
      _ <- |TCCO| Put (a, v);
      Ret tt
    else
      Ret tt
  else
    Ret tt.

Definition recover :=
  _ <- |TCCO| Delete _;
  _ <- |TCDO| Recover;
Ret tt.

Definition init l_av :=
  _ <- |TCCO| Delete _;
  |TCDO| Init l_av.



Definition transaction_rep (tcd: TransactionCacheLang.(state)) (td: (@total_mem addr addr_dec value) * (@total_mem addr addr_dec value)):=
  let al := map fst (fst tcd) in
  let vl := map snd (fst tcd) in
  Forall (fun a => a < data_length) al /\
  length (addr_list_to_blocks al) + length vl <= log_length /\
  fst td = upd_batch (snd tcd) (rev al) (rev vl) /\
  snd td = snd tcd.
  

Definition transaction_reboot_rep (tcd: TransactionCacheLang.(state)) (td: (@total_mem addr addr_dec value) * (@total_mem addr addr_dec value)):=
  snd td = snd tcd.

(*** Lemmas ***)
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

Lemma dedup_last_in :
  forall A AEQ (l: list A) a,
    In a l <-> In a (dedup_last AEQ l).
Proof.
  induction l; simpl; split; intros; eauto.
  {
    destruct (in_dec AEQ a l); eauto.
    apply IHl.
    split_ors; subst; eauto.
    
    split_ors; try solve [econstructor; eauto].
    apply IHl in H; solve [constructor; eauto].
  }
  {
    destruct (in_dec AEQ a l); eauto.
    apply IHl in H; eauto.
    
    simpl in *;
    split_ors; try solve [econstructor; eauto].
    apply IHl in H; eauto.
  }
Qed.

Lemma dedup_last_not_in :
  forall A AEQ (l: list A) a,
    ~ In a l <-> ~ In a (dedup_last AEQ l).
Proof.
  unfold not; split; intros;
  eapply dedup_last_in in H0; eauto.
Qed.

Lemma dedup_last_NoDup :
  forall A AEQ (l: list A),
    NoDup (dedup_last AEQ l).
Proof.
  induction l; simpl; eauto.
  econstructor.
  destruct (in_dec AEQ a l); eauto.
  constructor; eauto.
  apply dedup_last_not_in; eauto.
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


(*** Specs ***)
Theorem init_finished:
  forall u s o s' r l_av,
    let l_a := map fst l_av in
    let l_v := map snd l_av in
    exec TransactionCacheLang u o s (init l_av) (Finished s' r) ->
    fst s' = [] /\ snd s' = upd_batch (snd s) l_a l_v.
Proof.
  unfold init; intros; repeat invert_exec; eauto.
  repeat cleanup_pairs; eauto.
Qed.


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

Theorem commit_finished :
  forall u s o s' r td,
    transaction_rep s td ->
    exec TransactionCacheLang u o s commit (Finished s' r) ->
    transaction_rep s' (fst td, fst td) /\
    fst s' = [].
Proof.
  unfold commit, transaction_rep; simpl; intros.
  repeat invert_exec; simpl in *; cleanup;
  repeat cleanup_pairs.
  {
    repeat (split; eauto).
    pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.

    apply upd_batch_dedup_last_dedup_by_list; eauto;
    repeat rewrite rev_length, map_length; eauto.
    apply upd_batch_dedup_last_dedup_by_list; eauto;
    repeat rewrite rev_length, map_length; eauto.    
  }
  {
    split_ors.    
    {
      exfalso; apply H0; apply dedup_last_NoDup.
    }
    split_ors.
    {
      exfalso; apply H0; apply dedup_last_dedup_by_list_length_le.
      repeat rewrite rev_length, map_length; eauto.
    }
   
    split_ors.
    {
      exfalso; apply H0.
      eapply Forall_forall; intros.
      apply dedup_last_in in H1.
      apply In_rev in H1.
      eapply Forall_forall in H; eauto.
    }
    {
      edestruct dedup_by_list_length
        with (AEQ := addr_dec)
             (l1:= (rev (map fst s0)))
             (l2:= (rev (map snd s0))).

      repeat rewrite rev_length, map_length in *.
      pose proof (dedup_last_length addr_dec (rev (map fst s0))).
      rewrite rev_length in *.
      apply addr_list_to_blocks_length_le_preserve in H4.
      lia.
    }
  }
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

Definition read_finished :
  forall u s o s' r td a,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (read a) (Finished s' r) ->
    s' = s /\
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
  forall u s o s' a,
    exec TransactionCacheLang u o s (read a) (Crashed s') ->
    s' = s.
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
  destruct s; eauto.
  invert_exec; simpl; eauto.
  destruct s; eauto.
  invert_exec; simpl; eauto.
  repeat (
      match goal with
    [H: exec _ _ _ _ _ _ \/ _ |- _] =>
    destruct H
  end; cleanup; simpl in *;
      repeat invert_exec; cleanup;
      simpl in *; eauto); destruct s; eauto.
  eauto.
Qed.


Definition write_finished :
  forall u s o s' r td a v,
    transaction_rep s td ->
    exec TransactionCacheLang u o s (write a v) (Finished s' r) ->
    (transaction_rep s' (upd (fst td) a v, snd td) /\
     s' = ((a, v):: fst s, snd s)) \/
    ((a >= data_length \/
      (a < data_length /\
       length (addr_list_to_blocks (map fst (fst s) ++ [a])) +
             length ((map snd (fst s)) ++ [v]) > log_length)) /\
     s' = s).
Proof.
  unfold write, transaction_rep; intros; cleanup;
  repeat invert_exec; cleanup; simpl in *;
  repeat cleanup_pairs; eauto.
  {
    left; intuition eauto.
    clear D0.
    setoid_rewrite app_length in l0; simpl in *.
    erewrite addr_list_to_blocks_length_eq with (l_b:= (map fst s0 ++ [a])).
    lia.
    simpl; repeat rewrite app_length, map_length; simpl; lia.
    rewrite upd_batch_app; simpl; eauto.
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
  forall u s o s' a v,
    exec TransactionCacheLang u o s (write a v) (Crashed s') ->
    snd s' = snd s.
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
    invert_exec; simpl; eauto.
  }
  {
    simpl; eauto.
  }
Qed.

Definition recover_finished :
  forall u s o s' r td,
    transaction_reboot_rep s td ->
    exec TransactionCacheLang u o s recover (Finished s' r) ->
    transaction_rep s' (snd td, snd td) /\
    fst s' = [].
Proof.
  unfold recover, transaction_reboot_rep, transaction_rep; intros.
  repeat invert_exec; cleanup; repeat cleanup_pairs; simpl; eauto.
  intuition eauto.
  pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.  
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
  split_ors; cleanup; repeat invert_exec; eauto.
Qed.

Definition recover_finished_2 :
  forall u s o s' r td,
    transaction_rep s td ->
    exec TransactionCacheLang u o s recover (Finished s' r) ->
    transaction_rep s' (snd td, snd td) /\ fst s' = [].
Proof.
  unfold recover, transaction_reboot_rep, transaction_rep; intros.
  repeat invert_exec; cleanup; repeat cleanup_pairs; simpl; eauto.
  intuition eauto.
  pose proof (addr_list_to_blocks_length_le []); simpl in *; lia.
Qed.
