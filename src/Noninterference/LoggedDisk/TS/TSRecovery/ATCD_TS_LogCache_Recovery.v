Require Import Eqdep Lia Framework FSParameters CachedDiskLayer.
Require Import BatchOperations Log LogCache.
Require Import ATCDLayer.
Require Import ATCD_TS_BatchOperations_Recovery ATCD_TS_Log_Recovery.

Set Nested Proofs Allowed.

Lemma combine_same_to_map:
  forall T (l: list T),
  combine l l = map (fun t => (t, t)) l.
  Proof.
    induction l; simpl; eauto.
    rewrite IHl; eauto.
  Qed.


Lemma LogCache_TS_write_batch_to_cache:
forall u l1 l2 l3 l4 s1 s2 o s1' t,
exec CachedDiskLang u o s1 
(LogCache.write_batch_to_cache l1 l3)
     (Finished s1' t) ->
  length l1 = length l2 ->
  length l3 = length l4 ->
exists s2' t,
exec CachedDiskLang u o s2 
(LogCache.write_batch_to_cache l2 l4)
     (Finished s2' t).
Proof.
induction l1; destruct l2; simpl in *;
try lia; intros; repeat invert_exec.
{
  intros; do 2 eexists; repeat econstructor. 
}
{
  cleanup; destruct l4; simpl in *; try lia;
  repeat invert_exec;
  try solve [do 2 eexists; repeat econstructor].
  edestruct IHl1. 
  eauto.
  3: cleanup; do 2 eexists; repeat econstructor; eauto.
  all: eauto.
}
Qed.

Lemma LogCache_TS_write_lists_to_cache:
forall u l1 l2 s1 s2 o s1' t,
exec CachedDiskLang u o s1 
(LogCache.write_lists_to_cache l1)
     (Finished s1' t) ->
  length l1 = length l2 ->
  Forall2 (fun lx ly => length (fst lx) = length (fst ly) /\
  length (snd lx) = length (snd ly)) l1 l2 -> 
exists s2' t,
exec CachedDiskLang u o s2 
(LogCache.write_lists_to_cache l2)
     (Finished s2' t).
Proof.
induction l1; destruct l2; simpl in *;
try lia; intros; repeat invert_exec.
{
  intros; do 2 eexists; repeat econstructor. 
}
{
  inversion H1; cleanup.
  eapply LogCache_TS_write_batch_to_cache with (l2:=fst p) (l4:= snd p)in H; cleanup.
  edestruct IHl1. 
  eauto. 
  3:cleanup; do 2 eexists; repeat econstructor; eauto.
  all: eauto.
}
Qed.


Lemma LogCache_TS_write_batch_to_cache_crashed:
forall u l1 l2 l3 l4 s1 s2 o s1',
exec CachedDiskLang u o s1 
(LogCache.write_batch_to_cache l1 l3)
     (Crashed s1') ->
  length l1 = length l2 ->
  length l3 = length l4 ->
exists s2',
exec CachedDiskLang u o s2 
(LogCache.write_batch_to_cache l2 l4)
     (Crashed s2').
Proof.
induction l1; destruct l2; simpl in *;
try lia; intros; repeat invert_exec.
{
  intros; eexists; repeat econstructor. 
}
{
  cleanup; destruct l4; simpl in *; try lia;
  repeat invert_exec;
  try solve [eexists; repeat econstructor].

  split_ors; cleanup; repeat invert_exec.
  {
    eexists; repeat econstructor; eauto.
  }
  edestruct IHl1. 
  eauto.
  3: cleanup; eexists; repeat econstructor; eauto.
  all: eauto.
}
Qed.

Lemma LogCache_TS_write_lists_to_cache_crashed:
forall u l1 l2 s1 s2 o s1',
exec CachedDiskLang u o s1 
(LogCache.write_lists_to_cache l1)
     (Crashed s1') ->
  length l1 = length l2 ->
  Forall2 (fun lx ly => length (fst lx) = length (fst ly) /\
  length (snd lx) = length (snd ly)) l1 l2 -> 
exists s2',
exec CachedDiskLang u o s2 
(LogCache.write_lists_to_cache l2)
     (Crashed s2').
Proof.
induction l1; destruct l2; simpl in *;
try lia; intros; repeat invert_exec.
{
  intros; eexists; repeat econstructor. 
}
{
  inversion H1; cleanup.
  split_ors; cleanup; repeat invert_exec.
  {
    eapply LogCache_TS_write_batch_to_cache_crashed with (l2:=fst p) (l4:= snd p)in H; cleanup.
    eexists; repeat econstructor; eauto.
    all: eauto.
  }
  eapply LogCache_TS_write_batch_to_cache with (l2:=fst p) (l4:= snd p)in H2; cleanup.
  edestruct IHl1. 
  eauto. 
  3:cleanup; eexists; repeat econstructor; eauto.
  all: eauto.
}
Qed.



Lemma LogCache_TS_recover:
forall u s1 s2 o s1' t txns1 txns2 sa1 sa2 hdr1 hdr2 valid_part,
exec CachedDiskLang u o s1 LogCache.recover
     (Finished s1' t) ->

((exists (hdr_blockset: set value) (log_blocksets: list (set value)),
Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 
txns1 hdr_blockset log_blocksets (snd s1) /\
(valid_part = Log.Old_Part ->
 Log.hash (Log.current_part hdr1) <> 
 rolling_hash hash0 (firstn (Log.count (Log.current_part hdr1)) 
 (map fst log_blocksets)))) /\
sa1 = total_mem_map fst (shift (plus data_start) 
(list_upd_batch_set (snd (snd s1)) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
(forall a, a >= data_start -> snd ((snd (snd s1)) a) = []) /\ 
(forall a vs, snd (snd s1) a = vs -> snd vs = nil)) ->

((exists (hdr_blockset: set value) (log_blocksets: list (set value)),
Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 
txns2 hdr_blockset log_blocksets (snd s2) /\
(valid_part = Log.Old_Part ->
 Log.hash (Log.current_part hdr2) <> 
 rolling_hash hash0 (firstn (Log.count (Log.current_part hdr2)) 
 (map fst log_blocksets)))) /\
sa2 = total_mem_map fst (shift (plus data_start) 
(list_upd_batch_set (snd (snd s2)) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
(forall a, a >= data_start -> snd ((snd (snd s2)) a) = []) /\ 
(forall a vs, snd (snd s2) a = vs -> snd vs = nil)) ->

length txns1 = length txns2 ->

(Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2)) ->

Forall2
(fun rec1 rec2 : Log.txn_record =>
 Log.start rec1 = Log.start rec2 /\
 Log.addr_count rec1 = Log.addr_count rec2 /\
 Log.data_count rec1 = Log.data_count rec2)
(map Log.record txns1)
(map Log.record txns2) ->

exists s2' t,
exec CachedDiskLang u o s2 LogCache.recover
     (Finished s2' t).
Proof.
Transparent LogCache.recover.
Opaque Log.recover.
unfold LogCache.recover in *.
simpl in *; intros;
cleanup; repeat invert_exec.

unfold Log.log_reboot_rep in *.
simpl in *; intros;
cleanup; repeat invert_exec.

eapply_fresh Log_TS_recover in H13; eauto; cleanup.
eapply_fresh Specs.recover_finished in H; eauto.
eapply_fresh Specs.recover_finished in H13; eauto.
all: try solve[unfold Log.log_reboot_rep; 
rewrite <- H3 in *; eauto;
do 4 eexists; intuition eauto].
2:{
  unfold Log.log_reboot_rep; 
do 4 eexists; intuition eauto.
}
eapply LogCache_TS_write_lists_to_cache in H5; cleanup.

do 2 eexists; repeat econstructor; eauto.
rewrite cons_app; repeat econstructor; eauto.
eapply lift2_exec_step; eauto.

do 2 rewrite combine_length; do 4 rewrite map_length; eauto.
apply forall_forall2.
apply Forall_forall; intros.
repeat rewrite <- combine_map' in H14.
apply in_map_iff in H14; cleanup; simpl.

repeat rewrite combine_same_to_map in H15.
rewrite <- combine_map' in H15.
apply in_map_iff in H15; cleanup; simpl.
apply forall2_forall in H4.
eapply Forall_forall in H4; eauto.
2: rewrite <- combine_map'; eapply in_map_iff; eauto.
2:repeat rewrite combine_length_eq; repeat rewrite map_length; eauto.
simpl in *.

unfold Log.log_rep_explicit, Log.log_rep_inner, 
Log.txns_valid in *; logic_clean.
destruct x7; 
eapply_fresh in_combine_l in H15;
eapply_fresh in_combine_r in H15;
simpl in *.

eapply Forall_forall in H24; eauto.
eapply Forall_forall in H32; eauto.
unfold Log.txn_well_formed, Log.record_is_valid in *; logic_clean.
rewrite H35, H46.
split; try lia.
repeat rewrite firstn_length_l; try lia.

Unshelve.
exact CachedDiskLang.
Qed.


Lemma LogCache_TS_recover_crashed:
forall u s1 s2 o s1' txns1 txns2 sa1 sa2 hdr1 hdr2 valid_part,
exec CachedDiskLang u o s1 LogCache.recover (Crashed s1') ->

((exists (hdr_blockset: set value) (log_blocksets: list (set value)),
Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr1 
txns1 hdr_blockset log_blocksets (snd s1) /\
(valid_part = Log.Old_Part ->
Log.hash (Log.current_part hdr1) <> 
rolling_hash hash0 (firstn (Log.count (Log.current_part hdr1)) 
(map fst log_blocksets)))) /\
sa1 = total_mem_map fst (shift (plus data_start) 
(list_upd_batch_set (snd (snd s1)) (map Log.addr_list txns1) (map Log.data_blocks txns1))) /\
(forall a, a >= data_start -> snd ((snd (snd s1)) a) = []) /\ 
(forall a vs, snd (snd s1) a = vs -> snd vs = nil)) ->

((exists (hdr_blockset: set value) (log_blocksets: list (set value)),
Log.log_rep_explicit Log.Hdr_Synced Log.Synced valid_part hdr2 
txns2 hdr_blockset log_blocksets (snd s2) /\
(valid_part = Log.Old_Part ->
Log.hash (Log.current_part hdr2) <> 
rolling_hash hash0 (firstn (Log.count (Log.current_part hdr2)) 
(map fst log_blocksets)))) /\
sa2 = total_mem_map fst (shift (plus data_start) 
(list_upd_batch_set (snd (snd s2)) (map Log.addr_list txns2) (map Log.data_blocks txns2))) /\
(forall a, a >= data_start -> snd ((snd (snd s2)) a) = []) /\ 
(forall a vs, snd (snd s2) a = vs -> snd vs = nil)) ->

length txns1 = length txns2 ->

(Log.count (Log.current_part hdr1) = Log.count (Log.current_part hdr2)) ->

Forall2
(fun rec1 rec2 : Log.txn_record =>
Log.start rec1 = Log.start rec2 /\
Log.addr_count rec1 = Log.addr_count rec2 /\
Log.data_count rec1 = Log.data_count rec2)
(map Log.record txns1)
(map Log.record txns2) ->

exists s2',
exec CachedDiskLang u o s2 LogCache.recover (Crashed s2').
Proof.
Transparent LogCache.recover.
Opaque Log.recover.
unfold LogCache.recover in *.
simpl in *; intros;
cleanup; repeat invert_exec.
split_ors; cleanup; repeat invert_exec.
eexists; repeat econstructor.

unfold Log.log_reboot_rep in *.
simpl in *; intros;
cleanup; repeat invert_exec.

split_ors; cleanup; repeat invert_exec.
{
eapply_fresh Log_TS_recover_crashed in H9; eauto; cleanup.
rewrite cons_app.
eexists; econstructor; eauto.
repeat econstructor.
econstructor.
eapply lift2_exec_step_crashed; eauto.
rewrite <- H3 in *; eauto.
}
{
eapply_fresh Log_TS_recover in H13; eauto; cleanup.
eapply_fresh Specs.recover_finished in H14; eauto.
eapply_fresh Specs.recover_finished in H13; eauto.
all: try solve[unfold Log.log_reboot_rep; 
rewrite <- H3 in *; eauto;
do 4 eexists; intuition eauto].
2:{
  unfold Log.log_reboot_rep; 
do 4 eexists; intuition eauto.
}

eapply LogCache_TS_write_lists_to_cache_crashed in H9; cleanup.
rewrite cons_app.
eexists; repeat econstructor; eauto.
eapply lift2_exec_step; eauto.


repeat rewrite combine_length_eq; repeat rewrite map_length; eauto.
apply forall_forall2.
apply Forall_forall; intros.
repeat rewrite <- combine_map' in H.
apply in_map_iff in H; cleanup; simpl.

repeat rewrite combine_same_to_map in H15.
rewrite <- combine_map' in H15.
apply in_map_iff in H15; cleanup; simpl.
apply forall2_forall in H4.
eapply Forall_forall in H4; eauto.
2: rewrite <- combine_map'; eapply in_map_iff; eauto.
2:repeat rewrite combine_length_eq; repeat rewrite map_length; eauto.
simpl in *.

unfold Log.log_rep_explicit, Log.log_rep_inner, 
Log.txns_valid in *; logic_clean.
destruct x4; 
eapply_fresh in_combine_l in H15;
eapply_fresh in_combine_r in H15;
simpl in *.

eapply Forall_forall in H24; eauto.
eapply Forall_forall in H32; eauto.
unfold Log.txn_well_formed, Log.record_is_valid in *; logic_clean.
rewrite H35, H46.
split; try lia.
repeat rewrite firstn_length_l; try lia.
}
Unshelve.
all: exact CachedDiskLang.
Qed.

