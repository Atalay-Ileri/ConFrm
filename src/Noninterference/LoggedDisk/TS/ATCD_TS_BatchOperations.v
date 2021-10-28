Require Import Eqdep Lia Framework FSParameters CryptoDiskLayer BatchOperations.

Set Nested Proofs Allowed.

  
  Lemma BatchOperations_TS_hash_all:
  forall u l1 l2 s1 s2 o s1' t h1 h2,
  exec (CryptoDiskLang) u o s1 
  (hash_all h1 l1)
       (Finished s1' t) ->
  length l1 = length l2 ->
  consistent_with_upds (snd (fst (fst s2))) (rolling_hash_list h2 l2) (combine (h2:: rolling_hash_list h2 l2) l2) ->
  exists s2' t,
  exec (CryptoDiskLang) u o s2 
  (hash_all h2 l2)
       (Finished s2' t).
  Proof.
    induction l1; destruct l2; simpl in *; try lia;
    intros; repeat invert_exec_no_match.
    do 2 eexists; repeat econstructor.
    simpl in *.
    edestruct IHl1.
    eauto.
    3:{
      simpl in *; logic_clean.
      do 2 eexists; repeat econstructor; eauto.
      rewrite cons_app.
      repeat (econstructor; eauto).
    }
    eauto.
    simpl; eauto.
  Qed.

  Lemma BatchOperations_TS_read_consecutive:
  forall u n s1 s2 o s1' t h1 h2,
  exec (CryptoDiskLang) u o s1 
  (read_consecutive h1 n)
       (Finished s1' t) ->
       h2 + n < disk_size ->
  exists s2' t,
  exec (CryptoDiskLang) u o s2 
  (read_consecutive h2 n)
       (Finished s2' t).
  Proof.
    induction n; simpl in *; try lia;
    intros; repeat invert_exec_no_match.
    do 2 eexists; repeat econstructor.
    simpl in *.
    edestruct IHn.
    eauto.
    2:{
      simpl in *; logic_clean.
      do 2 eexists; repeat econstructor; eauto.
      rewrite cons_app.
      repeat (econstructor; eauto).
      lia.
    }
    lia.
  Qed.


  Lemma BatchOperations_TS_decrypt_all:
forall u l1 l2 k1 k2 s1 s2 o s1' t,

exec (CryptoDiskLang) u o s1 
(decrypt_all k1 l1)
     (Finished s1' t) ->

length l1 = length l2 ->

consistent_with_upds (snd (fst s2)) l2 (map (fun ev => (k2, decrypt k2 ev)) l2) ->

exists s2' t,
exec (CryptoDiskLang) u o s2 (decrypt_all k2 l2) (Finished s2' t).
Proof.
     induction l1; 
     destruct l2; simpl; intros; 
     try lia;repeat invert_exec.
     repeat econstructor.
     eapply IHl1 in H; cleanup.
     do 2 eexists; econstructor; eauto.
     do 3 econstructor; eauto.
     repeat econstructor; eauto.
     all: simpl; eauto.
Qed.


(*************************** Crashed TS ********************)

Lemma BatchOperations_TS_hash_all_crashed:
forall u l1 l2 s1 s2 o s1' h1 h2,
exec (CryptoDiskLang) u o s1 
(hash_all h1 l1) (Crashed s1') ->
length l1 = length l2 ->
consistent_with_upds (snd (fst (fst s2))) (rolling_hash_list h2 l2) (combine (h2:: rolling_hash_list h2 l2) l2) ->
exists s2',
exec (CryptoDiskLang) u o s2 
(hash_all h2 l2) (Crashed s2').
Proof.
  induction l1; destruct l2; simpl in *; try lia;
  intros; repeat invert_exec_no_match.
  eexists; repeat econstructor.

  simpl in *; split_ors; cleanup_no_match.
  repeat invert_exec.
  eexists; repeat econstructor.
  repeat invert_exec_no_match.
  simpl in *; split_ors; cleanup_no_match.
  edestruct IHl1.
  eauto.
  3:{
    eexists; rewrite cons_app.
    repeat (econstructor; eauto).
  }
  eauto.
  simpl; eauto.

  repeat invert_exec_no_match.
  eapply BatchOperations_TS_hash_all in H3; cleanup_no_match.
  eexists; rewrite cons_app.
repeat (econstructor; eauto).
eauto.
simpl; eauto.
Qed.

Lemma BatchOperations_TS_read_consecutive_crashed:
forall u n s1 s2 o s1' h1 h2,
exec (CryptoDiskLang) u o s1 
(read_consecutive h1 n)
     (Crashed s1') ->
     h2 + n < disk_size ->
exists s2',
exec (CryptoDiskLang) u o s2 
(read_consecutive h2 n) (Crashed s2').
Proof.
  induction n; simpl in *; try lia;
  intros; repeat invert_exec_no_match.
  eexists; repeat econstructor.

  simpl in *; split_ors; cleanup_no_match.
  repeat invert_exec.
  eexists; repeat econstructor.
  repeat invert_exec_no_match.
  simpl in *; split_ors; cleanup_no_match.

  edestruct IHn.
  eauto.
  2:{
    eexists; rewrite cons_app.
    repeat (econstructor; eauto).
    lia.
  }
  lia.


  repeat invert_exec_no_match.
  eapply BatchOperations_TS_read_consecutive in H1; cleanup_no_match.
  eexists; rewrite cons_app.
repeat (econstructor; eauto).
all: lia.
Qed.


Lemma BatchOperations_TS_decrypt_all_crashed:
forall u l1 l2 k1 k2 s1 s2 o s1',

exec (CryptoDiskLang) u o s1 
(decrypt_all k1 l1)
   (Crashed s1') ->

length l1 = length l2 ->

consistent_with_upds (snd (fst s2)) l2 (map (fun ev => (k2, decrypt k2 ev)) l2) ->

exists s2',
exec (CryptoDiskLang) u o s2 (decrypt_all k2 l2) (Crashed s2').
Proof.
   induction l1; 
   destruct l2; simpl; intros; 
   try lia;repeat invert_exec.
   repeat econstructor.

   simpl in *; split_ors; cleanup_no_match.
  repeat invert_exec.
  eexists; repeat econstructor.
  repeat invert_exec_no_match.
  simpl in *; split_ors; cleanup_no_match.
  edestruct IHl1.
  eauto.
  3:{
    eexists; rewrite cons_app.
    repeat (econstructor; eauto).
  }
  eauto.
  simpl; eauto.

  repeat invert_exec_no_match.
  eapply BatchOperations_TS_decrypt_all in H3; cleanup_no_match.
  eexists; rewrite cons_app.
repeat (econstructor; eauto).
eauto.
simpl; eauto.
Qed.