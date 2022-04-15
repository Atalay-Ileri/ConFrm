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


Lemma BatchOperations_TS_encrypt_all:
forall u l1 l2 k1 k2 s1 s2 o s1' t,

exec (CryptoDiskLang) u o s1 
(encrypt_all k1 l1)
     (Finished s1' t) ->

length l1 = length l2 ->

consistent_with_upds (snd (fst s2)) (map (encrypt k2) l2) (map (fun v => (k2, v)) l2) ->

exists s2' t,
exec (CryptoDiskLang) u o s2 (encrypt_all k2 l2) (Finished s2' t).
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

Lemma BatchOperations_TS_write_batch:
forall u la1 lv1 la2 lv2 s1 s2 o s1' t,

exec (CryptoDiskLang) u o s1 
(write_batch la1 lv1)
     (Finished s1' t) ->

length la1 = length la2 ->
length lv1 = length lv2 ->

Forall (fun a => a < disk_size) la2 ->

exists s2' t,
exec (CryptoDiskLang) u o s2 (write_batch la2 lv2) (Finished s2' t).
Proof.
     induction la1; 
     destruct la2; simpl; intros; 
     try lia;repeat invert_exec.
     repeat econstructor.

     inversion H2;
     cleanup; destruct lv2; 
     simpl in *; try lia;
     repeat invert_exec;
     try solve [repeat econstructor; eauto].
     edestruct IHla1. 
     eauto.
     3: eauto.
     3: cleanup; repeat econstructor; eauto.
     all: try lia.
Qed.

(*************************** Crashed TS ********************)

Lemma rolling_hash_list_length:
forall l h,
length (rolling_hash_list h l) = length l.
Proof.
induction l; simpl; eauto.
Qed.

Lemma BatchOperations_TS_hash_all_crashed:
forall u l1 l2 s1 s2 o s1' h1 h2,
exec (CryptoDiskLang) u o s1 
(hash_all h1 l1) (Crashed s1') ->
length l1 = length l2 ->
(forall x,
  consistent_with_upds (snd (fst (fst s1))) 
  (firstn x (rolling_hash_list h1 l1))
  (firstn x (combine (h1 :: rolling_hash_list h1 l1) l1)) ->
  consistent_with_upds (snd (fst (fst s2))) 
  (firstn x (rolling_hash_list h2 l2))
  (firstn x (combine (h2 :: rolling_hash_list h2 l2) l2))) ->

exists s2',
exec (CryptoDiskLang) u o s2 
(hash_all h2 l2) (Crashed s2').
Proof.
  Opaque combine.
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
    specialize (H1 1); simpl in *.
    eexists; rewrite cons_app.
    do 4 (econstructor; eauto).
    Transparent combine.
    simpl in *.
    apply H1; eauto.
  }
  eauto.
  simpl; eauto.
  {
     intros.
     specialize (H1 (S x)); simpl in *.
     apply H1; eauto.
  }

  repeat invert_exec_no_match.
  eapply BatchOperations_TS_hash_all in H2; cleanup_no_match.
  specialize (H1 1); simpl in *.
  eexists; rewrite cons_app.
  do 4 (econstructor; eauto).
  apply H1; eauto. 
  eauto.
  {
     specialize (H1 (S (length l1))).
     do 4 rewrite firstn_oob in H1.
     eapply BatchOperations.hash_all_finished in H2; cleanup_no_match.
     apply H1; eauto.
     simpl in *; eauto.
     all: repeat rewrite combine_length;
     simpl length;
     repeat rewrite rolling_hash_list_length;
     lia.
  }
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


Lemma BatchOperations_TS_encrypt_all_crashed:
forall u l1 l2 k1 k2 s1 s2 o s1',

exec (CryptoDiskLang) u o s1 
(encrypt_all k1 l1)
     (Crashed s1') ->

length l1 = length l2 ->

(forall x,
consistent_with_upds (snd (fst s1)) 
(firstn x (map (encrypt k1) l1)) (firstn x (map (fun v => (k1, v)) l1)) ->
consistent_with_upds (snd (fst s2)) 
(firstn x (map (encrypt k2) l2)) (firstn x (map (fun v => (k2, v)) l2))) ->

exists s2',
exec (CryptoDiskLang) u o s2 (encrypt_all k2 l2) (Crashed s2').
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
   specialize (H1 1).
   do 4 (econstructor; eauto).
   simpl in *.
   apply H1; eauto.
 }
 eauto.
 simpl; eauto.
 intros.
 specialize (H1 (S x)); simpl in *; eauto.
 apply H1; eauto.

 repeat invert_exec_no_match.
 eapply BatchOperations_TS_encrypt_all in H2; cleanup_no_match.
 eexists; rewrite cons_app.
 do 4 (econstructor; eauto).
 specialize (H1 1); simpl in *; apply H1; eauto.
 eauto.
 simpl; eauto.
 eapply BatchOperations.encrypt_all_finished in H2.
 simpl in *; cleanup.
 specialize (H1 (S (length l1))); simpl in *; eauto.
 do 4 rewrite firstn_oob in H1.
 apply H1; eauto.
 all: rewrite map_length; lia.
Qed.


Lemma BatchOperations_TS_write_batch_crashed:
forall u la1 lv1 la2 lv2 s1 s2 o s1',

exec (CryptoDiskLang) u o s1 
(write_batch la1 lv1)
     (Crashed s1') ->

length la1 = length la2 ->
length lv1 = length lv2 ->

Forall (fun a => a < disk_size) la2 ->

exists s2',
exec (CryptoDiskLang) u o s2 
(write_batch la2 lv2) (Crashed s2').
Proof.
     induction la1; 
     destruct la2; simpl; intros; 
     try lia;repeat invert_exec.
     repeat econstructor.

     inversion H2;
     cleanup; destruct lv2; 
     simpl in *; try lia;
     repeat invert_exec;
     try solve [repeat econstructor; eauto].

     split_ors; cleanup; repeat invert_exec.
     repeat econstructor.

     split_ors; cleanup; repeat invert_exec.
     edestruct IHla1. 
     eauto.
     3: eauto.
     3: cleanup; repeat econstructor; eauto.
     all: eauto.

     eapply BatchOperations_TS_write_batch in H3.
     cleanup; repeat econstructor; eauto.
     all: eauto.
Qed.