Require Import Lia Framework TotalMem CryptoDiskLayer.

  Fixpoint read_consecutive a count:=
    match count with
    | 0 => Ret nil
    | S count' =>
      v <- |DO| Read a;
      vl <- read_consecutive (S a) count';
    Ret (v::vl)
  end.

Fixpoint write_batch al vl :=
  match al, vl with
  | a::al', v::vl' =>
    _ <- |DO| Write a v;
    _ <- write_batch al' vl';
    Ret tt            
  | _, _ => Ret tt
  end.

Definition write_consecutive a vl := write_batch (seq a (length vl)) vl.
  
Fixpoint encrypt_all k vl :=
  match vl with
  | nil => Ret nil
  | v::vl' =>
    ev <- |CO| Encrypt k v;
    evl' <- encrypt_all k vl';
    Ret (ev::evl')
  end.

Fixpoint decrypt_all k evl :=
  match evl with
  | nil => Ret nil
  | ev::evl' =>
    v <- |CO| Decrypt k ev;
    vl' <- decrypt_all k evl';
    Ret (v::vl')
  end.

Fixpoint hash_all h vl :=
  match vl with
  | nil => Ret h
  | v::vl' =>
    h' <- |CO| Hash h v;
    h'' <- hash_all h' vl';
    Ret h''
  end.


(** Specs **)

Theorem write_batch_finished:
  forall al vl o t s s' u,
    length al = length vl ->
    exec CryptoDiskLang u o s (write_batch al vl) (Finished s' t) ->
    (forall a, In a al -> a < disk_size) /\
    fst s' = fst s /\ snd s' = upd_batch_set (snd s) al vl.
Proof.
  induction al; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  intuition eauto.

  eapply IHal in H0; try lia; cleanup.
  simpl in *; cleanup.
  intuition eauto.
  subst; congruence.
Qed.

Theorem write_batch_crashed:
  forall al vl o s s' u,
    length al = length vl ->
    exec CryptoDiskLang u o s (write_batch al vl) (Crashed s') ->
    exists n,
      n <= length al /\
      (forall a, In a (firstn n al) -> a < disk_size) /\
      fst s' = fst s /\ snd s' = upd_batch_set (snd s) (firstn n al) (firstn n vl).
Proof.
  induction al; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.

  {
    exists 0; split; intuition eauto.
    simpl in *; intuition.
  }
  
  split_ors; cleanup; repeat invert_exec; simpl.
  {
    exists 0; split; intuition eauto; simpl in *.
    lia.
    intuition.
  }

  split_ors; cleanup; repeat invert_exec; simpl in *.
  {
    eapply IHal in H0; try lia.
    cleanup; simpl in *; cleanup.
    exists (S x); split; intuition eauto; simpl in *.
    lia.
    split_ors; cleanup; eauto.
  }
  {
    eapply write_batch_finished in H1; eauto; cleanup.
    simpl in *; cleanup.
    exists (S (length al)).
    simpl.
    repeat rewrite firstn_oob by lia.
    cleanup; split; intuition eauto; simpl in *.
    cleanup.
    eauto.
  }
Qed.


Import Mem.

Theorem decrypt_all_finished:
  forall key evl o s s' t u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Finished s' t) ->
    t = map (decrypt key) evl /\
    consistent_with_upds (snd (fst s)) evl (map (fun ev => (key, decrypt key ev)) evl) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') = upd_batch (snd (fst s)) evl (map (fun ev => (key, decrypt key ev)) evl) /\
    snd s' = snd s.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  edestruct IHevl; eauto; cleanup.
  eexists; intuition eauto.
  repeat cleanup_pairs; eauto.
Qed.

Theorem decrypt_all_crashed:
  forall key evl o s s' u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Crashed s') ->
    exists n,
      consistent_with_upds (snd (fst s)) (firstn n evl) (firstn n (map (fun ev => (key, decrypt key ev)) evl)) /\
      fst (fst s') = fst (fst s) /\
      snd (fst s') = upd_batch (snd (fst s)) (firstn n evl) (firstn n (map (fun ev => (key, decrypt key ev)) evl)) /\
    snd s' = snd s.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  exists 0; simpl; eauto.
  
  split_ors; cleanup; repeat invert_exec.
  exists 0; simpl; eauto.
  
  split_ors; cleanup; repeat invert_exec.
  {
    apply IHevl in H; cleanup.
    exists (S x); simpl; intuition eauto.
    repeat cleanup_pairs; eauto.
    destruct p; eauto.
  }
  {
    eapply decrypt_all_finished in H0; cleanup; eauto.
    exists (S (length evl)); simpl.
    repeat rewrite firstn_oob; try lia.
    intuition eauto.
    repeat cleanup_pairs; eauto.
    destruct p; eauto.
    rewrite map_length; eauto.
  }
Qed.


Theorem hash_all_finished:
  forall vl h o s t s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Finished s' t) ->
    t = rolling_hash h vl /\
    consistent_with_upds (snd (fst (fst s))) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    (snd (fst (fst s'))) = upd_batch (snd (fst (fst s))) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd (fst s') = snd (fst s) /\
    snd s' = snd s.
Proof.
  induction vl; simpl; intros.
  repeat invert_exec; cleanup; intuition eauto.
  repeat invert_exec; cleanup.
  edestruct IHvl; eauto; cleanup.
  simpl in *; intuition eauto.
Qed.

Theorem hash_all_crashed:
  forall vl h o s s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Crashed s') ->
    exists n,
      n <= length (rolling_hash_list h vl) /\
    consistent_with_upds (snd (fst (fst s))) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    (snd (fst (fst s'))) = upd_batch (snd (fst (fst s))) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd (fst s') = snd (fst s) /\
    snd s' = snd s.
Proof.
  induction vl; simpl; intros.
  repeat invert_exec; cleanup; simpl; eauto.
  exists 0; simpl; intuition eauto.
  
  repeat invert_exec; cleanup.
  repeat (split_ors; cleanup; repeat invert_exec; simpl; eauto).
  exists 0; simpl; intuition eauto.
  lia.
  
  edestruct IHvl; eauto; cleanup.
  simpl in *; repeat cleanup_pairs; eauto.
  exists (S x); simpl; intuition eauto.
  lia.
    
  eapply hash_all_finished in H0; cleanup; eauto;
  simpl in *; intuition eauto.
  repeat cleanup_pairs; eauto.
  exists (length (hash_function h a :: rolling_hash_list (hash_function h a) vl)).
  repeat rewrite firstn_oob;
  simpl; intuition eauto.

  generalize vl (hash_function h a).
  induction vl0; simpl; intros; eauto.
  destruct vl0; simpl in *; eauto.
  specialize (IHvl0 (hash_function h1 a0)); lia.
Qed.

Theorem encrypt_all_finished:
  forall key vl o s s' t u,
    exec CryptoDiskLang u o s (encrypt_all key vl) (Finished s' t) ->
    t = map (encrypt key) vl /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) vl) (map (fun v => (key, v)) vl) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') = upd_batch (snd (fst s)) (map (encrypt key) vl) (map (fun v => (key, v)) vl) /\
    snd s' = snd s.
Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.

  - edestruct IHvl; eauto; cleanup.
    eexists; intuition eauto.
    repeat cleanup_pairs; eauto.
Qed.

Theorem encrypt_all_crashed:
  forall key vl o s s' u,
    exec CryptoDiskLang u o s (encrypt_all key vl) (Crashed s') ->
    exists n,
      consistent_with_upds (snd (fst s)) (firstn n (map (encrypt key) vl)) (firstn n (map (fun v => (key, v)) vl)) /\
      fst (fst s') = fst (fst s) /\
      snd (fst s') = upd_batch (snd (fst s)) (firstn n (map (encrypt key) vl)) (firstn n (map (fun v => (key, v)) vl)) /\
    snd s' = snd s.

Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  {
    exists 0; simpl; eauto.
  }

  split_ors; cleanup; repeat invert_exec.
  {
    exists 0; simpl; eauto.
  }
  split_ors; cleanup; repeat invert_exec.
  {
    eapply IHvl in H; eauto; cleanup; eauto.
    exists (S x); simpl; intuition eauto.
    repeat cleanup_pairs; eauto.
    destruct p; simpl in *; eauto.
  }
  {
    eapply encrypt_all_finished in H0; cleanup.
    exists (S (length vl)); simpl.
    repeat rewrite firstn_oob; try lia.
    intuition eauto.
    repeat cleanup_pairs; eauto.
    destruct p; simpl; eauto.
    all: rewrite map_length; eauto.
  }      
Qed.

Theorem read_consecutive_finished:
  forall count a o s s' t u,
    exec CryptoDiskLang u o s (read_consecutive a count) (Finished s' t) ->
    length t = count /\
    (forall i,
       i < count ->
       exists vs,
         (snd s) (a + i) = vs /\
         fst vs = seln t i value0) /\
    s' = s.
Proof.
  induction count; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try solve [intuition eauto; lia].

  edestruct IHcount; eauto; cleanup.
  split; intros; eauto.
  split; intros; eauto.
  destruct i; eauto.
  rewrite PeanoNat.Nat.add_0_r.
  simpl; eexists; eauto.
  simpl.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  eapply H1; lia.
  destruct s; eauto.
Qed.

Theorem read_consecutive_crashed:
  forall count a o s s' u,
    exec CryptoDiskLang u o s (read_consecutive a count) (Crashed s') ->
    s' = s.
Proof.
  induction count; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try solve [intuition eauto; lia].
  repeat (split_ors; cleanup; repeat invert_exec; simpl; eauto).
  destruct s; simpl; eauto.
 
  eapply IHcount; eauto; cleanup.
  destruct s; simpl in *; eauto.
  apply read_consecutive_finished in H0; cleanup; eauto.
  destruct s; eauto.
Qed.

Definition write_consecutive_finished := write_batch_finished.
Definition write_consecutive_crashed := write_batch_crashed.


(* Oracle length versions*)

Definition rec_oracle_op1_crypto n :=
  repeat (OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
    (Token1 CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)) Cont)) n.

Definition rec_oracle_op1_disk n :=
repeat (OpToken
(HorizontalComposition CryptoOperation
(DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
(Token2 CryptoOperation
(DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)) DiskLayer.Cont)) n.
      

Definition rec_oracle_op2 n :=
  repeat (LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))) n.

Definition rec_oracle_finished_crypto n :=
  rec_oracle_op1_crypto n ++
    [LayerImplementation.Cont
    CryptoDiskOperation] ++
    rec_oracle_op2 n.

Definition rec_oracle_finished_disk n :=
  rec_oracle_op1_disk n ++
    [LayerImplementation.Cont
    CryptoDiskOperation] ++
    rec_oracle_op2 n.


Theorem decrypt_all_finished_oracle:
  forall key evl o s s' t u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Finished s' t) ->
    t = map (decrypt key) evl /\
    consistent_with_upds (snd (fst s)) evl (map (fun ev => (key, decrypt key ev)) evl) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') = upd_batch (snd (fst s)) evl (map (fun ev => (key, decrypt key ev)) evl) /\
    snd s' = snd s /\
    o = rec_oracle_finished_crypto (length evl).
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; simpl; eauto.
  intuition eauto.

  edestruct IHevl; eauto; cleanup.
  eexists; intuition eauto.
  repeat cleanup_pairs; eauto.
  unfold rec_oracle_finished_crypto, rec_oracle_op1_crypto, rec_oracle_op2; 
  repeat cleanup_pairs; eauto.
  replace (LayerImplementation.Cont
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
:: repeat
     (LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value
              (fun a0 : addr => a0 < disk_size)))) 
              (length evl)) with 
     (repeat
         (LayerImplementation.Cont
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                  (fun a0 : addr => a0 < disk_size)))) 
         (S (length evl))) by (simpl; eauto).

  rewrite repeat_app_tail.
  repeat rewrite <- app_assoc; simpl; eauto.
Qed.

Definition batch_operations_crypto_crashed_oracle_is o n length_evl :=
  ((n <= length_evl /\ o = rec_oracle_op1_crypto n ++ [OpToken
      (HorizontalComposition CryptoOperation
         (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
      (Token1 CryptoOperation
         (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)) Crash)]) \/
      (n = length_evl /\
       o = rec_oracle_op1_crypto n ++ [LayerImplementation.Crash CryptoDiskOperation]) \/

      (exists k, k < length_evl /\ n = length_evl /\
      o = rec_oracle_op1_crypto n ++ [LayerImplementation.Cont
    CryptoDiskOperation] ++
    rec_oracle_op2 k ++
      [LayerImplementation.Crash
         (HorizontalComposition CryptoOperation
            (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))])).

Theorem decrypt_all_crashed_oracle:
  forall key evl o s s' u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Crashed s') ->
    exists n,
      consistent_with_upds (snd (fst s)) (firstn n evl) (firstn n (map (fun ev => (key, decrypt key ev)) evl)) /\
      fst (fst s') = fst (fst s) /\
      snd (fst s') = upd_batch (snd (fst s)) (firstn n evl) (firstn n (map (fun ev => (key, decrypt key ev)) evl)) /\
      snd s' = snd s /\
      n <= length evl /\
      batch_operations_crypto_crashed_oracle_is o n (length evl).
Proof.
  unfold batch_operations_crypto_crashed_oracle_is;
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  exists 0; simpl; eauto.
  intuition lia.
  
  split_ors; cleanup; repeat invert_exec.
  exists 0; simpl; eauto.
  intuition lia.

  split_ors; cleanup; repeat invert_exec.
  {
    apply IHevl in H; cleanup.
    exists (S x); simpl; intuition eauto;
    cleanup; subst; simpl; intuition (try lia).
    all: repeat cleanup_pairs; eauto.
    all: destruct p; eauto.
    right; right; 
    exists x0.
    unfold rec_oracle_finished_crypto;
    repeat rewrite <- app_assoc;
    simpl; intuition lia.
  }
  {
    eapply decrypt_all_finished_oracle in H0; cleanup; eauto.
    exists (S (length evl)); simpl.
    repeat rewrite firstn_oob; try lia.
    intuition eauto.
    repeat cleanup_pairs; eauto.
    destruct p; eauto.



    right; right; 
    exists (length evl).
    unfold rec_oracle_finished_crypto;
    repeat rewrite <- app_assoc;
    simpl; intuition lia.

    rewrite map_length; eauto.
  }
Qed.

Theorem read_consecutive_finished_oracle:
  forall count a o s s' t u,
    exec CryptoDiskLang u o s (read_consecutive a count) (Finished s' t) ->
    length t = count /\
    (forall i,
       i < count ->
       exists vs,
         (snd s) (a + i) = vs /\
         fst vs = seln t i value0) /\
    s' = s /\
    o = rec_oracle_finished_disk count.
Proof.
  induction count; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try solve [intuition eauto; lia].

  edestruct IHcount; eauto; cleanup.
  split; intros; eauto.
  split; intros; eauto.
  destruct i; eauto.
  rewrite PeanoNat.Nat.add_0_r.
  simpl; eexists; eauto.
  simpl.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  eapply H1; lia.
  simpl in *.

  unfold rec_oracle_finished_disk, rec_oracle_op1_disk, rec_oracle_op2; 
  repeat cleanup_pairs; eauto.
  replace (LayerImplementation.Cont
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
:: repeat
     (LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value
              (fun a0 : addr => a0 < disk_size)))) 
              (length x3)) with 
     (repeat
         (LayerImplementation.Cont
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                  (fun a0 : addr => a0 < disk_size)))) 
         (S (length x3))) by (simpl; eauto).

  rewrite repeat_app_tail.
  repeat rewrite <- app_assoc; simpl; eauto.
Qed.

Definition batch_operations_disk_crashed_oracle_is o n count :=
  ((n <= count /\ o = rec_oracle_op1_disk n ++ [OpToken
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
    (Token2 CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)) DiskLayer.Crash)]) \/
    (n = count /\
     o = rec_oracle_op1_disk n ++ [LayerImplementation.Crash CryptoDiskOperation]) \/

    (exists k, k < count /\ n = count /\
    o = rec_oracle_op1_disk n ++ [LayerImplementation.Cont
  CryptoDiskOperation] ++
  rec_oracle_op2 k ++
    [LayerImplementation.Crash
       (HorizontalComposition CryptoOperation
          (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))])).

Theorem read_consecutive_crashed_oracle:
  forall count a o s s' u,
    exec CryptoDiskLang u o s (read_consecutive a count) (Crashed s') ->
    s' = s /\ 
    exists n, batch_operations_disk_crashed_oracle_is o n count.
Proof.
  unfold batch_operations_disk_crashed_oracle_is;
  induction count; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try solve [intuition eauto; lia].
  repeat (split_ors; cleanup; repeat invert_exec; simpl; eauto).
  destruct s; simpl; intuition eauto.
  exists 0; simpl; intuition lia.

 
  eapply IHcount in H; eauto; cleanup.
  split.
  destruct s; simpl in *; eauto. 
  exists (S x); intuition eauto; cleanup; subst; simpl;
  try intuition lia.
    right; right; exists x0;
    simpl; repeat rewrite <- app_assoc; intuition lia.

  apply read_consecutive_finished_oracle in H0; cleanup; eauto.
  destruct s; intuition eauto.
  exists (S (length x0)).
    right; right; exists (length x0);
    unfold rec_oracle_finished_disk;
    simpl; repeat rewrite <- app_assoc; intuition lia.
Qed.

Theorem encrypt_all_finished_oracle:
  forall key vl o s s' t u,
    exec CryptoDiskLang u o s (encrypt_all key vl) (Finished s' t) ->
    t = map (encrypt key) vl /\
    consistent_with_upds (snd (fst s)) (map (encrypt key) vl) (map (fun v => (key, v)) vl) /\
    fst (fst s') = fst (fst s) /\
    snd (fst s') = upd_batch (snd (fst s)) (map (encrypt key) vl) (map (fun v => (key, v)) vl) /\
    snd s' = snd s /\
    (o = rec_oracle_finished_crypto (length vl)).
Proof.
  unfold rec_oracle_finished_crypto, rec_oracle_op1_crypto, rec_oracle_op2; 
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; simpl; eauto.
  - intuition eauto.
  - edestruct IHvl; eauto; cleanup; subst.
    eexists; intuition eauto.

    repeat cleanup_pairs; eauto.
    replace (LayerImplementation.Cont
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
  :: repeat
       (LayerImplementation.Cont
          (HorizontalComposition CryptoOperation
             (DiskOperation addr_dec value
                (fun a0 : addr => a0 < disk_size)))) 
       (length vl)) with 
       (repeat
           (LayerImplementation.Cont
              (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value
                    (fun a0 : addr => a0 < disk_size)))) 
           (S (length vl))) by (simpl; eauto).
  
    rewrite repeat_app_tail.
    repeat rewrite <- app_assoc; simpl; eauto.
Qed.


Theorem encrypt_all_crashed_oracle:
  forall key vl o s s' u,
    exec CryptoDiskLang u o s (encrypt_all key vl) (Crashed s') ->
    exists n,
      consistent_with_upds (snd (fst s)) (firstn n (map (encrypt key) vl)) (firstn n (map (fun v => (key, v)) vl)) /\
      fst (fst s') = fst (fst s) /\
      snd (fst s') = upd_batch (snd (fst s)) (firstn n (map (encrypt key) vl)) (firstn n (map (fun v => (key, v)) vl)) /\
      snd s' = snd s /\
      batch_operations_crypto_crashed_oracle_is o n (length vl).
Proof.
  unfold batch_operations_crypto_crashed_oracle_is.
  induction vl; simpl; intros;
  cleanup_no_match; simpl in *; 
  repeat invert_exec_no_match;
  cleanup_no_match; try lia; eauto.
  {
    exists 0; simpl; intuition eauto.
  }
  split_ors; cleanup_no_match; 
  repeat invert_exec_no_match.
  {
    exists 0; simpl; intuition eauto.
    intuition lia.
  }
  split_ors; cleanup_no_match; 
  repeat invert_exec_no_match.
  {
    eapply IHvl in H; eauto;
    cleanup_no_match; 
    eauto; simpl.
    exists (S x); simpl; cleanup_no_match; intuition eauto;
    repeat cleanup_pairs; eauto.
    all: try solve [destruct p; simpl in *; eauto].
    simpl; intuition lia.
    right; right; exists x0;
    simpl; intuition lia.
  }
  {
    eapply encrypt_all_finished_oracle in H0; cleanup_no_match.

    exists (S (length vl)); intuition eauto;
    repeat rewrite firstn_oob; simpl; eauto;
    try solve [rewrite map_length; simpl; lia];
    repeat cleanup_pairs; eauto.
    all: try solve [destruct p; simpl in *; eauto].
    right; right; 
    exists (length vl).
    unfold rec_oracle_finished_crypto;
    repeat rewrite <- app_assoc;
    simpl; intuition lia.
  }      
Qed.

Theorem hash_all_finished_oracle:
  forall vl h o s t s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Finished s' t) ->
    t = rolling_hash h vl /\
    consistent_with_upds (snd (fst (fst s))) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    (snd (fst (fst s'))) = upd_batch (snd (fst (fst s))) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd (fst s') = snd (fst s) /\
    snd s' = snd s /\
    (o = rec_oracle_finished_crypto (length vl)).
Proof.
  unfold rec_oracle_finished_crypto, rec_oracle_op1_crypto, rec_oracle_op2;
  induction vl; simpl; intros.
  repeat invert_exec; cleanup; intuition eauto.
  repeat invert_exec; cleanup.
  edestruct IHvl; eauto; cleanup.
  simpl in *; intuition eauto.

    repeat cleanup_pairs; eauto.
    replace (LayerImplementation.Cont
    (HorizontalComposition CryptoOperation
       (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
  :: repeat
       (LayerImplementation.Cont
          (HorizontalComposition CryptoOperation
             (DiskOperation addr_dec value
                (fun a0 : addr => a0 < disk_size)))) 
       (length vl)) with 
       (repeat
           (LayerImplementation.Cont
              (HorizontalComposition CryptoOperation
                 (DiskOperation addr_dec value
                    (fun a0 : addr => a0 < disk_size)))) 
           (S (length vl))) by (simpl; eauto).
  
    rewrite repeat_app_tail.
    repeat rewrite <- app_assoc; simpl; eauto.
Qed.

Lemma rolling_hash_list_length :
forall l h,
length (rolling_hash_list h l) = length l.
Proof.
  induction l; simpl; intuition eauto.
Qed.

Theorem hash_all_crashed_oracle:
  forall vl h o s s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Crashed s') ->
    exists n,
      n <= length (rolling_hash_list h vl) /\
    consistent_with_upds (snd (fst (fst s))) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    (snd (fst (fst s'))) = upd_batch (snd (fst (fst s))) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    fst (fst (fst s')) = fst (fst (fst s)) /\
    snd (fst s') = snd (fst s) /\
    snd s' = snd s /\
    batch_operations_crypto_crashed_oracle_is o n (length vl).
Proof.
  unfold batch_operations_crypto_crashed_oracle_is;
  induction vl; simpl; intros.
  repeat invert_exec; cleanup; simpl; eauto.
  exists 0; simpl; intuition eauto.
  
  repeat invert_exec; cleanup.
  repeat (split_ors; cleanup; repeat invert_exec; simpl; eauto).
  exists 0; simpl; intuition lia.

  edestruct IHvl; eauto; cleanup; subst.
  simpl in *; repeat cleanup_pairs; subst; eauto.
  exists (S x); subst; simpl; intuition (try lia).
  all: try solve [subst; simpl; intuition lia].
  cleanup_no_match; subst; simpl.
  right; right; exists x0;
  simpl; intuition lia.
    
  eapply hash_all_finished_oracle in H0; cleanup; eauto;
  simpl in *; intuition eauto.
  repeat cleanup_pairs; eauto.
  exists (length (hash_function h a :: rolling_hash_list (hash_function h a) vl)).
  repeat rewrite firstn_oob;
  simpl; intuition eauto.
 
  repeat rewrite app_length.
  setoid_rewrite rolling_hash_list_length.
  right; right; exists (length vl);
  unfold rec_oracle_finished_crypto;
  simpl; repeat rewrite <- app_assoc; intuition lia.

  generalize vl (hash_function h a).
  induction vl0; simpl; intros; eauto.
  destruct vl0; simpl in *; eauto.
  specialize (IHvl0 (hash_function h1 a0)); lia.
Qed.


Theorem write_batch_finished_oracle:
  forall al vl o t s s' u,
    length al = length vl ->
    exec CryptoDiskLang u o s (write_batch al vl) (Finished s' t) ->
    (forall a, In a al -> a < disk_size) /\
    fst s' = fst s /\ snd s' = TotalMem.upd_batch_set (snd s) al vl /\
     o = rec_oracle_finished_disk (length al).
Proof.
  induction al; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  intuition eauto.

  eapply IHal in H0; try lia; cleanup.
  simpl in *; cleanup.
  intuition eauto.
  subst; congruence.
  inversion H; subst.
  clear H4.

  unfold rec_oracle_finished_disk, rec_oracle_op1_disk, rec_oracle_op2; 
  repeat cleanup_pairs; eauto.
  replace (LayerImplementation.Cont
  (HorizontalComposition CryptoOperation
     (DiskOperation addr_dec value (fun a0 : addr => a0 < disk_size)))
:: repeat
     (LayerImplementation.Cont
        (HorizontalComposition CryptoOperation
           (DiskOperation addr_dec value
              (fun a0 : addr => a0 < disk_size)))) 
     (length al)) with 
     (repeat
         (LayerImplementation.Cont
            (HorizontalComposition CryptoOperation
               (DiskOperation addr_dec value
                  (fun a0 : addr => a0 < disk_size)))) 
         (S (length al))) by (simpl; eauto).

  rewrite repeat_app_tail.
  repeat rewrite <- app_assoc; simpl; eauto.
Qed.



Theorem write_batch_crashed_oracle:
  forall al vl o s s' u,
    length al = length vl ->
    exec CryptoDiskLang u o s (write_batch al vl) (Crashed s') ->
    exists n,
      n <= length al /\
      (forall a, In a (firstn n al) -> a < disk_size) /\
      fst s' = fst s /\ 
      snd s' = TotalMem.upd_batch_set (snd s) (firstn n al) (firstn n vl) /\
      batch_operations_disk_crashed_oracle_is o n (length al).
Proof.
  unfold batch_operations_disk_crashed_oracle_is;
  induction al; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  {
    exists 0; split; intuition eauto.
    simpl in *; intuition.
  }
  
  split_ors; cleanup; repeat invert_exec; simpl.
  {
    exists 0; split; intuition eauto; simpl in *; 
    intuition (try lia).
  }

  split_ors; cleanup; repeat invert_exec; simpl in *.
  {
    eapply IHal in H0; try lia.
    cleanup; simpl in *; cleanup.
    exists (S x); split; intuition eauto; simpl in *.
    all: try solve [subst; simpl; intuition lia].
    all: try solve [split_ors; cleanup; eauto].
    inversion H; subst.
    clear H6.
    cleanup; subst; simpl.
    right; right; exists x0;
  unfold rec_oracle_finished_disk;
  simpl; repeat rewrite <- app_assoc; intuition lia.
  }
  {
    eapply write_batch_finished_oracle in H1; eauto; cleanup.
    simpl in *; cleanup.
    exists (S (length al)).
    simpl.
    repeat rewrite firstn_oob by lia.
    cleanup; split; intuition eauto; simpl in *.
    cleanup.
    eauto.

    inversion H; subst.
    clear H4.
    cleanup; subst; simpl.
    right; right; exists (length al);
    unfold rec_oracle_finished_disk;
    simpl; repeat rewrite <- app_assoc; intuition lia.
  }
Qed.

Definition write_consecutive_finished_oracle := write_batch_finished_oracle.
Definition write_consecutive_crashed_oracle := write_batch_crashed_oracle.