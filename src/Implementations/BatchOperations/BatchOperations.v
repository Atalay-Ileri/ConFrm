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

 Fixpoint write_consecutive a vl := write_batch (seq a (length vl)) vl.
  
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
    exists (S x0); split; intuition eauto; simpl in *.
    lia.
    split_ors; cleanup; eauto.
  }
  {
    eapply write_batch_finished in H0; eauto; cleanup.
    simpl in *; cleanup.
    exists (S (length al)).
    simpl.
    repeat rewrite firstn_oob by lia.
    cleanup; split; intuition eauto; simpl in *.
    cleanup.
    eauto.
  }
Qed.
  
Theorem decrypt_all_finished:
  forall key evl o s s' t u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Finished s' t) ->
    t = map (decrypt key) evl /\ s' = s.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  edestruct IHevl; eauto; cleanup.
  eexists; intuition eauto.
  destruct s; eauto.
Qed.

Theorem decrypt_all_crashed:
  forall key evl o s s' u,
    exec CryptoDiskLang u o s (decrypt_all key evl) (Crashed s') ->
    s' = s.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  split_ors; cleanup; repeat invert_exec.
  destruct s; eauto.
  split_ors; cleanup; repeat invert_exec.
  destruct s; eauto.

  eapply decrypt_all_finished in H; cleanup; eauto.
  destruct s; eauto.
Qed.

Import Mem.

Theorem hash_all_finished:
  forall vl h o s t s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Finished s' t) ->
    t = rolling_hash h vl /\
    consistent_with_upds (snd (fst s)) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    (snd (fst s')) = upd_batch (snd (fst s)) (rolling_hash_list h vl) (combine (h:: rolling_hash_list h vl) vl) /\
    fst (fst s') = fst (fst s) /\
    snd s' = snd s.
Proof.
  induction vl; simpl; intros.
  repeat invert_exec; cleanup; eauto.
  repeat invert_exec; cleanup.
  edestruct IHvl; eauto; cleanup.
  simpl in *; intuition eauto.
Qed.

Theorem hash_all_crashed:
  forall vl h o s s' u,
    exec CryptoDiskLang u o s (hash_all h vl) (Crashed s') ->
    exists n,
      n <= length (rolling_hash_list h vl) /\
    consistent_with_upds (snd (fst s)) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    (snd (fst s')) = upd_batch (snd (fst s)) (firstn n (rolling_hash_list h vl)) (firstn n (combine (h:: rolling_hash_list h vl) vl)) /\
    fst (fst s') = fst (fst s) /\
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
  exists (S x0); simpl; intuition eauto.
  lia.
    
  eapply hash_all_finished in H; cleanup; eauto;
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
    s' = s.
Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.

  - edestruct IHvl; eauto; cleanup.
    eexists; intuition eauto.
    destruct s; simpl; eauto.
Qed.

Theorem encrypt_all_crashed:
  forall key vl o s s' u,
    exec CryptoDiskLang u o s (encrypt_all key vl) (Crashed s') ->
    s' = s.
Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.

  - split_ors; cleanup; repeat invert_exec.
    {
      repeat destruct s; simpl; intuition eauto.      
    }
    split_ors; cleanup; repeat invert_exec.
    {
      eapply IHvl; eauto; cleanup; eauto.
      destruct s; simpl in *; eauto.
    }
    {
      eapply encrypt_all_finished in H; cleanup.
      destruct s; simpl; eauto.
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
         fst vs = selN t i value0) /\
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
  apply read_consecutive_finished in H; cleanup; eauto.
  destruct s; eauto.
Qed.

Definition write_consecutive_finished := write_batch_finished.
Definition write_consecutive_crashed := write_batch_crashed.
