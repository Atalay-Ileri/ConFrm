Require Import Lia Framework CryptoDiskLayer.

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
  forall al vl o t s s',
    length al = length vl ->
    exec CryptoDiskLang o s (write_batch al vl) (Finished s' t) ->
    (forall a, In a al -> (snd s) a <> None) /\
    fst s' = fst s /\ snd s' = upd_batch_set (snd s) al vl.
Proof.
  induction al; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.

  eapply IHal in H1; try lia; cleanup.
  simpl in *; cleanup.
  intuition eauto.
  subst; congruence.
  destruct (addr_dec a a0); subst; try congruence.
  eapply H0; eauto.
  rewrite upd_ne; eauto.
  unfold upd_set; cleanup; eauto.
Qed.
  
Theorem decrypt_all_finished:
  forall key evl o s s' t,
    exec CryptoDiskLang o s (decrypt_all key evl) (Finished s' t) ->
    exists plain_blocks, t = plain_blocks /\ evl = map (encrypt key) plain_blocks /\ s' = s.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  edestruct IHevl; eauto; cleanup.
  eexists; intuition eauto.
  destruct s; eauto.
Qed.

Theorem hash_all_finished:
  forall vl h o s t s',
    exec CryptoDiskLang o s (hash_all h vl) (Finished s' t) ->
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
  repeat destruct s; destruct p; simpl in *; eauto.
Qed.

Theorem encrypt_all_finished:
  forall key vl o s s' t,
    exec CryptoDiskLang o s (encrypt_all key vl) (Finished s' t) ->
    consistent_with_upds (snd (fst (fst s))) (map (encrypt key) vl) (map (fun v => (key, v)) vl) /\
    t = map (encrypt key) vl /\
    snd s' = snd s /\
fst s' = ((fst (fst (fst s)), upd_batch (snd (fst (fst s))) (map (encrypt key) vl) (map (fun v => (key, v)) vl)), snd (fst s)).
Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try lia; eauto.
  
  - intuition eauto.
    destruct s', s; simpl; intuition eauto.

  - edestruct IHvl; eauto; cleanup.
    eexists; intuition eauto.
Qed.

Theorem read_consecutive_finished:
  forall count a o s s' t,
    exec CryptoDiskLang o s (read_consecutive a count) (Finished s' t) ->
    (forall i,
       i < count ->
       exists vs,
         (snd s) (a + i) = Some vs /\
         fst vs = selN t i value0) /\
    s' = s.
Proof.
  induction count; simpl; intros;
  cleanup; simpl in *; repeat invert_exec;
  cleanup; try solve [intuition eauto; lia].

  edestruct IHcount; eauto; cleanup.
  split; intros; eauto.
  destruct i; eauto.
  rewrite PeanoNat.Nat.add_0_r.
  simpl; eexists; eauto.
  simpl.
  rewrite <- PeanoNat.Nat.add_succ_comm.
  eapply H; lia.
  destruct s; eauto.
Qed.

