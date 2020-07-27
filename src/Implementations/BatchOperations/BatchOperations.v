Require Import Omega Framework CryptoDiskLayer.

  Fixpoint write_consecutive a vl :=
  match vl with
  | nil => Ret tt
  | v::vl' =>
    _ <- |DO| Write a v;
    _ <- write_consecutive (S a) vl';
    Ret tt
  end.

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

Theorem sp_write_batch:
  forall al vl F vsl t s' x,
    length vsl = length vl ->
    length al = length vl ->
    strongest_postcondition CryptoDiskLang (write_batch al vl)
       (fun o s => fst s = x /\ (F * al |L> vsl)%predicate (snd s)) t s' ->
    fst s' = x /\ (F * al |L> (write_all_to_set vl vsl))%predicate (snd s').
Proof.
  induction al; simpl; intros;
  cleanup; simpl in *;
  cleanup; try omega; eauto.
  repeat (apply sp_exists_extract in H1; cleanup).

  edestruct IHal; try omega; eauto.
  eapply sp_impl; eauto.
  simpl; intros.
  instantiate (2:= x).
  cleanup; intuition eauto.
  apply sep_star_assoc.
  eapply ptsto_upd.
  pred_apply; cancel.
  cleanup; intuition eauto.
  pred_apply; cancel.
  eapply sp_extract_precondition in H1; cleanup.
  
  eapply_fresh pimpl_trans in H7.
  eapply ptsto_valid with (a:= a) in Hx; cleanup.
  2: eauto.
  2: cancel.
  cleanup; eauto.
Qed.
  
Theorem sp_decrypt_all:
  forall key evl t s' F,
    strongest_postcondition CryptoDiskLang (decrypt_all key evl)
       (fun o s => F s) t s' ->
    exists plain_blocks, t = plain_blocks /\ evl = map (encrypt key) plain_blocks /\ F s'.
Proof.
  induction evl; simpl; intros;
  cleanup; simpl in *;
  cleanup; try omega; eauto.
  repeat (apply sp_exists_extract in H; cleanup).
  edestruct IHevl.
  eapply sp_impl; eauto.
  simpl; intros; cleanup.  
  instantiate (1:= F); destruct s; eauto.
  cleanup; intuition eauto.
  eexists; intuition eauto.
  simpl.
  eapply sp_extract_precondition in H; cleanup; eauto.
Qed.

Theorem sp_hash_all:
  forall vl h t s' F x,
    strongest_postcondition CryptoDiskLang (hash_all h vl)
       (fun o s => fst s = x /\ F (snd s)) t s' ->
    t = rolling_hash h vl /\
    fst s' = fst s' /\ (** TODO: Fix this **)
    F (snd s').
Proof.
  induction vl; simpl; intros;
  cleanup; simpl in *;
  cleanup; try omega; eauto.
  repeat (apply sp_exists_extract in H; cleanup).
  edestruct IHvl.
  eapply sp_impl; eauto.
  simpl; intros; cleanup.  
  instantiate (1:= F); destruct s; simpl in *; eauto.
  cleanup; intuition eauto.
  eapply sp_extract_precondition in H; cleanup; eauto.
Qed.
