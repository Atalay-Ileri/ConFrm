Require Import List Lia.
Require Import Primitives.BaseTypes Mem.

Lemma get_all_existing_length_le:
  forall A AEQ V (m: @mem A AEQ V) al,
    length (get_all_existing m al) <= length al.
Proof.
  induction al; intros; simpl in *; eauto.
  destruct (m a); simpl in *; eauto.
  lia.
Qed.

Lemma firstn_rolling_hash_list_comm:
  forall n h vl,
    firstn n (rolling_hash_list h vl) = rolling_hash_list h (firstn n vl).
Proof.
  induction n; intros; simpl in *; eauto.
  destruct vl; simpl; eauto.
  rewrite IHn; eauto.
Qed.

Lemma firstn_hash_and_pair_comm:
  forall n h vl,
    firstn n (hash_and_pair h vl) = hash_and_pair h (firstn n vl).
Proof.
  induction n; intros; simpl in *; eauto.
  destruct vl; simpl; eauto.
  rewrite IHn; eauto.
Qed.
