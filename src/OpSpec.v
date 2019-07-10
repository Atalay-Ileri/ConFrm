Require Import List BaseTypes Memx Predx SepAuto Prog ProgAuto Hoare.
Open Scope pred_scope.

Theorem read_okay:
  forall a v,
    << u, o, s >>
     (a |-> v)
     (Read a)
    << o', s', r >>
     ([[o = Handle r :: o']] *
      [[s r = None]] *
      [[s' = upd s r (fst v)]] *
      a |-> v)
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    unfold Disk.upd_store.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
  }
Qed.

Theorem write_okay:
  forall a h v v',
    << u, o, s >>
     ([[s h = Some v' ]] * a |-> v)
     (Write a h)
    << o', s', r >>
     ([[s' = s]] *
      [[o' = o]] *
      a |-> (v', (fst v::snd v)))
     (a |-> v).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    unfold Disk.read in *;
    eapply ptsto_valid' in H as Hx;
    cleanup; eauto.  
    unfold Disk.write; cleanup.
    unfold Disk.upd_disk.
    apply sep_star_assoc.
    eapply ptsto_upd'.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
  }
Qed.

Theorem auth_okay:
  forall p,
    << u, o, s >>
     [[True]]
     (Auth p)
    << o', s', r >>
     ([[s' = s]] *
      [[o' = o]] *
      [[(r = true /\ can_access u p) \/
       (r = false /\ ~can_access u p)]])
     [[True]].
Proof.
  intros.
  unfold hoare_triple; intros.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
  }
Qed.

Theorem seal_okay:
  forall p v,
    << u, o, s >>
     [[True]]
     (Seal p v)
    << o', s', r >>
     ([[o = Handle r :: o']] *
      [[s r = None]] *
      [[s' = upd s r (p,v)]])
     [[True]].
Proof.
  intros.
  unfold hoare_triple; intros.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
  }
Qed.


Theorem unseal_okay:
  forall h v,
    << u, o, s >>
     ([[s h = Some v]] *
      [[can_access u (fst v)]])           
     (Unseal h)
    << o', s', r >>
     ([[o' = o]] *
      [[s' = s]] *
      [[r = snd v]])
     [[True]].
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
    do 3 eexists;
      split; eauto.
    pred_apply; cancel.
  }
Qed.

Theorem ret_okay:
  forall T (v: T),
    << u, o, s >>
     [[True]]
     (Ret v)
    << o', s', r >>
     ([[o' = o]] *
      [[s' = s]] *
      [[r = v]])
     [[True]].
Proof.
  intros.
  unfold hoare_triple; intros.
  inv_exec_perm; cleanup.
  {
    split; [|simpl]; auto; left.
    do 4 eexists; split; eauto.
    pred_apply; cancel; eauto.
  }
  {
    split; [|simpl]; auto; right; eauto.
  }
Qed.

