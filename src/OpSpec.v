Require Import List BaseTypes Memx Predx SepAuto Prog ProgAuto Hoare.
Open Scope pred_scope.

Theorem read_can_exec:
  forall a v h o',
    << u, o, s >>
     ([[o = Handle h :: o']] *
      [[s h = None ]] * a |-> v)
     (Read a).
Proof.
  intros.
  unfold can_exec; intros.
  repeat eexists.
  destruct_lift' H; subst.
  instantiate (2:=h).
  eapply ExecRead; eauto.
  unfold Disk.read;
    eapply ptsto_valid' in H;
    cleanup; eauto.  
Qed.

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

Theorem write_can_exec:
  forall a v h v',
    << u, o, s >>
     ([[s h = Some v' ]] * a |-> v)
     (Write a h).
Proof.
  intros.
  unfold can_exec; intros.
  repeat eexists.
  destruct_lift H; subst.
  econstructor; eauto.
  unfold Disk.read;
    eapply ptsto_valid' in H;
    cleanup; eauto.
  intro X; inversion X.
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

Theorem auth_can_exec:
  forall p,
    << u, o, s >>
     [[True]]
     (Auth p).
Proof.
  intros.
  unfold can_exec; intros.
  destruct (can_access_dec u p).
  repeat eexists;
    econstructor; eauto.
  repeat eexists;
  eapply ExecAuthFail; eauto.
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

Theorem seal_can_exec:
  forall h p v o',
    << u, o, s >>
     ([[o = Handle h:: o']] *
      [[s h = None]])
     (Seal p v).
Proof.
  intros.
  unfold can_exec; intros.
  destruct_lift H.
  repeat eexists;
    econstructor; eauto.
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

Theorem unseal_can_exec:
  forall h v,
    << u, o, s >>
     [[s h = Some v]]
     (Unseal h).
Proof.
  intros.
  unfold can_exec; intros.
  destruct_lift H.
  repeat eexists;
    econstructor; eauto.
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

Theorem ret_can_exec:
  forall T (v: T),
    << u, o, s >>
     [[True]]
     (Ret v).
Proof.
  intros.
  unfold can_exec; intros.
  repeat eexists;
    econstructor; eauto.
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