Require Import Mem.
Require Import EquivDec.
Require Import List.
Require Import PeanoNat.
Require Import Nat.
Require Import Omega.
Require Import DisksecDefs.
Import ListNotations.
Set Implicit Arguments.

  
Section Disksec.

Parameter key : Type.
Parameter key_dec : forall k k':key, {k=k'}+{k<>k'}.
Parameter value : Type.

Parameter user : Type.
Parameter user_dec : forall (p p': user), {p = p'}+{p <> p'}.
Parameter permission : Type.

Parameter handle : Type.
Parameter handle_dec : forall k k':handle, {k=k'}+{k<>k'}.

Record State := 
  {
    User : user;
    Disk : @Mem.mem key key_dec (permission * value);
    Mem :  @Mem.mem handle handle_dec (permission * value);
  }.

Parameter can_access: user -> permission -> Prop.
Parameter can_access_dec: forall u p, {can_access u p}+{~can_access u p}.

Definition change_user st u := Build_State u (Disk st) (Mem st).
Definition update_disk st k v := Build_State (User st) (upd (Disk st) k v) (Mem st).
Definition update_mem st k v := Build_State (User st) (Disk st) (upd (Mem st) k v).

Inductive prog : Type -> Type :=
| Read : key -> prog handle
| Write : key -> handle -> prog unit
| Alloc : handle -> prog key
| Seal : permission -> value -> prog handle
| Unseal : handle -> prog value
| Auth : permission -> prog bool
| GetPerm : key -> prog permission
| ChPerm : key -> permission -> prog unit
| Ret : forall T, T -> prog T
| Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.

Inductive exec:
  forall T, State -> prog T -> State -> T -> list permission -> Prop :=
| ExecRead    : forall st a i bs,
    Mem st i = None ->
    Disk st a = Some bs ->
    exec st (Read a) (update_mem st i bs) i []
         
| ExecWrite   : forall st a i b,
    Mem st i = Some b ->
    exec st (Write a i) (update_disk st a b) tt []
         
| ExecSeal : forall i p b st,
    Mem st i = None ->
    exec st (Seal p b) (update_mem st i (p,b)) i []
         
| ExecUnseal : forall st i b,
    Mem st i = Some b ->
    can_access (User st) (fst b) ->
    exec st (Unseal i) st (snd b) [fst b]

| ExecAlloc : forall st i b k,
    Mem st i = Some b ->
    Disk st k = None ->
    exec st (Alloc i) (update_disk st k b) k []
         
| ExecAuthSucc : forall st k,
    can_access (User st) k ->
    exec st (Auth k) st true []
         
| ExecAuthFail : forall st k,
    ~can_access (User st) k ->
    exec st (Auth k) st false []
         
| ExecGetPerm : forall st k b,
    Disk st k = Some b ->
    exec st (GetPerm k) st (fst b) []
         
| ExecChPerm : forall st a p b,
    Disk st a = Some b ->
    can_access (User st) (fst b) ->
    exec st (ChPerm a p) (update_disk st a (p, snd b)) tt [fst b]
         
| ExecRet : forall T st (r: T),
    exec st (Ret r) st r []
         
| ExecBind : forall T T' (p1 : prog T) (p2: T -> prog T') st st' st'' v r tr tr',
    exec st p1 st' v tr ->
    exec st' (p2 v) st'' r tr' ->
    exec st (Bind p1 p2) st'' r (tr++tr').

Definition equivalent {T TEQ} u (m1 m2 : @Mem.mem T TEQ (permission * value)) :=
  forall a,
    (m1 a = None /\ m2 a = None) \/
    (exists vs1 vs2,
       m1 a = Some vs1 /\ m2 a = Some vs2 /\
       fst vs1 = fst vs2 /\
       (can_access u (fst vs1) ->
        snd vs1 = snd vs2)).

Definition equivalent_state (st1 st2: State):=
  User st1 = User st2 /\
  equivalent (User st1) (Disk st1) (Disk st2) /\
  equivalent (User st1) (Mem st1) (Mem st2).

Lemma app_cons_nil:
  forall T (l: list T) a,
    a::l = (a::nil)++l.
Proof.
  intros; simpl; auto.
Qed.

Lemma cons_app_inv_tail :
  forall T (l l': list T) a,
    a::l = l'++l ->
    a::nil = l'.
Proof.
  intros.
  rewrite app_cons_nil in H.
  apply app_inv_tail in H; subst; auto.
Qed.


Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.


Ltac inv_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

Ltac inv_exec' :=
  match goal with
  | [ H: exec _ (Ret _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Read _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Write _ _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Seal _ _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Alloc _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Unseal _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (GetPerm _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (Auth _) _ _ _ |- _ ] =>
    inv_exec'' H
  | [ H: exec _ (ChPerm _ _) _ _ _ |- _ ] =>
    inv_exec'' H
  end.

Lemma bind_sep:
  forall T T' st st' (p1: prog T) (p2: T -> prog T') r tr,
    exec st (Bind p1 p2) st' r tr ->
    (exists st1 r1 tr1 tr2,
       exec st p1 st1 r1 tr1 /\
       exec st1 (p2 r1) st' r tr2 /\
    tr = tr1++tr2).
Proof.
  intros. inv_exec'' H; eauto.
  repeat eexists; eauto.
Qed.

Ltac logic_clean:=
  match goal with
  | [H: exists _, _ |- _] => destruct H; repeat logic_clean
  | [H: _ /\ _ |- _] => destruct H; repeat logic_clean
  end.

Ltac some_subst :=
  match goal with
  | [H: Some _ = Some _ |- _] => inversion H; subst; clear H; repeat some_subst
  end.

Ltac clear_dup:=
  match goal with
  | [H: ?x = ?x |- _] => clear H; repeat clear_dup
  | [H: ?x, H0: ?x |- _] => clear H0; repeat clear_dup
  end.

Ltac rewrite_upd_eq:=
  match goal with
  |[H: upd _ ?x _ ?x = _ |- _] => rewrite upd_eq in H; repeat rewrite_upd_eq; try some_subst
  end.

Ltac rewriteall :=
  match goal with
  | [H: ?x = ?x |- _ ] => clear H; repeat rewriteall
  | [H: ?x = ?y, H0: ?y = ?x |- _ ] => clear H0; repeat rewriteall
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  end.



Ltac clear_trace:=
  match goal with
  | [H: _++?tr = _++?tr |- _] =>
    apply app_inv_tail in H; repeat clear_trace
  | [H: ?tr = _++?tr |- _] =>
    rewrite <- app_nil_l in H at 1; repeat clear_trace
  | [H: _::?tr = _++?tr |- _] =>
    apply cons_app_inv_tail in H; repeat clear_trace
  | [H: _::_++?tr = _++?tr |- _] =>
    rewrite app_comm_cons in H; repeat clear_trace
  | [H: _++_++?tr = _++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  | [H: _++?tr = _++_++?tr |- _] =>
    rewrite app_assoc in H; repeat clear_trace
  end.


Ltac split_match:=
  match goal with
  |[H: context [match ?x with | _ => _ end] |- _] =>
   let name := fresh "D" in
     destruct x eqn:name; repeat split_match
  end.

Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; subst; try rewriteall.

Ltac split_ors:=
  match goal with
  | [H: _ \/ _ |- _ ] => destruct H; cleanup
  end.


Ltac inv_exec_perm :=
  match goal with
  |[H : exec _ (Bind _ _) _ _ _ |- _ ] => apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ |- _ ] => inv_exec'
  end.

Lemma exec_user_eq:
  forall T (p: prog T) st st' r tr,
    exec st p st' r tr ->
    User st = User st'.
Proof.
  induction 1; simpl; eauto.
  rewrite IHexec1; eauto.
Qed.

Theorem single_noninterference:
  forall T (p: prog T) st1 st1' st2 (r: T) tr,
    exec st1 p st1' r tr ->
    equivalent_state st1 st2 ->
    exists st2',
      exec st2 p st2' r tr /\
      equivalent_state st1' st2'.
Proof.
  unfold equivalent_state; induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    destruct bs.
    specialize (H1 r) as Hx; intuition; cleanup; try congruence.
    specialize (H0 k) as Hx; intuition; cleanup; try congruence.
    destruct x0.
    simpl in *.
    eexists; split.
    econstructor; eauto.
    simpl.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (handle_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Write **)
    destruct b; simpl in *.
    specialize (H1 h) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (key_dec a k); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Alloc **)
    specialize (H1 h) as Hx; intuition; cleanup; try congruence.
    specialize (H0 r) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (key_dec a r); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Seal **)
    specialize (H1 r) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (handle_dec a r); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Unseal **)
    specialize (H1 h) as Hx; intuition; cleanup; try congruence.
    specialize (H7 H5).
    eexists; split.
    econstructor; eauto.
    destruct x, x0; simpl in *; cleanup; eauto.
    simpl; rewrite <- H; eauto.
    repeat (split; eauto).
  }
  { (** Auth true **)
    eexists; split.
    econstructor; eauto.
    rewrite <- H; eauto.
    repeat (split; eauto).
  }
  { (** Auth false **)
    eexists; split.
    econstructor; eauto.
    rewrite <- H; eauto.
    repeat (split; eauto).
  }
  { (** GetPerm **)
    specialize (H0 k) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    eexists; split.
    rewrite H5; econstructor; eauto.
    repeat (split; eauto).
  }
  { (** ChPerm **)
    specialize (H0 k) as Hx; intuition; cleanup; try congruence.
    specialize (H6 H7).
    eexists; split.
    econstructor; eauto.
    destruct x, x0; simpl in *; cleanup; eauto.
    simpl; rewrite <- H; eauto.    
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (key_dec a k); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Ret **)
    eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
  }  
  { (** Bind **)
    specialize IHp with (1:=H0); cleanup.
    edestruct IHp; eauto.
    cleanup.
    specialize H with (1:=H4); cleanup.
    edestruct H; eauto.
    cleanup.
    eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
  }
Qed.

Fixpoint no_permission_change {T} (p: prog T) :=
  match p with
  | ChPerm _ _ => False
  | Bind p1 p2 => no_permission_change p1 /\
                 forall v, no_permission_change (p2 v)
  | _ => True
  end.

Theorem viewer_noninterference:
  forall T (p: prog T) viewer st st' st1 (r: T) tr,
    exec st p st' r tr ->
    (forall p, can_access (User st) p -> ~can_access viewer p) ->
    equivalent_state (change_user st viewer) (change_user st1 viewer) ->
    no_permission_change p ->
    User st = User st1 ->
    exists st1' r1,
      exec st1 p st1' r1 tr /\
      equivalent_state (change_user st' viewer) (change_user st1' viewer).
Proof.
  unfold equivalent_state; induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    destruct bs.
    specialize (H4 r) as Hx; intuition; cleanup; try congruence.
    specialize (H1 k) as Hx; intuition; cleanup; try congruence.
    destruct x0.
    simpl in *.
    do 2 eexists; split.
    econstructor; eauto.
    simpl.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (handle_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Write **)
    destruct b; simpl in *.
    specialize (H4 h) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    do 2 eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (key_dec a k); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Alloc **)
    specialize (H4 h) as Hx; intuition; cleanup; try congruence.
    specialize (H1 r) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    do 2 eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (key_dec a r); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Seal **)
    specialize (H4 r) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    do 2 eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
    unfold equivalent; intros.
    destruct (handle_dec a r); subst.
    right; simpl.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    simpl.
    repeat rewrite Mem.upd_ne; eauto.
  }
  { (** Unseal **)
    specialize (H4 h) as Hx; intuition; cleanup; try congruence.
    (* specialize (H7 H5). *)
    do 2 eexists; split.
    rewrite H9.
    econstructor; eauto.
    destruct x, x0; simpl in *; cleanup; eauto.
    simpl; rewrite <- H3; eauto.
    repeat (split; eauto).
  }
  { (** Auth true **)
    do 2 eexists; split.
    econstructor; eauto.
    rewrite <- H3; eauto.
    repeat (split; eauto).
  }
  { (** Auth false **)
    do 2 eexists; split.
    eapply ExecAuthFail; eauto.
    rewrite <- H3; eauto.
    repeat (split; eauto).
  }
  { (** GetPerm **)
    specialize (H1 k) as Hx; intuition; cleanup; try congruence.
    simpl in *.
    do 2 eexists; split.
    econstructor; eauto.
    repeat (split; eauto).
  }
  { (** ChPerm **)
    inversion H2.
  }
  { (** Bind **)
    cleanup.
    apply exec_user_eq in H0 as Hx.
    eapply single_noninterference with (st2:= st1) in H0; eauto.
    cleanup.
    rewrite Hx in H1.
    specialize IHp with (1:= H0)(2:= H1)(4:= H3); cleanup.
    edestruct IHp; eauto.
    admit.
    cleanup.
    specialize (H8 x0).
    apply exec_user_eq in H7 as Hy.
    rewrite <- H4 in H1.
    eapply single_noninterference with (st2:= x3) in H7; eauto.
    cleanup.
    unfold equivalent_state in *; cleanup.
    rewrite H2, <- Hy in H1.
    specialize H with (1:= H7)(2:= H1)(4:= H8); cleanup.
    edestruct H; eauto.
    apply exec_user_eq in H9; rewrite Hy; eauto.
    cleanup; clear H9.
    do 2 eexists; split.
    econstructor; eauto.
Abort.

Definition disksec_layer := Build_Layer prog exec equivalent_state.
Parameter low : Layer.
Parameter refinement : Refinement low disksec_layer.

Definition ret_noninterference {T} (p: prog T):=
  forall st st' st1 r tr,
    exec st p st' r tr ->
    equivalent_state st st1 ->
    exists st1',
      exec st1 p st1' r tr.

Theorem unseal_safe_to_ret_noninterference:
  forall T (p: prog T),
    ret_noninterference p.
Proof.
  unfold ret_noninterference; intros.
  edestruct single_noninterference; eauto.
  destruct H1; eexists; eauto.
Qed.  

Definition state_noninterference {T} (p: prog T):=
  forall viewer st st' st1 r tr,
    exec st p st' r tr ->
    User st <> viewer ->
    equivalent_state (change_user st viewer) (change_user st1 viewer) ->
    exists st1',
      exec st1 p st1' r tr /\
      equivalent_state (change_user st' viewer) (change_user st1' viewer).

