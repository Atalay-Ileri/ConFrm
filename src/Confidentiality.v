Require Import Primitives.
Close Scope pred_scope.
Set Nested Proofs Allowed.

Lemma deterministic_prog:
  forall T (p: prog T) u o s d ret1 ret2 tr1 tr2,
    exec u o s d p ret1 tr1 ->
    exec u o s d p ret2 tr2 ->
    ret1 = ret2 /\ tr1 = tr2.
Proof.
  induction p; simpl; intros;
    inv_exec_perm; cleanup;
      inv_exec_perm; cleanup; eauto.
  intuition.
  intuition.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  eauto.
  
  destruct H0; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.

  destruct H0; cleanup; destruct H1; cleanup.
  specialize IHp with (1:= H0)(2:=H1); cleanup; eauto.
  
  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.

  specialize IHp with (1:= H0)(2:=H1); cleanup.
  specialize H with (1:= H2)(2:=H3); cleanup.
  eauto.
Qed.

Definition data_except u (d: disk):=
  fun a =>
    match d a with
    | None => d a
    | Some vs =>
      let value := (fst vs) in
      if can_access_dec u (fst value) then
        if permission_dec (fst value) Public then
          d a
        else
          None
      else
        d a
    end.

Definition data_except_store u (s: store):=
  fun a =>
    match s a with
    | None => s a
    | Some value =>
      if can_access_dec u (fst value) then
        if permission_dec (fst value) Public then
          s a
        else
          None
      else
        s a
    end.

Definition equivalent_except u (d1 d2: disk):=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
        d1 a = Some vs1 /\ d2 a = Some vs2 /\
        fst (fst vs1) =  fst (fst vs2) /\
        ((fst (fst vs1) = Public \/ ~can_access u (fst (fst vs1))) ->
         snd (fst vs1) = snd (fst vs2)))%type.

Definition equivalent_except_store u (s1 s2: store):=
  forall a,
    (s1 a = None /\ s2 a = None) \/
    (exists v1 v2,
        s1 a = Some v1 /\ s2 a = Some v2 /\
        fst v1 =  fst v2 /\
        ((fst v1 = Public \/ ~can_access u (fst v1)) ->
         snd v1 = snd v2))%type.

Definition data_of def u (d: disk):=
  fun a =>
    match d a with
    | None => None
    | Some vs =>
      let value := (fst vs) in
      if can_access_dec u (fst value) then
        d a
      else
        Some def
    end.

Definition data_of_store def u (s: store):=
  fun a =>
    match s a with
    | None => None
    | Some value =>
      if can_access_dec u (fst value) then
        s a
      else
        Some def
    end.

Definition equivalent_for u (d1 d2: disk):=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
        d1 a = Some vs1 /\ d2 a = Some vs2 /\
        (can_access u (fst (fst vs1)) ->
        fst vs1 =  fst vs2))%type.

Definition equivalent_for_store u (s1 s2: store):=
  forall a,
    (s1 a = None /\ s2 a = None) \/
    (exists v1 v2,
        s1 a = Some v1 /\ s2 a = Some v2 /\
        (can_access u (fst v1) ->
        v1 = v2))%type.

Lemma data_of_implies_equivalent_for:
  forall u (d1 d2: disk),
    (forall def a, data_of def u d1 a = data_of def u d2 a) ->
    equivalent_for u d1 d2.
Proof. Abort.

Lemma hoare_triple_to_trace_ok:
  forall T (p: prog T) pre post crash,
    hoare_triple pre p post crash ->
    (forall u o s d,
       pre u o s d ->
       (forall ret tr,
          exec u o d s p ret tr ->
          trace_ok tr)).
Proof.
  unfold hoare_triple; intros.
  specialize H with (1:= H0) (2:= H1); cleanup; eauto.
Qed.

Definition ret_noninterference {T} (p: prog T) :=
  forall u o d1 d2 s1 s2 o1' d1' s1' r1 tr1,
    exec u o d1 s1 p (Finished o1' d1' s1' r1) tr1 ->
    equivalent_for u d1 d2 ->
    equivalent_for_store u s1 s2 ->
    trace_ok tr1 ->
    (exists o2' d2' s2' r2 tr2,
      exec u o d2 s2 p (Finished o2' d2' s2' r2) tr2 /\
      equivalent_for u d1' d2' /\
      equivalent_for_store u s1' s2' /\
      tr1 = tr2 /\
      o1' = o2' /\
      r1 = r2)%type.

Lemma equivalent_for_store_none:
  forall u s1 s2 h,
    equivalent_for_store u s1 s2 ->
    s1 h = None ->
    s2 h = None.
Proof.
  unfold equivalent_for_store; simpl; intros.
  specialize (H h); destruct H; cleanup; eauto.
Qed.

Lemma equivalent_for_read:
      forall u d1 d2 a v,
        equivalent_for u d1 d2 ->
        read d1 a = Some v ->
        exists v', read d2 a = Some v' /\
              (can_access u (fst v) ->
              v = v').
Proof.
  unfold read, equivalent_for; simpl; intros.
  specialize (H a); destruct H; cleanup; eauto.
Qed.

Lemma equivalent_for_store_upd_store:
  forall u s1 s2 h v x,
    equivalent_for_store u s1 s2 ->
    (can_access u (fst v) -> v = x) ->
    equivalent_for_store u (upd_store s1 h v) (upd_store s2 h x).
Proof.
  unfold equivalent_for_store, upd_store; simpl; intros.
  destruct (handle_dec a h); subst.
  - repeat rewrite upd_eq; eauto.
    right; eauto.
  - repeat rewrite upd_ne; eauto.
Qed.

Lemma not_none_iff_some:
  forall T (exp: option T),
    exp <> None <->
    exists t, exp = Some t.
Proof.
  intros; split; intros; destruct exp;
  intuition eauto; cleanup.
Qed.

Lemma equivalent_for_store_some:
  forall u s1 s2 h v,
    equivalent_for_store u s1 s2 ->
    s1 h = Some v ->
    exists v', s2 h = Some v' /\
          (can_access u (fst v) -> v = v').
Proof.
  unfold equivalent_for_store; simpl; intros.
  specialize (H h); destruct H; cleanup; eauto.
Qed.

Tactic Notation "eapply_fresh" constr(thm) "in" hyp(H) :=
  let Hx := fresh "Hx" in eapply thm in H as Hx.

Tactic Notation "destruct_fresh" constr(term) :=
  let D := fresh "D" in destruct term eqn:D.

Tactic Notation "assert_fresh" constr(ass) :=
  let A := fresh "A" in assert ass as A.

Lemma trace_ok_app_split:
  forall tr tr',
    trace_ok (tr++tr') ->
    trace_ok tr /\ trace_ok tr'.
Proof.
  induction tr; simpl; intros; eauto.
  destruct a; simpl in *; cleanup; intuition eauto.
  all: specialize IHtr with (1:= H0); cleanup; eauto.
Qed.

Lemma equivalent_for_write:
  forall u d1 d2 a v v',
    equivalent_for u d1 d2 ->
    (can_access u (fst v) -> v = v') ->
    equivalent_for u (write d1 a v) (write d2 a v').
Proof.
  unfold equivalent_for, write, upd_disk; intros.
  specialize (H a0).
  destruct (addr_dec a a0); subst.
  
  destruct_fresh (d1 a0);
  destruct_fresh (d2 a0);
  try solve [destruct H; cleanup].
  repeat rewrite upd_eq; eauto.
  right; do 2 eexists; eauto.
  left; eauto.

  destruct_fresh (d1 a);
  destruct_fresh (d2 a);
  repeat rewrite upd_ne; eauto.
Qed.

Theorem trace_ok_to_ret_noninterference:
  forall T (p: prog T),
    ret_noninterference p.
Proof.
  unfold ret_noninterference; induction p; simpl in *;
  intros; try specialize H with (1:=H0) as Hx; inv_exec_perm.
  { (*Read*)
    eapply_fresh equivalent_for_read in H0 ; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_none; eauto.
    eapply equivalent_for_store_upd_store; eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H16; cleanup.
    eapply_fresh equivalent_for_read in H0; eauto; cleanup.
    eapply_fresh equivalent_for_store_some in H1; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply not_none_iff_some; eauto.
    eapply equivalent_for_write; eauto.
  }
  { (*Auth Success*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
  }
  { (*Auth Fail*)
    do 5 eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
  }
  { (*Seal*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_none; eauto.
    eapply equivalent_for_store_upd_store; eauto.
  }
  { (*Unseal*)
    unfold trace_ok in H2; simpl in *; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_some in H1; eauto; cleanup.
    intuition; cleanup; eauto.
  }
  { (*Ret*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
  }
  { (*Bind*)
      apply trace_ok_app_split in H3; cleanup.
      edestruct IHp; eauto; cleanup.
      edestruct H; eauto; cleanup.
      do 5 eexists; intuition eauto.
      econstructor; eauto.
  }
Qed.

Definition ret_noninterference_precondition {T} (pre: precond) (p: prog T) :=
  forall u o d1 d2 s1 s2 o1' d1' s1' r1 tr1,
    exec u o d1 s1 p (Finished o1' d1' s1' r1) tr1 ->
    equivalent_for u d1 d2 ->
    equivalent_for_store u s1 s2 ->
    pre u o s1 d1 ->
    (exists o2' d2' s2' r2 tr2,
      exec u o d2 s2 p (Finished o2' d2' s2' r2) tr2 /\
      equivalent_for u d1' d2' /\
      equivalent_for_store u s1' s2' /\
      tr1 = tr2 /\
      o1' = o2' /\
      r1 = r2)%type.

Theorem hoare_triple_to_ret_noninterference:
  forall T (p: prog T) pre post crash,
    hoare_triple pre p post crash ->
    ret_noninterference_precondition pre p.
Proof.
  unfold ret_noninterference_precondition; induction p; simpl in *;
  intros; try specialize H with (1:=H0) as Hx; inv_exec_perm.
  { (*Read*)
    eapply_fresh equivalent_for_read in H1 ; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_none; eauto.
    eapply equivalent_for_store_upd_store; eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H17; cleanup.
    eapply_fresh equivalent_for_read in H1; eauto; cleanup.
    eapply_fresh equivalent_for_store_some in H2; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply not_none_iff_some; eauto.
    eapply equivalent_for_write; eauto.
  }
  { (*Auth Success*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
  }
  { (*Auth Fail*)
    do 5 eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
  }
  { (*Seal*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_none; eauto.
    eapply equivalent_for_store_upd_store; eauto.
  }
  { (*Unseal*)
    eapply hoare_triple_to_trace_ok in H3; eauto.
    2: econstructor; eauto.
    unfold trace_ok in H3; simpl in *; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_store_some in H2; eauto; cleanup.
    intuition; cleanup; eauto.
  }
  { (*Ret*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
  }
  { (*Bind*)
    edestruct H0; eauto; cleanup.
    econstructor; eauto.
    eapply trace_ok_to_ret_noninterference; eauto.
    econstructor; eauto.
  }
Qed.