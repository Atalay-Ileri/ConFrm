Require Import BaseTypes Memx Disk CommonAutomation.
Require Import Simulation.

Definition equivalent_for_fst {A AEQ V} u (d1 d2: @mem A AEQ ((permission * V) * list (permission * V))):=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
        d1 a = Some vs1 /\ d2 a = Some vs2 /\
        (can_access u (fst (fst vs1)) ->
        fst vs1 =  fst vs2))%type.

Definition equivalent_for {A AEQ V} u (d1 d2: @mem A AEQ (permission * V)):=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists v1 v2,
        d1 a = Some v1 /\ d2 a = Some v2 /\
        (can_access u (fst v1) ->
        v1 = v2))%type.


Lemma equivalent_for_none:
  forall A AEQ V u s1 s2 h,
    @equivalent_for A AEQ V u s1 s2 ->
    s1 h = None ->
    s2 h = None.
Proof.
  unfold equivalent_for; simpl; intros.
  specialize (H h); destruct H; intuition eauto.
  do 2 destruct H; intuition.
  rewrite H0 in H1; inversion H1.
Qed.

Lemma equivalent_for_fst_read:
      forall u (d1 d2: disk) a v,
        @equivalent_for_fst _ addr_dec _ u d1 d2 ->
        read d1 a = Some v ->
        exists v', read d2 a = Some v' /\
              (can_access u (fst v) ->
              v = v').
Proof.
  unfold read, equivalent_for; simpl; intros.
  specialize (H a); destruct H; intuition eauto.
  rewrite H1 in H0; inversion H0.
  do 2 destruct H; intuition eauto.
  rewrite H1 in H0; inversion H0; subst.
  eexists; rewrite H; eauto.
Qed.

Lemma equivalent_for_upd_store:
  forall u s1 s2 h v x,
    equivalent_for u s1 s2 ->
    (can_access u (fst v) -> v = x) ->
    equivalent_for u (upd_store s1 h v) (upd_store s2 h x).
Proof.
  unfold equivalent_for, upd_store; simpl; intros.
  destruct (handle_dec a h); subst.
  - repeat rewrite upd_eq; eauto.
    right; eauto.
  - repeat rewrite upd_ne; eauto.
Qed.

Lemma equivalent_for_some:
  forall A AEQ V u s1 s2 h v,
    @equivalent_for A AEQ V u s1 s2 ->
    s1 h = Some v ->
    exists v', s2 h = Some v' /\
          (can_access u (fst v) -> v = v').
Proof.
  unfold equivalent_for; simpl; intros.
  specialize (H h); destruct H; intuition eauto.
  rewrite H1 in H0; inversion H0.
  do 2 destruct H; intuition eauto.
  rewrite H1 in H0; inversion H0; subst.
  eexists; rewrite H; eauto.
Qed.

Lemma equivalent_for_fst_write:
  forall u d1 d2 a v v',
    equivalent_for_fst u d1 d2 ->
    (can_access u (fst v) -> v = v') ->
    @equivalent_for_fst _ addr_dec _ u (write d1 a v) (write d2 a v').
Proof.
  unfold equivalent_for_fst, write, upd_disk; intros.
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

Lemma not_none_iff_some:
  forall T (exp: option T),
    exp <> None <->
    exists t, exp = Some t.
Proof.
  intros; split; intros; destruct exp;
    intuition eauto; inversion H0.
  destruct H; inversion H.
Qed.




(*

Theorem trace_ok_to_ret_noninterference:
  forall T (p: prog T),
    ret_noninterference p.
Proof.
  unfold ret_noninterference; induction p; simpl in *;
  intros; try specialize H with (1:=H0) as Hx; inv_exec_perm.
  { (*Read*)
    eapply_fresh equivalent_for_fst_read in H0 ; eauto; cleanup.
    eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_none; eauto.
    do 5 eexists; intuition eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Read Crash*)
    eexists; intuition eauto.
    eapply ExecReadCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H12; cleanup.
    eapply_fresh equivalent_for_fst_read in H0; eauto; cleanup.
    eapply_fresh equivalent_for_some in H1; eauto; cleanup.
    eexists; intuition eauto.
    econstructor; eauto.
    eapply not_none_iff_some; eauto.
    do 5 eexists; intuition eauto.
    eapply equivalent_for_fst_write; eauto.
  }
  { (*Write Crash*)
    eexists; intuition eauto.
    eapply ExecWriteCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Auth Success*)
    eexists; intuition eauto.
    econstructor; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Auth Fail*)
    eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Auth Crash*)
    eexists; intuition eauto.
    eapply ExecAuthCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Seal*)
    eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_none; eauto.
    do 5 eexists; intuition eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Auth Crash*)
    eexists; intuition eauto.
    eapply ExecSealCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Unseal*)
    unfold trace_ok in H2; simpl in *; cleanup.
    eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_some in H1; eauto; cleanup.
    intuition; cleanup; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Unseal Crash*)
    eexists; intuition eauto.
    eapply ExecUnsealCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Ret*)
    eexists; intuition eauto.
    econstructor; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Ret Crash*)
    eexists; intuition eauto.
    eapply ExecRetCrash; eauto.
    do 5 eexists; intuition eauto.
  }
  { (*Bind*)
      apply trace_ok_app_split in H3; cleanup.
      edestruct IHp; eauto; cleanup.
      destruct H7; cleanup.
      edestruct H; eauto; cleanup.
      destruct H10; cleanup.
      eexists; intuition eauto.
      econstructor; eauto.
      do 5 eexists; intuition eauto.
  }
  { (*Bind Crash*)
    destruct H0; cleanup;
    edestruct IHp; eauto; cleanup.

    - destruct H5; cleanup.
      eexists; intuition eauto.
      eapply ExecBindCrash; eauto.
      do 5 eexists; intuition eauto.

    - apply trace_ok_app_split in H3; cleanup; eauto.

    - apply trace_ok_app_split in H3; cleanup; eauto.
      destruct H6; cleanup.
      edestruct H; eauto; cleanup.
      destruct H10; cleanup.
      eexists; intuition eauto.
      econstructor; eauto.
      do 5 eexists; intuition eauto.
  }
Qed.

Definition ret_noninterference_precondition {T} (pre: precond) (p: prog T) :=
  forall u o d1 d2 s1 s2 o1' d1' s1' r1 tr1,
    exec u o d1 s1 p (Finished o1' d1' s1' r1) tr1 ->
    equivalent_for_fst u d1 d2 ->
    equivalent_for u s1 s2 ->
    pre u o s1 d1 ->
    (exists o2' d2' s2' r2 tr2,
      exec u o d2 s2 p (Finished o2' d2' s2' r2) tr2 /\
      @equivalent_for_fst _ addr_dec _ u d1' d2' /\
      @equivalent_for _ handle_dec _ u s1' s2' /\
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
    eapply_fresh equivalent_for_fst_read in H1 ; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_none; eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H17; cleanup.
    eapply_fresh equivalent_for_fst_read in H1; eauto; cleanup.
    eapply_fresh equivalent_for_some in H2; eauto; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply not_none_iff_some; eauto.
    eapply equivalent_for_fst_write; eauto.
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
    eapply equivalent_for_none; eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Unseal*)
    eapply hoare_triple_to_trace_ok in H3; eauto.
    2: econstructor; eauto.
    unfold trace_ok in H3; simpl in *; cleanup.
    do 5 eexists; intuition eauto.
    econstructor; eauto.
    eapply equivalent_for_some in H2; eauto; cleanup.
    intuition; cleanup; eauto.
  }
  { (*Ret*)
    do 5 eexists; intuition eauto.
    econstructor; eauto.
  }
  { (*Bind*)
    edestruct H0; eauto; cleanup.
    econstructor; eauto.
Abort.
(* 
eapply trace_ok_to_ret_noninterference in H1; eauto.
    econstructor; eauto.
  }
Qed.
*)

*)