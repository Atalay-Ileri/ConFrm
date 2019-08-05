Require Import Program.Tactics CommonAutomation Prog ProgAuto.
Require Import BaseTypes Disk Confidentiality Simulation.

Lemma exec_preserves_user:
  forall T (p: prog T) st st' tr,
    exec st p st' tr ->
    get_user st = get_user (extract_state st').
Proof.
  induction 1; simpl; intros; simpl in *; cleanup; auto.
Qed.

Theorem trace_ok_to_ret_noninterference:
  forall T (p: prog T),
      ret_noninterference_trace p.
Proof.
  induction p; simpl in *;
    match goal with
    |[H: exec _ (Bind _ _) _ _ |- _] =>
     idtac
    | _ => 
     unfold ret_noninterference_trace, state_equivalent_for, get_user
    end;                                                     
    intros; try specialize H with (1:=H0) as Hx; invert_exec;
  cleanup; simpl in *.
  { (*Read*)
    eapply_fresh equivalent_for_fst_read in H2 ; eauto; cleanup.
    simpl; eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    simpl; eapply equivalent_for_none; eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Read Crash*)
    eexists; intuition eauto.
    eapply ExecReadCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H8; cleanup.
    eapply_fresh equivalent_for_fst_read in H2; eauto; cleanup.
    eapply_fresh equivalent_for_some in H3; eauto; cleanup.
    eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply not_none_iff_some.
    eexists; apply H0.
    auto.
    eapply equivalent_for_fst_write; eauto.
  }
  { (*Write Crash*)
    eexists; intuition eauto.
    eapply ExecWriteCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Success*)
    eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Fail*)
    eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Crash*)
    eexists; repeat split.
    eapply ExecAuthCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Seal*)
    eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply equivalent_for_none; eauto.
    eapply equivalent_for_upd_store; eauto.
  }
  { (*Auth Crash*)
    eexists; intuition eauto.
    eapply ExecSealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Unseal*)
    unfold trace_ok in H2; simpl in *; cleanup.
    eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply equivalent_for_some in H3; eauto; cleanup.
    intuition; cleanup; eauto.
  }
  { (*Unseal Crash*)
    eexists; intuition eauto.
    eapply ExecUnsealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret*)
    eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret Crash*)
    eexists; intuition eauto.
    eapply ExecRetCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Bind*)
      apply trace_ok_app_split in H2; cleanup.
      edestruct IHp; intuition eauto; cleanup.
      instantiate (1:= (u0, o0, d0, s0)); simpl in *.
      simpl; intuition eauto.
      simpl in *; cleanup.

      edestruct H; intuition eauto; cleanup.
      instantiate (1:=s2); simpl; intuition eauto.
      unfold state_equivalent_for in *; cleanup.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.
      simpl; intuition eauto.
      eexists; intuition eauto.
      econstructor; eauto.

      unfold state_equivalent_for in *; cleanup.
      simpl in *; cleanup; intuition eauto.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.
      unfold state_equivalent_for in *; cleanup.
      intuition eauto.
      intuition.
  }
  { (*Bind Crash*)
    destruct H0; cleanup;
    edestruct IHp; eauto; cleanup.
    simpl.

    instantiate (1:= (u0, o0, d0, s0)); simpl; intuition.
    simpl in *; cleanup; intuition.
    
    
    - eexists; intuition eauto.
      eapply ExecBindCrash; eauto.
      simpl; eauto.

    - simpl in *.
      instantiate (1:= (u0, o0, d0, s0)); simpl; intuition.
      
    - apply trace_ok_app_split in H2; cleanup; eauto.
      
    - apply trace_ok_app_split in H2; cleanup; eauto.
      simpl in *; cleanup; intuition.
      
      unfold state_equivalent_for in *; cleanup.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.

      edestruct H; simpl in *; intuition eauto.
      instantiate (1:= (u1, o1, d2, s4)); simpl; intuition eauto.

      simpl in *; cleanup; intuition eauto.
      eexists; intuition eauto.
      econstructor; eauto.
      simpl; unfold state_equivalent_for in *; cleanup.
      intuition eauto.
  }
Qed.


(*
Inductive op : Type -> Type :=
  | Read : addr -> op handle
  | Write : addr -> handle -> op unit
  
  | Auth : permission -> op bool
  | Seal : permission -> value -> op handle
  | Unseal : handle -> op value
.

Inductive tail_prog : Type -> Type :=
| Ret: forall T, T -> tail_prog T
| Op: forall T T', tail_prog T -> (T -> op T') -> tail_prog T'.

Definition op_to_prog {T} (o: op T) : prog T :=
  match o with
  | Read a => Prog.Read a
  | Write a h => Prog.Write a h
  | Auth p => Prog.Auth p
  | Seal p v => Prog.Seal p v
  | Unseal h => Prog.Unseal h
  end.

Set Implicit Arguments.

Fixpoint tail_prog_to_prog {T} (tp: tail_prog T) : prog T :=
  match tp with
  |Ret _ v => Prog.Ret v
  |Op _ _ tp' o => Prog.Bind (tail_prog_to_prog tp') (fun x => op_to_prog (o x))
  end.
 *)


Lemma state_noninterference_bind:
  forall T T' (p1: prog T) (p2: T -> prog T'),
    state_noninterference_trace p1 ->
    (forall t : T, state_noninterference_trace (p2 t)) ->
    state_noninterference_trace (Bind p1 p2).
Proof.
  intros. unfold state_noninterference_trace.
  intros. invert_exec.
  {
    apply trace_ok_app_split in H3; cleanup.
    eapply H in H1.
    edestruct H1; eauto; clear H1; cleanup; simpl in *.
Abort.
  
Theorem trace_ok_to_state_noninterference_op:
  forall T (p: prog T),
      state_noninterference_trace p.
Proof.
  
  induction p; simpl in *;
    match goal with
    |[H: exec _ (Bind _ _) _ _ |- _] =>
     idtac
    | _ => 
     unfold state_noninterference_trace, state_equivalent_for, get_user
    end; intros;
      try specialize H with (1:=H0) as Hx; invert_exec;
  cleanup; simpl in *.
   { (*Read*)
    eapply_fresh equivalent_for_fst_read in H2 ; eauto; cleanup.
    simpl; do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    simpl; eapply equivalent_for_none; eauto.
    all: eapply equivalent_for_upd_store; eauto.
  }
  { (*Read Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecReadCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H8; cleanup.
    eapply_fresh equivalent_for_fst_read in H2; eauto; cleanup.
    eapply_fresh equivalent_for_some in H3; eauto; cleanup.
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply not_none_iff_some.
    eexists; apply H0.
    auto.
    all: eapply equivalent_for_fst_write; eauto.
  }
  { (*Write Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecWriteCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Success*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Fail*)
    do 2 eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Crash*)
    do 2 eexists; repeat split.
    eapply ExecAuthCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Seal*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply equivalent_for_none; eauto.
    all: eapply equivalent_for_upd_store; eauto.
  }
  { (* Seal Crash *)
    do 2 eexists; intuition eauto.
    eapply ExecSealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Unseal*)
    eapply_fresh equivalent_for_some in H3; eauto; cleanup.
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Unseal Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecUnsealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecRetCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Bind*)
      apply trace_ok_app_split in H2; cleanup.
      edestruct IHp; intuition eauto; cleanup.
      instantiate (3:= (u0, o0, d0, s0)); simpl in *.
      simpl; intuition eauto.
      simpl in *; cleanup.
      
      edestruct H; intuition eauto; cleanup.
      instantiate (3:=(u3, o3, d4, s6)); simpl; intuition eauto.
      eapply_fresh exec_preserves_user in H0;
        unfold get_user in *; simpl in *; cleanup.
      inversion D; cleanup.
      inversion D2; cleanup.
      inversion D0; cleanup.
      inversion D4; cleanup.
      do 2 eexists; intuition eauto.
      econstructor; eauto.

      Show finish goes to finish

      unfold state_equivalent_for in *; cleanup.
      simpl in *; cleanup; intuition eauto.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.
      unfold state_equivalent_for in *; cleanup.
      intuition eauto.
      intuition.
  }
Qed.


Theorem trace_ok_to_state_noninterference:
  forall T (tp: tail_prog T),
      state_noninterference_trace (tail_prog_to_prog tp).
Proof.
  induction tp; simpl in *;
  intros; cleanup; simpl in *.

  
  { (*Bind*)
      apply trace_ok_app_split in H1; cleanup.
      edestruct IHtp; intuition eauto; cleanup.
      instantiate (3:= (u0, o1, d0, s0)); simpl in *.
      simpl; intuition eauto.
      simpl in *; cleanup.

      inversion D; cleanup.
      inversion D2; cleanup.
      eapply trace_ok_to_state_noninterference_op in H5.
      edestruct H5.
      unfold state_equivalent_for.
      instantiate (3:= (u1, o2, d2, s3)); simpl in *.
      simpl; intuition eauto.
      eauto.
      simpl in *; cleanup.
      

      edestruct H; intuition eauto; cleanup.
      instantiate (3:=(u3, o3, d4, s6)); simpl; intuition eauto.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.
      do 2 eexists; intuition eauto.
      econstructor; eauto.

      Show finish goes to finish

      unfold state_equivalent_for in *; cleanup.
      simpl in *; cleanup; intuition eauto.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.
      unfold state_equivalent_for in *; cleanup.
      intuition eauto.
      intuition.
  }
  { (*Bind Crash*)
    destruct H0; cleanup;
    edestruct IHp; eauto; cleanup.
    simpl.

    instantiate (1:= (u0, o0, d0, s0)); simpl; intuition.
    simpl in *; cleanup; intuition.
    
    
    - eexists; intuition eauto.
      eapply ExecBindCrash; eauto.
      simpl; eauto.

    - simpl in *.
      instantiate (1:= (u0, o0, d0, s0)); simpl; intuition.
      
    - apply trace_ok_app_split in H2; cleanup; eauto.
      
    - apply trace_ok_app_split in H2; cleanup; eauto.
      simpl in *; cleanup; intuition.
      
      unfold state_equivalent_for in *; cleanup.
      eapply_fresh exec_preserves_user in H0;
      unfold get_user in *; simpl in *; cleanup.

      edestruct H; simpl in *; intuition eauto.
      instantiate (1:= (u1, o1, d2, s4)); simpl; intuition eauto.

      simpl in *; cleanup; intuition eauto.
      eexists; intuition eauto.
      econstructor; eauto.
      simpl; unfold state_equivalent_for in *; cleanup.
      intuition eauto.
  }
Qed.




  
  { (*Read*)
    eapply_fresh equivalent_for_fst_read in H2 ; eauto; cleanup.
    simpl; do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    simpl; eapply equivalent_for_none; eauto.
    all: eapply equivalent_for_upd_store; eauto.
  }
  { (*Read Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecReadCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Write*)
    apply not_none_iff_some in H8; cleanup.
    eapply_fresh equivalent_for_fst_read in H2; eauto; cleanup.
    eapply_fresh equivalent_for_some in H3; eauto; cleanup.
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply not_none_iff_some.
    eexists; apply H0.
    auto.
    all: eapply equivalent_for_fst_write; eauto.
  }
  { (*Write Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecWriteCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Success*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Fail*)
    do 2 eexists; intuition eauto.
    eapply ExecAuthFail; eauto.
    all: simpl; intuition eauto.
  }
  { (*Auth Crash*)
    do 2 eexists; repeat split.
    eapply ExecAuthCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Seal*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
    eapply equivalent_for_none; eauto.
    all: eapply equivalent_for_upd_store; eauto.
  }
  { (* Seal Crash *)
    do 2 eexists; intuition eauto.
    eapply ExecSealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Unseal*)
    eapply_fresh equivalent_for_some in H3; eauto; cleanup.
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Unseal Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecUnsealCrash; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret*)
    do 2 eexists; intuition eauto.
    econstructor; eauto.
    all: simpl; intuition eauto.
  }
  { (*Ret Crash*)
    do 2 eexists; intuition eauto.
    eapply ExecRetCrash; eauto.
    all: simpl; intuition eauto.
  }
  Abort.