Require Import Primitives Simulation.
Import ListNotations.

Set Implicit Arguments.

Module Type Operation.
  Parameter oracle : Type.
  Parameter oracle_dec: forall (o o': oracle), {o = o'}+{o <> o'}.
  Parameter state : Type.
  Parameter op : Type -> Type.
  Parameter exec: forall T, oracle -> state -> op T -> @Result state T -> Prop.
  Parameter oracle_ok : forall T, op T -> oracle -> state -> Prop.
  Parameter exec_deterministic_wrt_oracle :
    forall o s T (p: op T) ret1 ret2,
      exec o s p ret1 ->
      exec o s p ret2 ->
      ret1 = ret2.
  Parameter exec_then_oracle_ok:
    forall T (p: op T) o s r,
      exec o s p r ->
      oracle_ok p o s.
End Operation.

Module Language (Op: Operation).
  Import Op.
  
  Inductive token :=
  | OpOracle : Op.oracle -> token
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
    apply oracle_dec.
  Defined.

  Definition oracle := list token.
  
  Inductive prog : Type -> Type :=
  | Op : forall T, op T -> prog T
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecOp : 
      forall T (p : op T) o s s' r,
        Op.exec o s p (Finished s' r) ->
        exec [OpOracle o] s (Op p) (Finished s' r)
             
  | ExecRet :
      forall d T (v: T),
        exec [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 d1 d1' o2 r ret,
        exec o1 d1 p1 (Finished d1' r) ->
        exec o2 d1' (p2 r) ret ->
        exec (o1++o2) d1 (Bind p1 p2) ret

  | ExecOpCrash : 
      forall T (p : op T) o s s',
        Op.exec o s p (Crashed s') ->
        exec [OpOracle o] s (Op p) (Crashed s')
             
  | ExecRetCrash :
      forall T d (v: T),
        exec [Crash] d (Ret v) (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog T) (p2: T -> prog T')
        o1 o2 d1 d1',
        exec o1 d1 p1 (Crashed d1') ->
        exec (o1++o2) d1 (Bind p1 p2) (Crashed d1').

  Fixpoint oracle_ok {T} (p: prog T) o s :=
    match p with
    | Bind p1 p2 =>
      exists o1 o2,
      o = o1++o2 /\
      oracle_ok p1 o1 s /\
      (forall s' r,
          exec o1 s p1 (Finished s' r) ->
          oracle_ok (p2 r) o2 s') 
    | Op p' =>
      exists o',
      o = [OpOracle o'] /\
      Op.oracle_ok p' o' s
    | Ret _ =>
      o = [Cont] \/ o = [Crash]
    end.

  Definition lts := Build_LTS oracle state prog exec.
  
  Notation "| p |" := (Op p)(at level 60).
  Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
  Notation "x <-| p1 ; p2" := (Bind (Op p1) (fun x => p2))(right associativity, at level 60).
  Hint Constructors exec.

  (* Automation *)
  Local Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

  Local Ltac invert_exec' :=
  match goal with
  | [ H: exec _ _ ?p _ |- _ ] =>
    match p with
    | Bind _ _ => idtac
    | Op _ => invert_exec'' H
    | Ret _ => invert_exec'' H
    end
  end.

Lemma bind_sep:
  forall T T' o d (p1: prog T) (p2: T -> prog T') ret,
    exec o d (Bind p1 p2) ret ->
    match ret with
    | Finished d' r =>
    (exists o1 o2 d1 r1,
       exec o1 d p1 (Finished d1 r1) /\
       exec o2 d1 (p2 r1) ret /\
       o = o1++o2)
  | Crashed d' =>
    (exists o1 o2,
    o = o1++o2 /\    
    (exec o1 d p1 (Crashed d') \/
     (exists d1 r1,
        exec o1 d p1 (Finished d1 r1) /\
        exec o2 d1 (p2 r1) ret)))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  do 2 eexists; split; eauto.
Qed.

Ltac invert_exec :=
  match goal with
  |[H : exec _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ |- _ ] =>
   invert_exec'
  end.


  Definition prog_equiv T : prog T -> prog T -> Prop :=
    fun p1 p2 => forall o d out,
        exec o d p1 out <-> exec o d p2 out.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - repeat invert_exec; cleanup.
      rewrite <- app_assoc.
      repeat econstructor; eauto.

      split_ors.
      invert_exec; cleanup.
      split_ors; cleanup.
      rewrite <- app_assoc.
      eapply ExecBindCrash; auto.

      rewrite <- app_assoc.
      econstructor; eauto.
      
      invert_exec.
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    
    - repeat invert_exec; cleanup.
      rewrite app_assoc.
      repeat (eapply ExecBind; eauto).
      
      split_ors.
      replace (x ++ x0) with ((x ++ x0)++[]) by (apply app_nil_r).
      eapply ExecBindCrash; eauto.
      
      invert_exec.
      split_ors.
      rewrite app_assoc.
      eapply ExecBindCrash; eauto.
      
      rewrite app_assoc.
      repeat econstructor; eauto.
  Qed.

  (* Facts *)

  (*
Lemma exec_crash_in:
  forall T (p: prog T) o d d',
    exec o d p (Crashed d') ->
    In Crash o.
Proof.
  induction p; simpl in *; intros;
    try invert_exec; intuition; eauto.
  cleanup.
  apply in_app_iff; eauto.
Qed.
*)

Lemma exec_finished_deterministic_prefix:
  forall T (p: prog T) o1 o2 o3 o4 s s1 s2 r1 r2,
      exec o1 s p (Finished s1 r1) ->
      exec o2 s p (Finished s2 r2) ->
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  eapply Op.exec_deterministic_wrt_oracle in H7; eauto; cleanup; eauto.
  
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H0)(2:= H1)(3:=H2); cleanup.
  apply app_inv_head in H2.
  specialize H with (1:= H4)(2:= H3)(3:=H2); cleanup; eauto.
Qed.

Lemma finished_not_crashed_oracle_prefix:
  forall T (p: prog T) o1 o2 o3 o4 s s1 s2 r1,
    exec o1 s p (Finished s1 r1) ->
    o1 ++ o3 = o2 ++ o4 ->
    ~exec o2 s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup); simpl; eauto.
  eapply exec_deterministic_wrt_oracle in H7; eauto; cleanup.
  
  split_ors; cleanup.
  -
    repeat rewrite <- app_assoc in H1; eauto.
  -
    repeat rewrite <- app_assoc in H1; eauto.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    apply app_inv_head in H1; cleanup; eauto.
Qed.

Lemma finished_not_crashed_oracle_app:
  forall T (p: prog T) o1 o2 s s1 s2 r1,
    exec o1 s p (Finished s1 r1) ->
    ~exec (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup); simpl; eauto.
  eapply exec_deterministic_wrt_oracle in H6; eauto; cleanup.
  
  split_ors; cleanup.
  -
    rewrite <- app_assoc in H1; eauto.
    clear H3; eapply finished_not_crashed_oracle_prefix; eauto.
  -
    rewrite <- app_assoc in H1; eauto.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    apply app_inv_head in H1; cleanup; eauto.
Qed.

Lemma exec_deterministic_wrt_oracle_prefix:
      forall T (p: prog T) o1 o2 x1 x2 s ret1 ret2,
      exec o1 s p ret1 -> 
      exec x1 s p ret2 ->
      o1 ++ o2 = x1 ++ x2 ->
      ret1 = ret2.
    Proof.
       induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  -
    eapply Op.exec_deterministic_wrt_oracle; eauto.
  -
    eapply Op.exec_deterministic_wrt_oracle in H6; eauto; cleanup.
  -
    eapply Op.exec_deterministic_wrt_oracle in H6; eauto; cleanup.
  -
    eapply Op.exec_deterministic_wrt_oracle; eauto; cleanup.
  -
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    repeat rewrite <- app_assoc in H2.
    apply app_inv_head in H2; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; eauto.
  -
    split_ors; cleanup.
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    apply app_inv_head in H2; cleanup; eauto.
    
  -
    split_ors; cleanup.
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H0)(2:=H3)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    apply app_inv_head in H2; cleanup; eauto.
  -
    repeat split_ors; cleanup.
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:= H1)(2:= H0)(3:=H2); cleanup; eauto.

    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H1)(2:=H0)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H1)(2:=H0)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2.
    eapply exec_finished_deterministic_prefix in H1; eauto; cleanup; eauto.
    apply app_inv_head in H2; cleanup; eauto.
    Qed.

    (*
Lemma oracle_nonempty_app_not_crashed:
  forall T (p: prog T) o1 o2 s s1 ret,
    exec o1 s p ret ->
    o2 <> [] ->
    ~exec (o1++o2) s p (Crashed s1).
Proof.
  unfold not; induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup); simpl; eauto.
  
  -
    split_ors; cleanup.
  +
    rewrite <- app_assoc in H2; eauto.
    clear H4; eapply finished_not_crashed_oracle_prefix; eauto. 
  +
    rewrite <- app_assoc in H2; eauto.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    apply app_inv_head in H2; cleanup; eauto.

  -   
    repeat split_ors; cleanup; eauto.
  +
    rewrite <- app_assoc in H2; eauto.
    Lemma exec_crashed_oracle_prefix:
      forall o1 o2 s s1 s2 T (p: prog T),
        exec o1 s p (Crashed s1) ->
        exec o2 s p (Crashed s2) ->
        exists o, o1 = o2++o \/ o1++o = o2.
    Admitted.

    eapply exec_crashed_oracle_prefix in H3 as Hx; eauto; cleanup.
    split_ors; cleanup.
    *
      rewrite <- app_assoc in H2; eauto.
      apply app_inv_head in H2; cleanup; eauto.
      
    specialize IHp with (1:=H3)(3:=H0).
    apply IHp; eauto.
    intros; apply H1; cleanup; simpl in *.
    apply app_inv_head in H2; cleanup; eauto.
    apply app_eq_nil in H4; cleanup; eauto.
  +
    eapply exec_deterministic_wrt_oracle_prefix in H0; eauto; cleanup.    
  +
    rewrite <- app_assoc in H4; eauto.
    eapply exec_finished_deterministic in H0; eauto; cleanup; eauto.
    apply app_inv_head in H4; cleanup; eauto.
    
Qed.

*)

Lemma exec_deterministic_wrt_oracle:
  forall T (p: prog T) o s r1 r2,
      exec o s p r1 ->
      exec o s p r2 ->
      r1 = r2.
Proof.
  intros.
  eapply exec_deterministic_wrt_oracle_prefix; eauto.
  Unshelve.
  eauto.
Qed.

  Lemma oracle_ok_nonempty:
    forall T (p: prog T) s,
      ~oracle_ok p [] s.
  Proof.
    unfold not;
      induction p; simpl; intros; try (split_ors; cleanup); try intuition congruence.
    cleanup; inversion H. 
    cleanup; symmetry in H0; apply app_eq_nil in H0; cleanup; eauto.
  Qed.

  Lemma oracle_ok_bind_assoc:
    forall T T' T'' (p1: prog T) (p2: T -> prog T') (p3: T' -> prog T'') o sl,
      oracle_ok (Bind (Bind p1 p2) p3) o sl ->
      oracle_ok (Bind p1 (fun x => (Bind (p2 x) p3))) o sl.      
  Proof.
    intros; simpl in *; cleanup.
    exists x1, (x2++x0).
    split.
    rewrite app_assoc; eauto.
    intuition eauto.
    specialize H3 with (1:= H).
    do 2 eexists; intuition eauto.
  Qed.
  
  Lemma oracle_ok_bind_finished_split:
    forall T T' (p1: prog T) (p2: T -> prog T') o1 o2 sl sl' r ret,
      exec o1 sl p1 (Finished sl' r) ->
      exec o2 sl' (p2 r) ret ->
      oracle_ok (Bind p1 p2) (o1 ++ o2) sl ->
      oracle_ok p1 o1 sl /\
      oracle_ok (p2 r) o2 sl'.      
  Proof.
    induction p1; simpl; intros;
    try solve [  pose proof H;
      simpl in *; intuition;
        invert_exec; simpl in *; cleanup;
      split_ors; cleanup; inversion H1; subst; eauto;
      specialize H3 with (1:= H); eauto].
    invert_exec; simpl in *; cleanup; simpl in *; split;
      inversion H; subst; eauto.
    
    invert_exec.
    repeat rewrite <- app_assoc in H2.
    specialize (IHp1 (fun x => Bind (p x) p2)) with (1:=H0).
    edestruct IHp1.
    econstructor; eauto.
    rewrite H2.
    econstructor; eexists; intuition eauto.
    specialize H6 with (1:=H3).
    econstructor; eexists; intuition eauto.

    specialize H with (1:=H7)(2:= H1).
    destruct H; intuition eauto.
    
    simpl in *; cleanup.
    
    do 2 eexists; intuition eauto.
    eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup; eauto.
  Qed.
(*
  Lemma oracle_ok_finished_eq:
    forall T (p: prog T) o1 o2 o1' o2' s s' r,
      exec o1 s p (Finished s' r) ->
      o1 ++ o2 = o1' ++ o2' ->
      oracle_ok p o1' s ->
      o1 = o1' /\ o2 = o2'.
  Proof.
    induction p; simpl; intros;
    try solve [ unfold oracle_ok in *; intuition;
                invert_exec; simpl in *; cleanup; eauto ].
    invert_exec; cleanup.
     repeat rewrite <- app_assoc in H1.
     specialize IHp with (1:= H0)(2:= H1)(3:=H3); cleanup.
     specialize H4 with (1:= H0).
     specialize H with (1:= H6)(2:= H7)(3:=H4); cleanup; eauto.
  Qed.     

  Lemma oracle_ok_exec_crashed_app_nil:
    forall T (p: prog T) o1 o2 s s',
      exec (o1++o2) s p (Crashed s') ->
      oracle_ok p o1 s ->
      o2=[].
  Proof.
     induction p; simpl; intros;
     try solve [ intuition; invert_exec; simpl in *; cleanup; eauto].
     split_ors; cleanup; invert_exec; eauto.
     
     invert_exec; split_ors; cleanup.

     -
       rewrite <- app_assoc in H0.
       specialize IHp with (1:= H0)(2:=H2).
       apply app_eq_nil in IHp; cleanup; eauto.

     -
       rewrite <- app_assoc in H5.
       symmetry in H5.
       eapply_fresh oracle_ok_finished_eq in H0; eauto; cleanup.
       specialize H3 with (1:=H0).
       specialize H with (1:= H1)(2:=H3); eauto.
  Qed.

   Lemma oracle_ok_bind_crashed_split:
    forall T T' (p1: prog T) (p2: T -> prog T') o1 sl sl',
      exec o1 sl p1 (Crashed sl') ->
      oracle_ok (Bind p1 p2) o1 sl ->
      oracle_ok p1 o1 sl.      
  Proof.
    intros; simpl in *; cleanup.
    eapply_fresh oracle_ok_exec_crashed_app_nil in H; eauto; cleanup.
    rewrite app_nil_r; eauto.
  Qed.
*)
   Lemma exec_then_oracle_ok:
    forall T (p: prog T) o s r,
      exec o s p r ->
      oracle_ok p o s.
  Proof.
    induction p; simpl; intros; try solve [invert_exec; cleanup; simpl; eauto].
    invert_exec; cleanup; simpl; eauto; eapply exec_then_oracle_ok in H5; eauto.
    
    invert_exec.
    - specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup; eauto.
    -
      split_ors; cleanup.
      specialize IHp with (1:= H0).
      do 2 eexists; intuition; eauto;
        eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup; eauto.

      specialize IHp with (1:= H0).
      specialize H with (1:=H1).
      do 2 eexists; intuition; eauto;
        eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup; eauto.
  Qed.

  (*
  Lemma finished_crash_not_in:
    forall T (p: prog T) s s' o r,
      exec o s p (Finished s' r) ->
      ~In Crash o.
  Proof.
    induction p; simpl; intros; invert_exec; cleanup; simpl; intuition eauto; try congruence.
    apply in_app_iff in H2; intuition eauto.
  Qed.
  *)


End Language.

