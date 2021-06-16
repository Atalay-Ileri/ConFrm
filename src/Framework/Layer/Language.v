Require Import Primitives Layer.Core Lia.
Import ListNotations.

Set Implicit Arguments.

Section Language.
  
  Variable O: Core.

  Inductive token' :=
  | OpToken : O.(token) -> token'
  | Crash : token'
  | Cont : token'.

  Definition oracle' := list token'.

  Definition state' := O.(state).
  
  Inductive prog' : Type -> Type :=
  | Op : forall T, O.(operation) T -> prog' T
  | Ret : forall T, T -> prog' T
  | Bind : forall T T', prog' T -> (T -> prog' T') -> prog' T'.
  
  Inductive exec' :
    forall T, user -> oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecOp : 
      forall T (p : O.(operation) T) u o s s' r,
        O.(exec) u o s p (Finished s' r) ->
        exec' u [OpToken o] s (Op T p) (Finished s' r)
             
  | ExecRet :
      forall d T (v: T) u,
        exec' u [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog' T) (p2: T -> prog' T')
        u o1 d1 d1' o2 r ret,
        exec' u o1 d1 p1 (Finished d1' r) ->
        exec' u o2 d1' (p2 r) ret ->
        exec' u (o1++o2) d1 (Bind p1 p2) ret

  | ExecOpCrash : 
      forall T (p : O.(operation) T) u o s s',
        O.(exec) u o s p (Crashed s') ->
        exec' u [OpToken o] s (Op T p) (Crashed s')
             
  | ExecRetCrash :
      forall T d (v: T) u,
        exec' u [Crash] d (Ret v) (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog' T) (p2: T -> prog' T')
        u o1 d1 d1',
        exec' u o1 d1 p1 (Crashed d1') ->
        exec' u o1 d1 (Bind p1 p2) (Crashed d1').

  Inductive recovery_exec' :
    forall T, user -> list oracle' -> state' -> list (state' -> state') -> prog' T -> prog' unit -> @Recovery_Result state' T -> Prop :=
  | ExecFinished :
      forall T (p: prog' T) p_rec
        u o d d' t,
        exec' u o d p (Finished d' t) ->
        recovery_exec' u [o] d [] p p_rec (RFinished d' t)
  | ExecRecovered :
      forall T (p: prog' T) p_rec
        u o lo d d' get_reboot_state l_grs ret,
        exec' u o d p (Crashed d') ->
        recovery_exec' u lo (get_reboot_state d') l_grs p_rec p_rec ret ->
        recovery_exec' u (o::lo) d (get_reboot_state::l_grs) p p_rec (Recovered (extract_state_r ret)).
  
  Hint Constructors exec' : core.

  Record Language :=
    {
      token := token';
      oracle := oracle';
      state := state';
      prog := prog';
      exec := exec';
      recovery_exec := recovery_exec';
    }.

End Language.

Arguments Ret {O T}.
Arguments Op O {T}.
Hint Extern 1 (Language.exec _ _ _ _ (Op _ _) (Finished _ _)) => eapply (ExecOp _) : core.
Notation "| p |" := (Op _ p)(at level 60).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op _ p1) (fun x => p2))(right associativity, at level 60).




 (** Facts **)

 Lemma exec_empty_oracle:
      forall O (L: Language O) T (p: prog L T) u s s',
      ~ exec L u [] s p s'.
      induction p; unfold not; intros.
      inversion H; cleanup.
      inversion H; cleanup.
      inversion H0; cleanup.
      apply app_eq_nil in H1; cleanup.
      simpl in *; eauto.
      eapply IHp; eauto.
      eapply IHp; eauto.
  Qed.

Lemma exec_finished_deterministic_prefix:
  forall O (L: Language O) T (p: prog L T) u o1 o2 o3 o4 s s1 s2 r1 r2,
      exec L u o1 s p (Finished s1 r1) ->
      exec L u o2 s p (Finished s2 r2) -> 
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    (try inversion H; try inversion H0; try inversion H1; simpl in *; cleanup);
    simpl in *; cleanup;
    simpl; eauto; try solve [intuition].
  
  eapply O.(exec_deterministic_wrt_token) in H8; eauto; cleanup; eauto.
  
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H9)(2:= H19)(3:=H2); cleanup.
  specialize H with (1:= H12)(2:= H22)(3:=H2); cleanup; eauto.
Qed.

Lemma finished_not_crashed_oracle_prefix:
  forall O (L: Language O) T (p: prog L T) u o1 o2 o3 o4 s s1 s2 r1,
    exec L u o1 s p (Finished s1 r1) ->
    o1 ++ o3 = o2 ++ o4 ->
    ~exec L u o2 s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
  (try inversion H; try inversion H0; try inversion H1;
    try inversion H2; simpl in *; cleanup);
  simpl in *; cleanup; simpl; eauto.
  eapply exec_deterministic_wrt_token in H8; eauto; cleanup.
  -
    repeat rewrite <- app_assoc in H1; eauto.
    eapply exec_finished_deterministic_prefix in H9; eauto; cleanup; eauto.
  -
    repeat rewrite <- app_assoc in H1; eauto.
    Unshelve.
    eauto.
Qed.

Lemma finished_not_crashed_oracle_app:
  forall O (L: Language O) T (p: prog L T) u o1 o2 s s1 s2 r1,
    exec L u o1 s p (Finished s1 r1) ->
    ~exec L u (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
  (try inversion H; try inversion H0; try inversion H1;
    try inversion H2; simpl in *; cleanup);
  simpl in *; cleanup; simpl; eauto.
  eapply exec_deterministic_wrt_token in H7; eauto; cleanup.

  - rewrite <- app_assoc in H12; eauto.
    eapply exec_finished_deterministic_prefix in H8; eauto; cleanup; eauto.
    
  - rewrite <- app_assoc in H17; eauto.
    Unshelve.
    all: eauto.  
Qed.

Lemma exec_deterministic_wrt_oracle_prefix:
      forall O (L: Language O) T (p: prog L T) u o1 o2 x1 x2 s ret1 ret2,
      exec L u o1 s p ret1 -> 
      exec L u x1 s p ret2 ->
      o1 ++ o2 = x1 ++ x2 ->
      ret1 = ret2.
    Proof.
       induction p; simpl; intros;
    (try inversion H; try inversion H0; try inversion H1;
    try inversion H2; simpl in *; cleanup);
  simpl in *; cleanup;
    simpl; eauto; try solve [intuition].
  -
    eapply O.(exec_deterministic_wrt_token); eauto.
  -
    eapply O.(exec_deterministic_wrt_token) in H8; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_token) in H8; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_token); eauto; cleanup.
  -
    eapply exec_finished_deterministic_prefix in H9; eauto; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; eauto.
  -
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H9)(2:=H18)(3:=H2); cleanup.

  - repeat rewrite <- app_assoc in H2.
    specialize IHp with (1:=H8)(2:=H18)(3:=H2); cleanup.
  -
    repeat rewrite <- app_assoc in H2.
    specialize IHp with (1:=H8)(2:=H17)(3:=H2); cleanup; eauto.
    Unshelve.
    eauto.
 Qed.
    
Lemma exec_deterministic_wrt_oracle:
  forall O (L: Language O) T (p: prog L T) u o s r1 r2,
      exec L u o s p r1 ->
      exec L u o s p r2 ->
      r1 = r2.
Proof.
  intros.
  eapply exec_deterministic_wrt_oracle_prefix; eauto.
  Unshelve.
  eauto.
Qed.

Lemma recovery_exec_deterministic_wrt_reboot_state :
  forall O (L: Language O) u lo s T (p: L.(prog) T) rec l_get_reboot_state ret1 ret2,
    recovery_exec L u lo s l_get_reboot_state p rec ret1 ->
    recovery_exec L u lo s l_get_reboot_state p rec ret2 ->
    ret1 = ret2.
Proof.
  induction 1; intros;  try repeat
                             match goal with
                             | [H: exec' _ _ _ (Bind _ _) _ |- _ ] =>
                               inversion H; clear H; simpl in *; cleanup
                             | [H: recovery_exec _ _ _ _ _ _ _ _ |- _ ] =>
                               inversion H; clear H; simpl in *; cleanup
                             end.
  try solve [eapply exec_deterministic_wrt_oracle in H; eauto; cleanup; eauto].
  eapply exec_deterministic_wrt_oracle in H; eauto; cleanup; eauto.
  erewrite IHrecovery_exec'; eauto.
  Unshelve.
  all: eauto.
Qed.

Definition minimal_oracle {O} {L: Language O} {T} (p: L.(prog) T) u s o om :=
forall s',
      exec L u o s p s' ->
      exists o',
      o = om ++ o' /\
      exec L u om s p s' /\
      (forall n r, 
      n < length om ->
      ~exec L u (firstn n om) s p r).


Lemma minimal_oracle_finished_same :
forall O (L: Language O) T (p: prog L T) o u s s' r,
exec L u o s p (Finished s' r) ->
minimal_oracle p u s o o.
Proof.
  induction p; simpl; intros.
  {
    unfold minimal_oracle; intros.
    eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    exists nil; simpl; intuition eauto.
    rewrite app_nil_r; eauto.
    inversion H0; cleanup.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
  }
  {
    unfold minimal_oracle; intros.
    eapply exec_deterministic_wrt_oracle in H; eauto; cleanup.
    exists nil; simpl; intuition eauto.
    rewrite app_nil_r; eauto.
    inversion H0; cleanup.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
  }
  { 
    unfold minimal_oracle in *; intros.
    eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    inversion H1; cleanup; eauto.
    eapply_fresh H in H10; eauto.
    eapply_fresh IHp in H7; eauto.
    logic_clean.
    exists nil; intuition eauto.
    rewrite app_nil_r; eauto.

    rewrite app_length in *.
    destruct (PeanoNat.Nat.eq_dec n (length o1)).

    rewrite firstn_app_l in H9; eauto.
    rewrite firstn_oob in H9; eauto.
    inversion H9; subst; sigT_eq.
    eapply exec_finished_deterministic_prefix in H7; eauto.
    logic_clean.
    
    assert (length o0 = length o0 + length o3). {
      rewrite H7 at 1.
      rewrite app_length; eauto.
    }
    assert (length o3 = 0). { lia. }
    apply length_zero_iff_nil in H14; subst;
    eapply exec_empty_oracle; eauto.
    eapply finished_not_crashed_oracle_prefix. 
    apply H7.
    2: eauto.
    eauto.
    all: try lia.
    
    apply PeanoNat.Nat.lt_gt_cases in n0.
    destruct n0.
    {
      rewrite firstn_app_l in H9; eauto.
      inversion H9; subst; sigT_eq.
      destruct o3.
      eapply exec_empty_oracle; eauto.
      assert (exists m, o0 = firstn m o1 /\ m < length o1). {
      rewrite <- firstn_skipn with (n:= length o0) in H12.
      eapply app_split_length_eq_l in H12. 
      logic_clean; subst.
      rewrite firstn_firstn in H12.
      eexists; eauto.
      split; eauto.
      eapply PeanoNat.Nat.min_lt_iff; eauto.
      rewrite firstn_skipn in H12.
      rewrite <- H12.
      rewrite firstn_app2; eauto.
    }
    logic_clean; subst.
    eapply H4; eauto.
    eapply finished_not_crashed_oracle_prefix. 
    apply H7.
    2: eauto.
    rewrite app_nil_r; eauto.
    erewrite firstn_skipn with (l:= o1); eauto.
    lia.
    }
    {
      rewrite firstn_app_le in H9.
    inversion H9; subst; sigT_eq.
    eapply exec_finished_deterministic_prefix in H7; eauto.
    logic_clean; subst; clear_lists; subst.
    eapply H6; eauto.
    lia.
    eapply finished_not_crashed_oracle_prefix in H7; eauto.
    rewrite <- app_assoc; eauto.
    lia.
    }
  }
  Unshelve.
  all: eauto.
Qed.


  Lemma minimal_oracle_exists :
forall O (L: Language O) T (p: prog L T) u o s r,
exec L u o s p r ->
exists om, minimal_oracle p u s o om.
Proof.
  induction p; simpl; intros.
  {
    unfold minimal_oracle; intros.
    eexists; intros.
    inversion H; cleanup.
    exists nil; intuition eauto.
    rewrite app_nil_r; eauto.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
    
    exists nil; intuition eauto.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
  }
  {
    unfold minimal_oracle; intros.
    eexists; intros.
    inversion H; cleanup.
    exists nil; intuition eauto.
    rewrite app_nil_r; eauto.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
    
    exists nil; intuition eauto.
    simpl in *.
    destruct n; try lia.
    simpl in *; eapply exec_empty_oracle; eauto.
  }
  {
    
    inversion H0; cleanup; eauto.
    edestruct IHp; eauto.
    eapply_fresh minimal_oracle_finished_same in H7; eauto; subst.
    edestruct H; eauto.
    eapply_fresh H2 in H10; cleanup.
    eapply_fresh Hx in H7; logic_clean.
    clear H3 H6.
    exists (o1++x0).
    unfold minimal_oracle; intros.
    eexists; intros.
    rewrite <- app_assoc; eauto.
    intuition eauto.
    econstructor; eauto.
    inversion H3; cleanup.
    {
      eapply exec_finished_deterministic_prefix in H7; eauto; cleanup.
      eapply H2 in H18; logic_clean; eauto.
    }
    {
      exfalso; 
      eapply finished_not_crashed_oracle_prefix; [eauto | | eauto].
      rewrite <- app_assoc; eauto.
    }
    {
      rewrite app_length in *.
    destruct (PeanoNat.Nat.eq_dec n (length o1)).

    rewrite firstn_app_l in H9; eauto.
    rewrite firstn_oob in H9; eauto.
    inversion H9; subst; sigT_eq.
    eapply exec_finished_deterministic_prefix in H7; eauto.
    logic_clean.
    
    assert (length o0 = length o0 + length o2). {
      rewrite H7 at 1.
      rewrite app_length; eauto.
    }
    assert (length o2 = 0). { lia. }
    apply length_zero_iff_nil in H14; subst;
    eapply exec_empty_oracle; eauto.
    rewrite <- app_assoc; eauto.

    eapply finished_not_crashed_oracle_prefix. 
    apply H7.
    2: eauto.
    eauto.
    all: try lia.
    
    apply PeanoNat.Nat.lt_gt_cases in n0.
    destruct n0.
    {
      rewrite firstn_app_l in H9; eauto.
      inversion H9; subst; sigT_eq.
      destruct o2.
      eapply exec_empty_oracle; eauto.
      assert (exists m, o0 = firstn m o1 /\ m < length o1). {
      rewrite <- firstn_skipn with (n:= length o0) in H12.
      eapply app_split_length_eq_l in H12. 
      logic_clean; subst.
      rewrite firstn_firstn in H12.
      eexists; eauto.
      split; eauto.
      eapply PeanoNat.Nat.min_lt_iff; eauto.
      rewrite firstn_skipn in H12.
      rewrite <- H12.
      rewrite firstn_app2; eauto.
    }
    logic_clean; subst.
    eapply H8; eauto.
    eapply finished_not_crashed_oracle_prefix. 
    apply H7.
    2: eauto.
    rewrite app_nil_r; eauto.
    erewrite firstn_skipn; eauto.
    repeat rewrite <- app_assoc; eauto.
    lia.
    }
    {
      rewrite firstn_app_le in H9.
    inversion H9; subst; sigT_eq.
    eapply exec_finished_deterministic_prefix in H7; eauto.
    logic_clean; subst; clear_lists; subst.
    eapply H5; eauto.
    lia.
    eapply finished_not_crashed_oracle_prefix in H7; eauto.
    repeat rewrite <- app_assoc; eauto.
    lia.
    }
  }
  {
    edestruct IHp; eauto.
    apply H1 in H6; eauto; cleanup.
    exists x; intuition eauto.
    unfold minimal_oracle; intros.
    eapply exec_deterministic_wrt_oracle in H0; eauto; cleanup.
    eexists; intuition eauto.
    eapply ExecBindCrash; eauto.
    inversion H5; cleanup.
    {
    eapply finished_not_crashed_oracle_prefix. 
    apply H12.
    2: eauto.
    setoid_rewrite app_nil_r at 2; eauto.
    instantiate (1:= o2 ++ skipn n x).
    erewrite <- firstn_skipn with (l:= x) at 2.
    rewrite <- H6.
    repeat rewrite <- app_assoc; eauto.
    }
    {
      eauto.
    }
    }
  }
  
  Unshelve.
  all:  eauto.
Qed.

Lemma minimal_oracle_unique :
forall O (L: Language O) T (p: prog L T) u o om1 om2 s r,
exec L u o s p r ->
minimal_oracle p u s o om1 ->
minimal_oracle p u s o om2 ->
om1 = om2.
Proof.
  intros.
  eapply_fresh H0 in H; cleanup.
  eapply_fresh H1 in H; cleanup.
  destruct (PeanoNat.Nat.eq_dec (length om1) (length om2)).
  eapply app_split_length_eq_l in H2; eauto; cleanup; eauto.

  apply PeanoNat.Nat.lt_gt_cases in n.
  destruct n.
  {
    assert (exists m, om1 = firstn m om2 /\ m < length om2). {
    rewrite <- firstn_skipn with (n:= length om1) in H2.
    eapply app_split_length_eq_l in H2. 
    logic_clean; subst.
    rewrite firstn_app_l in H2.
    eexists; eauto.
    lia.
    rewrite firstn_length_l; eauto.
    rewrite app_length; lia.
  }
  logic_clean; subst.
  exfalso; eapply H6; eauto.
  }
  {
    assert (exists m, om2 = firstn m om1 /\ m < length om1). {
    rewrite <- firstn_skipn with (n:= length om2) (l:= om1) in H2.
    rewrite <- app_assoc in H2.
    eapply app_split_length_eq_l in H2. 
    logic_clean; subst.
    eexists; eauto.
    rewrite firstn_length_l; eauto; lia.
  }
  logic_clean; subst.
  exfalso; eapply H4; eauto.
  }
Qed.

Lemma exec_crashed_minimal_oracle:
  forall O (L: Language O) T (p: prog L T) u o s s',
      exec L u o s p (Crashed s') ->
      exists o1 o2,
      o = o1 ++ o2 /\
      exec L u o1 s p (Crashed s') /\
      (forall n r, 
      n < length o1 ->
      ~ exec L u (firstn n o1) s p r).
Proof.
  intros; eapply_fresh minimal_oracle_exists in H; cleanup.
  eapply H0 in H; cleanup.
  do 2 eexists; intuition eauto.
Qed.