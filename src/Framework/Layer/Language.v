Require Import Primitives Layer.Core.
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
    forall T, oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecOp : 
      forall T (p : O.(operation) T) o s s' r,
        O.(exec) o s p (Finished s' r) ->
        exec' [OpToken o] s (Op T p) (Finished s' r)
             
  | ExecRet :
      forall d T (v: T),
        exec' [Cont] d (Ret v) (Finished d v)

  | ExecBind :
      forall T T' (p1: prog' T) (p2: T -> prog' T')
        o1 d1 d1' o2 r ret,
        exec' o1 d1 p1 (Finished d1' r) ->
        exec' o2 d1' (p2 r) ret ->
        exec' (o1++o2) d1 (Bind p1 p2) ret

  | ExecOpCrash : 
      forall T (p : O.(operation) T) o s s',
        O.(exec) o s p (Crashed s') ->
        exec' [OpToken o] s (Op T p) (Crashed s')
             
  | ExecRetCrash :
      forall T d (v: T),
        exec' [Crash] d (Ret v) (Crashed d)
             
  | ExecBindCrash :
      forall T T' (p1: prog' T) (p2: T -> prog' T')
        o1 o2 d1 d1',
        exec' o1 d1 p1 (Crashed d1') ->
        exec' (o1++o2) d1 (Bind p1 p2) (Crashed d1').

  Inductive recovery_exec' :
    forall T, list oracle' -> state' -> list (state' -> state') -> prog' T -> prog' unit -> @Recovery_Result state' T -> Prop :=
  | ExecFinished :
      forall T (p: prog' T) p_rec
        o d d' t,
        exec' o d p (Finished d' t) ->
        recovery_exec' [o] d [] p p_rec (RFinished d' t)
  | ExecRecovered :
      forall T (p: prog' T) p_rec
        o lo d d' get_reboot_state l_grs ret,
        exec' o d p (Crashed d') ->
        recovery_exec' lo (get_reboot_state d') l_grs p_rec p_rec ret ->
        recovery_exec' (o::lo) d (get_reboot_state::l_grs) p p_rec (Recovered (extract_state_r ret)).
  
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
Hint Extern 1 (Language.exec _ _ _ (Op _ _) (Finished _ _)) => eapply (ExecOp _) : core.
Notation "| p |" := (Op _ p)(at level 60).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op _ p1) (fun x => p2))(right associativity, at level 60).




 (** Facts **)

Lemma exec_finished_deterministic_prefix:
  forall O (L: Language O) T (p: prog L T) o1 o2 o3 o4 s s1 s2 r1 r2,
      exec L o1 s p (Finished s1 r1) ->
      exec L o2 s p (Finished s2 r2) -> 
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    (try inversion H; try inversion H0; try inversion H1; simpl in *; cleanup);
    simpl in *; cleanup;
    simpl; eauto; try solve [intuition].
  
  eapply O.(exec_deterministic_wrt_token) in H7; eauto; cleanup; eauto.
  
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H8)(2:= H17)(3:=H2); cleanup.
  specialize H with (1:= H11)(2:= H20)(3:=H2); cleanup; eauto.
Qed.

Lemma finished_not_crashed_oracle_prefix:
  forall O (L: Language O) T (p: prog L T) o1 o2 o3 o4 s s1 s2 r1,
    exec L o1 s p (Finished s1 r1) ->
    o1 ++ o3 = o2 ++ o4 ->
    ~exec L o2 s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
  (try inversion H; try inversion H0; try inversion H1;
    try inversion H2; simpl in *; cleanup);
  simpl in *; cleanup; simpl; eauto.
  eapply exec_deterministic_wrt_token in H7; eauto; cleanup.
  -
    repeat rewrite <- app_assoc in H1; eauto.
    eapply exec_finished_deterministic_prefix in H8; eauto; cleanup; eauto.
  -
    repeat rewrite <- app_assoc in H1; eauto.
    Unshelve.
    eauto.
Qed.

Lemma finished_not_crashed_oracle_app:
  forall O (L: Language O) T (p: prog L T) o1 o2 s s1 s2 r1,
    exec L o1 s p (Finished s1 r1) ->
    ~exec L (o1++o2) s p (Crashed s2).
Proof.
  unfold not; induction p; simpl; intros;
  (try inversion H; try inversion H0; try inversion H1;
    try inversion H2; simpl in *; cleanup);
  simpl in *; cleanup; simpl; eauto.
  eapply exec_deterministic_wrt_token in H6; eauto; cleanup.

  - rewrite <- app_assoc in H11; eauto.
    eapply exec_finished_deterministic_prefix in H7; eauto; cleanup; eauto.
    
  - rewrite <- app_assoc in H11; eauto.
    clear H1; eapply finished_not_crashed_oracle_prefix in H7; eauto.
    Unshelve.
    all: eauto.  
Qed.

Lemma exec_deterministic_wrt_oracle_prefix:
      forall O (L: Language O) T (p: prog L T) o1 o2 x1 x2 s ret1 ret2,
      exec L o1 s p ret1 -> 
      exec L x1 s p ret2 ->
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
    eapply O.(exec_deterministic_wrt_token) in H7; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_token) in H7; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_token); eauto; cleanup.
  -
    eapply exec_finished_deterministic_prefix in H8; eauto; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; eauto.
  -
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H8)(2:=H16)(3:=H2); cleanup.

  - repeat rewrite <- app_assoc in H2.
    specialize IHp with (1:=H7)(2:=H16)(3:=H2); cleanup.
  -
    repeat rewrite <- app_assoc in H2.
    specialize IHp with (1:=H7)(2:=H15)(3:=H2); cleanup; eauto.
    Unshelve.
    eauto.
 Qed.
    
Lemma exec_deterministic_wrt_oracle:
  forall O (L: Language O) T (p: prog L T) o s r1 r2,
      exec L o s p r1 ->
      exec L o s p r2 ->
      r1 = r2.
Proof.
  intros.
  eapply exec_deterministic_wrt_oracle_prefix; eauto.
  Unshelve.
  eauto.
Qed.

Lemma recovery_exec_deterministic_wrt_reboot_state :
  forall O (L: Language O) lo s T (p: L.(prog) T) rec l_get_reboot_state ret1 ret2,
    recovery_exec L lo s l_get_reboot_state p rec ret1 ->
    recovery_exec L lo s l_get_reboot_state p rec ret2 ->
    ret1 = ret2.
Proof.
  induction 1; intros;  try repeat
                             match goal with
                             | [H: exec' _ _ (Bind _ _) _ |- _ ] =>
                               inversion H; clear H; simpl in *; cleanup
                             | [H: recovery_exec _ _ _ _ _ _ _ |- _ ] =>
                               inversion H; clear H; simpl in *; cleanup
                             end.
  try solve [eapply exec_deterministic_wrt_oracle in H; eauto; cleanup; eauto].
  eapply exec_deterministic_wrt_oracle in H; eauto; cleanup; eauto.
  erewrite IHrecovery_exec'; eauto.
  Unshelve.
  all: eauto.
Qed.
