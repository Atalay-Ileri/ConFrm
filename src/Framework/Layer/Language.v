Require Import Primitives Layer.Operation.
Import ListNotations.

Set Implicit Arguments.

Section Language.
  
  Variable O: Operation.

  Inductive token' :=
  | OpOracle : O.(oracle) -> token'
  | Crash : token'
  | Cont : token'.

  Definition token_dec' : forall (t t': token'), {t=t'}+{t<>t'}.
    decide equality.
    apply O.(oracle_dec).
  Defined.

  Definition oracle' := list token'.
  Definition oracle_dec' : forall (o o': oracle'), {o=o'}+{o<>o'}.
    repeat decide equality.
    apply O.(oracle_dec).
  Defined.


  Definition state' := O.(state).
  
  Inductive prog' : Type -> Type :=
  | Op : forall T, O.(prog) T -> prog' T
  | Ret : forall T, T -> prog' T
  | Bind : forall T T', prog' T -> (T -> prog' T') -> prog' T'.
  
  Inductive exec' :
    forall T, oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecOp : 
      forall T (p : O.(prog) T) o s s' r,
        O.(exec) o s p (Finished s' r) ->
        exec' [OpOracle o] s (Op T p) (Finished s' r)
             
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
      forall T (p : O.(prog) T) o s s',
        O.(exec) o s p (Crashed s') ->
        exec' [OpOracle o] s (Op T p) (Crashed s')
             
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
        (* O.(after_reboot) d' (get_reboot_state d') -> *)
        recovery_exec' lo (get_reboot_state d') l_grs p_rec p_rec ret ->
        recovery_exec' (o::lo) d (get_reboot_state::l_grs) p p_rec (Recovered (extract_state_r ret)).
  
  Fixpoint weakest_precondition' T (p: prog' T) :=    
      match p with
    | Bind p1 p2 =>
      fun Q o s =>
        exists o1 o2,
      o = o1++o2 /\
      weakest_precondition' p1 (fun r s' => weakest_precondition' (p2 r) Q o2 s') o1 s
    | Op T' p' =>
      fun Q o s =>
        exists o',
      o = [OpOracle o'] /\
      O.(weakest_precondition) p' Q o' s
    | Ret v =>
      fun Q o s =>
        o = [Cont] /\ Q v s
      end.

  Fixpoint weakest_crash_precondition' T (p: prog' T) :=    
      match p with
    | Bind p1 p2 =>
      fun Q (o: oracle') s =>
        exists o1 o2,
          o = o1++o2 /\
          (weakest_crash_precondition' p1 Q o1 s \/
           (exists s' r,
              exec' o1 s p1 (Finished s' r) /\
              weakest_crash_precondition' (p2 r) Q o2 s'))
    | Op T' p' =>
      fun Q o s =>
        exists o',
      o = [OpOracle o'] /\
      O.(weakest_crash_precondition) p' Q o' s
    | Ret v =>
      fun Q o s =>
        o = [Crash] /\ Q s
      end.

  Fixpoint strongest_postcondition' T (p: prog' T) :=    
      match p with
    | Bind p1 p2 =>
      fun P t s' => 
      exists t1,
        strongest_postcondition' (p2 t1)
           (fun o2 sx => strongest_postcondition' p1 (fun o1 s => P(o1++o2) s) t1 sx) t s'
    | Op T' p' =>
      fun P t s => 
      O.(strongest_postcondition) p' (fun o s' => P [OpOracle o] s') t s
    | Ret v =>
      fun P t s =>
        P [Cont] s /\ t = v
      end.

  Fixpoint strongest_crash_postcondition' T (p: prog' T) :=    
      match p with
    | Bind p1 p2 =>
      fun P s' =>
        strongest_crash_postcondition' p1 (fun o1 s => exists o2, P (o1++o2) s) s' \/
        (exists t1,
           strongest_crash_postcondition' (p2 t1)
           (fun o2 sx => strongest_postcondition' p1 (fun o1 s => P(o1++o2) s) t1 sx) s')
    | Op T' p' =>
      fun P s => 
      O.(strongest_crash_postcondition) p' (fun o s' => P [OpOracle o] s') s
    | Ret v =>
      fun P s =>
        P [Crash] s
      end.

  Hint Constructors exec' : core.

  Record Language :=
    {
      token := token';
      token_dec := token_dec';
      oracle := oracle';
      oracle_dec := oracle_dec';
      state := state';
      (* after_reboot := O.(after_reboot); *)
      prog := prog';
      exec := exec';
      recovery_exec := recovery_exec';
      weakest_precondition := weakest_precondition';
      weakest_crash_precondition := weakest_crash_precondition';
      strongest_postcondition := strongest_postcondition';
      strongest_crash_postcondition := strongest_crash_postcondition';
    }.

End Language.

Arguments Ret {O T}.
Arguments Op O {T}.
Hint Extern 1 (Language.exec _ _ _ (Op _ _) (Finished _ _)) => eapply (ExecOp _) : core.
Notation "| p |" := (Op _ p)(at level 60).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))(right associativity, at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op _ p1) (fun x => p2))(right associativity, at level 60).

Lemma wp_complete :
  forall O (L: Language O) T (p: L.(prog) T) H Q,
        (forall o s, H o s -> L.(weakest_precondition) p Q o s) <->
        (forall o s, H o s ->
                (exists s' v, L.(exec) o s p (Finished s' v) /\ Q v s')).
Proof.
  induction p; intros.
  { (* Op *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup.
      eapply wp_to_exec in H1; eauto; cleanup; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      inversion H0; cleanup.
      eapply exec_to_wp in H1; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup; eauto.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      inversion H0; sigT_eq; cleanup; eauto.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - specialize H1 with (1:=X); cleanup; eauto.
      edestruct IHp.
      edestruct H1; eauto; simpl in *; cleanup.
      edestruct H.
      edestruct H6; eauto; simpl in *; cleanup.      
      do 2 eexists; intuition eauto.
      econstructor; eauto.

    - specialize H1 with (1:=X); cleanup.
      inversion H1; sigT_eq; cleanup; eauto.
      do 2 eexists; intuition eauto.
      eapply IHp.
      intros.
      do 2 eexists; intuition eauto.
      instantiate (1:= fun o s => exec L o s p (Finished d1' r)) in X0; simpl in *; eauto.
            
      eapply H; intros; eauto.  
      do 2 eexists; intuition eauto.
      instantiate (1:= fun o s => exec L o s (p0 r) (Finished x x0)) in X1; simpl in *; eauto.
      all: simpl in *; eauto.
  }
Qed.

Lemma wcp_complete :
  forall O (L: Language O) T (p: L.(prog) T) H Q,
        (forall o s, H o s -> L.(weakest_crash_precondition) p Q o s) <->
        (forall o s, H o s ->
                (exists s', L.(exec) o s p (Crashed s') /\ Q s')).
Proof.
  induction p; intros.
  { (* Op *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup.
      eapply wcp_to_exec in H1; eauto; cleanup; eauto.
      do 2 eexists; eauto.
      eapply ExecOpCrash; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      inversion H0; sigT_eq; cleanup.
      eapply exec_to_wcp in H1; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup; eauto.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      inversion H0; sigT_eq; cleanup; eauto.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - specialize H1 with (1:=X); cleanup; eauto.
      split_ors; cleanup.
      + edestruct IHp.
        edestruct H2; eauto; simpl in *; cleanup.
        eexists. intuition eauto. eapply ExecBindCrash; eauto.
      + edestruct H.
        eapply H3 in H2; eauto; simpl in *; cleanup.      
        eexists; intuition eauto.
        econstructor; eauto.

    - specialize H1 with (1:=X); cleanup.
      inversion H1; sigT_eq; cleanup; eauto.
            
      + do 2 eexists; intuition eauto.
        right; do 2 eexists; split; eauto.
        eapply H.
        intros.
        eexists; intuition eauto.
        instantiate (1:= fun o s => exec L o s (p0 r) (Crashed x)) in X0; simpl in *; eauto.
        simpl; eauto.

      + do 2 eexists; intuition eauto.
        left; eapply IHp.
        intros.
        eexists; intuition eauto.
        instantiate (1:= fun o s => exec L o s p (Crashed x)) in X0; simpl in *; eauto.
        simpl; eauto.
  }
Qed.



Lemma sp_complete :
  forall O (L: Language O) T (p: L.(prog) T) P (Q: T -> L.(state) -> Prop),
    (forall t s', L.(strongest_postcondition) p P t s' -> Q t s') <->
        (forall o s s' t, P o s -> L.(exec) o s p (Finished s' t) ->  Q t s').
Proof.
  induction p; intros.
  { (* Op *)
    simpl; split; intros.
    - inversion H1; sigT_eq; cleanup;    
      eapply H.
      eapply exec_to_sp; eauto.
    - eapply sp_to_exec in H0; cleanup; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - inversion H1; sigT_eq; cleanup; eauto.
    - cleanup.
      eapply H; eauto.
      constructor.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - inversion H2; sigT_eq; cleanup.
      eapply H0; intros.
      exists r.
      edestruct H.
      eapply H3; simpl in *; eauto.
      simpl; intuition.
      edestruct IHp.
      eapply H5; simpl in *; eauto.
      simpl; eauto.

    - cleanup.
      edestruct H.
      eapply H3 in H1; intros; eauto; cleanup.
      edestruct IHp.
      eapply H7 in H4.
      instantiate (1:= fun t1 s'1 => exists o0 s0, P (o0++o) s0 /\ exec L o0 s0 p (Finished s'1 t1)) in H4;
      simpl in *; cleanup.
      eapply H0; eauto.
      econstructor; eauto.
      simpl; intros; eauto.
  }
Qed.

Theorem scp_complete:
  forall O (L: Language O) T (p: L.(prog) T) P (C: L.(state) -> Prop),
    (forall s', L.(strongest_crash_postcondition) p P s' -> C s') <->
    (forall o s s', P o s -> L.(exec) o s p (Crashed s') ->  C s').
Proof.
  induction p; intros.
  { (* Op *)
    simpl; split; intros.
    - inversion H1; sigT_eq; cleanup;     
      eapply H.
      eapply exec_to_scp; eauto.
    - eapply scp_to_exec in H0; cleanup; eauto.
      eapply H; eauto.
      constructor; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - inversion H1; sigT_eq; cleanup; eauto.
    - cleanup.
      eapply H; eauto.
      constructor.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - inversion H2; sigT_eq; cleanup;
      eapply H0; intros.
      + right.        
        exists r.
        edestruct H.
        eapply H3; simpl in *; eauto.
        simpl; intuition.
        edestruct sp_complete.
        eapply H5; simpl in *; eauto.
        simpl; eauto.
        
      + left.
        edestruct IHp.
        eapply H3; simpl in *; eauto.
        simpl; eauto.

    - split_ors; cleanup.
      +
        edestruct IHp.
        eapply H3; eauto.
        simpl; intros; cleanup.        
        eapply H0; eauto.
        constructor; eauto.

      + edestruct H.
        eapply H3; eauto.
        simpl; intros; cleanup.
        edestruct sp_complete.
        eapply H7 in H4.
        instantiate (1:= fun t1 s'1 => exists o0 s0, P (o0++o) s0 /\ exec L o0 s0 p (Finished s'1 t1)) in H4;
        simpl in *; cleanup.
        eapply H0; eauto.
        econstructor; eauto.
      simpl; intros; eauto.
  }
  Unshelve.
  eauto.
Qed.

Lemma wp_to_exec:
  forall O (L: Language O) T (p: prog L T) Q o s,
    weakest_precondition L p Q o s -> (exists s' v, exec L o s p (Finished s' v) /\ Q v s').
Proof.
  intros. eapply wp_complete; eauto.
Qed.

Lemma exec_to_wp:
  forall O (L: Language O) T (p: prog L T) (Q: T -> state L -> Prop) o s s' v,
    exec L o s p (Finished s' v) ->
    Q v s' ->
    weakest_precondition L p Q o s.
Proof.
  intros.
  eapply wp_complete; intros.
  apply X.
  simpl; eauto.
Qed.

Lemma wcp_to_exec:
  forall O (L: Language O) T (p: L.(prog) T) Q o s,
    weakest_crash_precondition L p Q o s -> (exists s', exec L o s p (Crashed s') /\ Q s').
Proof.
  intros. eapply wcp_complete; eauto.
Qed.
  
Lemma exec_to_wcp:
  forall O (L: Language O) T (p: L.(prog) T) (Q: state L -> Prop) o s s',
    exec L o s p (Crashed s') ->
    Q s' ->
    weakest_crash_precondition L p Q o s.
Proof.
  intros.
  eapply wcp_complete; intros.
  apply X.
  simpl; eauto.
Qed.

Lemma sp_to_exec:
  forall O (L: Language O) T (p: prog L T) P t s',
    strongest_postcondition L p P t s' -> (exists o s, exec L o s p (Finished s' t) /\ P o s).
Proof.
  intros. edestruct sp_complete; eauto.
  instantiate (1:= fun t s' => exists o s, exec L o s p (Finished s' t) /\ P o s) in H1;
  simpl in *.
  eapply H1; intros; eauto.
Qed.

Lemma exec_to_sp:
  forall O (L: Language O) T (p: prog L T) (P: oracle L -> state L -> Prop) o s s' v,
    P o s ->
    exec L o s p (Finished s' v) ->
    strongest_postcondition L p P v s'.
Proof.
  intros. edestruct sp_complete; eauto.
  eapply H2; eauto.
Qed.

Lemma scp_to_exec:
  forall O (L: Language O) T (p: L.(prog) T) P s',
    strongest_crash_postcondition L p P s' -> (exists o s, exec L o s p (Crashed s') /\ P o s).
Proof.
  intros. edestruct scp_complete; eauto.
  instantiate (1:= fun s' => exists o s, exec L o s p (Crashed s') /\ P o s) in H1;
  simpl in *.
  eapply H1; intros; eauto.
Qed.
  
Lemma exec_to_scp:
  forall O (L: Language O) T (p: L.(prog) T) (P: oracle L -> state L -> Prop) o s s',
    P o s ->
    exec L o s p (Crashed s') ->
    strongest_crash_postcondition L p P s'.
Proof.
  intros. edestruct scp_complete; eauto.
  eapply H2; eauto.
Qed.

(**********)







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
  
  eapply O.(exec_deterministic_wrt_oracle) in H7; eauto; cleanup; eauto.
  
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
  eapply exec_deterministic_wrt_oracle in H7; eauto; cleanup.
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
  eapply exec_deterministic_wrt_oracle in H6; eauto; cleanup.

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
    eapply O.(exec_deterministic_wrt_oracle); eauto.
  -
    eapply O.(exec_deterministic_wrt_oracle) in H7; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_oracle) in H7; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_oracle); eauto; cleanup.
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


(** SP Theorems **)
(*
Lemma sp_impl:
    forall O (L: Language O) T (p: prog L T) (P P': list (Language.token' O) -> Operation.state O -> Prop) s' t,
      (forall o s, P' o s -> P o s) ->
      strongest_postcondition L p P' t s' ->
      strongest_postcondition L p P t s'.
  Proof.
    intros.
    eapply sp_to_exec in H0; cleanup.
    eapply exec_to_sp; eauto.
  Qed.

  Lemma sp_bind:
    forall O (L: Language O) T T' (p1: prog L T) (p2: T -> prog L T') P s' t,
      strongest_postcondition L (Bind p1 p2) P t s' ->
      exists s0 t0,
        strongest_postcondition L p1 (fun o s => exists o2, P (o++o2) s) t0 s0 /\
        strongest_postcondition L (p2 t0)
        (fun o s => strongest_postcondition L p1 (fun ox sx => P (ox++o) sx) t0 s) t s'.
  Proof.
    intros.
    eapply sp_to_exec in H; cleanup.
    invert_exec.
    do 2 eexists; split.
    eapply exec_to_sp; eauto.
    intros.            
    repeat (eapply exec_to_sp; eauto).
  Qed.


Lemma sp_exists_extract:
    forall X O (L: Language O) T (p: prog L T) (P: X -> list (Language.token' O) -> Operation.state O -> Prop) s' t,
      strongest_postcondition L p (fun o s => exists x, P x o s) t s' ->
      (exists x, strongest_postcondition L p (P x) t s').
  Proof.
    intros.
    eapply sp_to_exec in H; cleanup.
    eexists; eapply exec_to_sp; eauto.
  Qed.

Theorem sp_extract_precondition:
  forall O (L : Language O) T (p: prog L T) s t P,
    strongest_postcondition L p P t s ->
    strongest_postcondition L p P t s /\ (exists o s, P o s).
Proof.
  intros; eapply_fresh sp_to_exec in H; cleanup; eauto.
Qed.
*)
