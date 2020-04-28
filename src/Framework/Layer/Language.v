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

(*
  Fixpoint strongest_crash_postcondition' T (p: prog' T) :=    
      match p with
    | Bind p1 p2 =>
      fun P s =>
      forall o t1 s1 (P1: _ -> _ -> Prop),   
      (strongest_crash_postcondition' p1 P t1 s1 -> P1 o s1) ->
      strongest_crash_postcondition' (p2 t1) P1 t s
    | Op T' p' =>
      fun P t s =>
      O.(strongest_postcondition) p' (fun o s' => P [OpOracle o] s') t s
    | Ret v =>
      fun P t s =>
        P [Cont] s /\ t = v
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
*)
  Hint Constructors exec' : core.

  (* Automation *)
(*

  Definition prog_equiv T : prog' T -> prog' T -> Prop :=
    fun p1 p2 => forall o d out,
        exec' o d p1 out <-> exec' o d p2 out.

  Arguments prog_equiv {T} _ _.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_assoc : forall T T' T'' (p1: prog' T) (p2: T -> prog' T') (p3: T' -> prog' T''),
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
*)
    
(*  
Lemma exec_crashed_oracle_app:
  forall T (p: prog T) o1 o2 s s1,
    exec o1 s p (Crashed s1) ->
    exec (o1++o2) s p (Crashed s1).
Proof.
  induction p; simpl; intros;
  repeat (invert_exec; simpl in *; cleanup); simpl; eauto.
  
  split_ors; cleanup.
  -
    rewrite <- app_assoc; eapply ExecBindCrash; eauto.

  -
    rewrite <- app_assoc; econstructor; eauto.
    eapply H in H1; eauto.
Qed.
 *)
    
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
 *)


(*
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
*)
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
Record Language :=
  {
    token := token';
    token_dec := token_dec';
    oracle := oracle';
    oracle_dec := oracle_dec';
    state := state';
    prog := prog';
    exec := exec';
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

  Local Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

  Local Ltac invert_exec' :=
  match goal with
  | [ H: exec _ _ _ ?p _ |- _ ] =>
    match p with
    | Bind _ _ => idtac
    | Op _ _ => invert_exec'' H
    | Ret _ => invert_exec'' H
    end
  end.

Lemma bind_sep:
  forall O (L: Language O) T T' o d (p1: prog L T) (p2: T -> prog L T') ret,
    exec L o d (Bind p1 p2) ret ->
    match ret with
    | Finished d' r =>
    (exists o1 o2 d1 r1,
       exec L o1 d p1 (Finished d1 r1) /\
       exec L o2 d1 (p2 r1) ret /\
       o = o1++o2)
  | Crashed d' =>
    (exists o1 o2,
    o = o1++o2 /\    
    (exec L o1 d p1 (Crashed d') \/
     (exists d1 r1,
        exec L o1 d p1 (Finished d1 r1) /\
        exec L o2 d1 (p2 r1) ret)))
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
  |[H : exec _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec _ _ _ _ _ |- _ ] =>
   invert_exec'
  end.

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
      invert_exec.
      eapply exec_to_wp in H1; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup; eauto.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      invert_exec; eauto.
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
      invert_exec; eauto.
      do 2 eexists; intuition eauto.
      eapply IHp.
      intros.
      do 2 eexists; intuition eauto.
      instantiate (1:= fun o s => exec L o s p (Finished x3 x4)) in X0; simpl in *; eauto.
            
      eapply H; intros; eauto.  
      do 2 eexists; intuition eauto.
      instantiate (1:= fun o s => exec L o s (p0 x4) (Finished x x0)) in X1; simpl in *; eauto.
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
      invert_exec.
      eapply exec_to_wcp in H1; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - specialize H0 with (1:=X); cleanup; eauto.
      do 2 eexists; intuition eauto.
      econstructor; eauto.
      
    - specialize H0 with (1:=X); cleanup.
      invert_exec; eauto.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - specialize H1 with (1:=X); cleanup; eauto.
      split_ors.
      + edestruct IHp.
        edestruct H2; eauto; simpl in *; cleanup.
        eexists. intuition eauto. eapply ExecBindCrash; eauto.
      + edestruct H.
        eapply H3 in H2; eauto; simpl in *; cleanup.      
        eexists; intuition eauto.
        econstructor; eauto.

    - specialize H1 with (1:=X); cleanup.
      invert_exec; eauto.
      split_ors.
      + do 2 eexists; intuition eauto.
        left; eapply IHp.
        intros.
        eexists; intuition eauto.
        instantiate (1:= fun o s => exec L o s p (Crashed x)) in X0; simpl in *; eauto.
        simpl; eauto.
            
      + do 2 eexists; intuition eauto.
        right; do 2 eexists; split; eauto.
        eapply H.
        intros.
        eexists; intuition eauto.
        instantiate (1:= fun o s => exec L o s (p0 x3) (Crashed x)) in X0; simpl in *; eauto.
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
    - invert_exec.      
      eapply H.
      eapply exec_to_sp; eauto.
    - eapply sp_to_exec in H0; cleanup; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - invert_exec; eauto.
    - cleanup.
      eapply H; eauto.
      constructor.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - invert_exec.
      eapply H0; intros.
      exists x2.
      edestruct H.
      eapply H4; simpl in *; eauto.
      simpl; intuition.
      edestruct IHp.
      eapply H6; simpl in *; eauto.
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
    - invert_exec.      
      eapply H.
      eapply exec_to_scp; eauto.
    - eapply scp_to_exec in H0; cleanup; eauto.
      eapply H; eauto.
      constructor; eauto.
  }
  {(* Ret *)
    simpl; split; intros.
    - invert_exec; eauto.
    - cleanup.
      eapply H; eauto.
      constructor.
  }
  {(*Bind*)
    simpl in *; split; intros.
    - invert_exec.
      split_ors; cleanup;
      eapply H0; intros.
      + left.
        edestruct IHp.
        eapply H3; simpl in *; eauto.
        simpl; eauto.
      + right.        
        exists x2.
        edestruct H.
        eapply H4; simpl in *; eauto.
        simpl; intuition.
        edestruct sp_complete.
        eapply H6; simpl in *; eauto.
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


  (* Facts *)

Lemma exec_finished_deterministic_prefix:
  forall O (L: Language O) T (p: prog L T) o1 o2 o3 o4 s s1 s2 r1 r2,
      exec L o1 s p (Finished s1 r1) ->
      exec L o2 s p (Finished s2 r2) ->
      o1 ++ o3 = o2 ++ o4 ->
      o1 = o2 /\ s1 = s2 /\ r1 = r2.
Proof.
  induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  eapply O.(exec_deterministic_wrt_oracle) in H7; eauto; cleanup; eauto.
  
  repeat rewrite <- app_assoc in H2.
  specialize IHp with (1:= H0)(2:= H1)(3:=H2); cleanup.
  specialize H with (1:= H4)(2:= H3)(3:=H2); cleanup; eauto.
Qed.

Lemma finished_not_crashed_oracle_prefix:
  forall O (L: Language O) T (p: prog L T) o1 o2 o3 o4 s s1 s2 r1,
    exec L o1 s p (Finished s1 r1) ->
    o1 ++ o3 = o2 ++ o4 ->
    ~exec L o2 s p (Crashed s2).
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
Qed.

Lemma finished_not_crashed_oracle_app:
  forall O (L: Language O) T (p: prog L T) o1 o2 s s1 s2 r1,
    exec L o1 s p (Finished s1 r1) ->
    ~exec L (o1++o2) s p (Crashed s2).
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
Qed.

Lemma exec_deterministic_wrt_oracle_prefix:
      forall O (L: Language O) T (p: prog L T) o1 o2 x1 x2 s ret1 ret2,
      exec L o1 s p ret1 -> 
      exec L x1 s p ret2 ->
      o1 ++ o2 = x1 ++ x2 ->
      ret1 = ret2.
    Proof.
       induction p; simpl; intros;
    repeat (invert_exec; simpl in *; cleanup);
    simpl; eauto; try solve [intuition].
  -
    eapply O.(exec_deterministic_wrt_oracle); eauto.
  -
    eapply O.(exec_deterministic_wrt_oracle) in H6; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_oracle) in H6; eauto; cleanup.
  -
    eapply O.(exec_deterministic_wrt_oracle); eauto; cleanup.
  -
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; cleanup; eauto.
    repeat rewrite <- app_assoc in H2; eauto.
  -
    split_ors; cleanup.
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
    
  -
    split_ors; cleanup.
    repeat rewrite <- app_assoc in H2; eauto.
    specialize IHp with (1:=H0)(2:=H3)(3:=H2); cleanup.

    repeat rewrite <- app_assoc in H2.
    eapply exec_finished_deterministic_prefix in H0; eauto; cleanup; eauto.
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
