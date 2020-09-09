Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition token_dec' : forall (t t': token'), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle' := list token'.  

  Definition state' := user.

  (** TODO: This may need to change
  Definition after_crash' (s1 s2: state') := s1 = s2.
   **)
  
  Inductive authentication_prog : Type -> Type :=
  | Auth : user -> authentication_prog (option unit).
  
  Inductive exec' :
    forall T, oracle' ->  state' -> authentication_prog T -> @Result state' T -> Prop :=
  | ExecAuthSuccess : 
      forall s u,
        u = s ->
        exec' [Cont] s (Auth u) (Finished s (Some tt))
             
  | ExecAuthFail : 
      forall s u,
        u <> s ->
        exec' [Cont] s (Auth u) (Finished s None)
              
  | ExecCrash :
      forall T d (p: authentication_prog T),
        exec' [Crash] d p (Crashed d).

  Hint Constructors exec' : core.
  
  Definition weakest_precondition' T (p: authentication_prog T) :=
   match p in authentication_prog T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   |  Auth u =>
     fun Q o s =>
        o = [Cont] /\
        ((s = u /\ Q (Some tt) s) \/
        (s <> u /\ Q None s))
   end.

  Definition weakest_crash_precondition' T (p: authentication_prog T) :=
    fun (Q: state' -> Prop) o (s: state') => o = [Crash] /\ Q s.

  Definition strongest_postcondition' T (p: authentication_prog T) :=
   match p in authentication_prog T' return (oracle' -> state' -> Prop) -> T' -> state' -> Prop with
   | Auth u =>
     fun P t s' =>
       exists s,
        P [Cont] s /\
        s' = s /\
        ((s = u /\ t = Some tt) \/
         (s <> u /\ t = None))
   end.

  Definition strongest_crash_postcondition' T (p: authentication_prog T) :=
    fun (P: oracle' -> state' -> Prop) (s: state') => P [Crash] s.

  Theorem sp_complete':
    forall T (p: authentication_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros.
    try inversion H1; cleanup;
    eapply H; eauto;
    do 2 eexists; eauto.
    cleanup; split_ors; cleanup; eauto.
  Qed.

  Theorem scp_complete':
    forall T (p: authentication_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto.
  Qed.
  
  Theorem wp_complete':
    forall T (p: authentication_prog T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto.
    split_ors; cleanup; eauto.
    inversion H0; cleanup; eauto.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: authentication_prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
      (forall o s, H o s -> (exists s', exec' o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition';
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
  Qed.

  Theorem exec_deterministic_wrt_oracle' :
    forall o s T (p: authentication_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto; congruence.
  Qed.
  
  Definition AuthenticationOperation :=
    Build_Operation
      (list_eq_dec token_dec')
      (* after_crash' *)
      authentication_prog
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
      exec_deterministic_wrt_oracle'.

  Definition AuthenticationLang := Build_Language AuthenticationOperation.

  Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
