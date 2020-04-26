Require Import Framework.
Import ListNotations.

Set Implicit Arguments.
  
  Inductive token :=
  | Crash : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle := list token.  

  Definition state := disk value.
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog (option value)
  | Write : addr -> value -> prog unit.

  
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall d a,
        exec [Cont] d (Read a) (Finished d (d a))
             
  | ExecWrite :
      forall d a v,
        exec [Cont] d (Write a v) (Finished (upd d a v) tt)

  | ExecCrash :
      forall T d (p: prog T),
        exec [Crash] d p (Crashed d).

  Hint Constructors exec : core.
  
  Definition weakest_precondition T (p: prog T) :=
   match p in prog T' return (T' -> state -> Prop) -> oracle -> state -> Prop with
   | Read a =>
     (fun Q o s =>
        o = [Cont] /\
        Q (s a) s)
   | Write a v =>
     (fun Q o s =>
        o = [Cont] /\
        Q tt (upd s a v))
   end.

  Definition weakest_crash_precondition T (p: prog T) :=
   fun (Q: state -> Prop) o (s: state) => o = [Crash] /\ Q s.

  Theorem wp_complete:
    forall T (p: prog T) H Q,
      (forall o s, H o s -> weakest_precondition p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;

    inversion H0; cleanup; eauto.
  Qed.
  
  Theorem wcp_complete:
    forall T (p: prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition p C o s) <->
      (forall o s, H o s -> (exists s', exec o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition;
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;

    inversion H0; cleanup; eauto.
  Qed.

  Theorem exec_deterministic_wrt_oracle :
    forall o s T (p: prog T) ret1 ret2,
      exec o s p ret1 ->
      exec o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.
  
  Definition CacheOperation :=
    Build_Operation
      (list_eq_dec token_dec)
      prog
      exec
      weakest_precondition
      weakest_crash_precondition
      wp_complete
      wcp_complete
      exec_deterministic_wrt_oracle.

  Definition CacheLang := Build_Language CacheOperation.
  Definition CacheHL := Build_HoareLogic CacheLang.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
