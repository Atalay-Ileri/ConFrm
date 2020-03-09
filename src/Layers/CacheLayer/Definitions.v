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
  | Write : addr -> value -> prog unit
  | Ret : forall T, T -> prog T
  | Bind : forall T T', prog T -> (T -> prog T') -> prog T'.
   
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

  Hint Constructors exec.
  
  Fixpoint oracle_ok T (p: prog T) o (s: state) :=
      o = [Cont] \/ o = [Crash].

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

  Theorem exec_then_oracle_ok:
    forall T (p: prog T) o s r,
      exec o s p r ->
      oracle_ok p o s.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.
  
Module CacheOperation <: Operation.
  Definition oracle := oracle.
  Definition oracle_dec:= list_eq_dec token_dec.
  Definition state := state.
  Definition prog := prog.
  Definition exec := exec.
  Definition oracle_ok := oracle_ok.
  Definition exec_deterministic_wrt_oracle :=
    exec_deterministic_wrt_oracle.
  Definition exec_then_oracle_ok :=
    exec_then_oracle_ok.
End CacheOperation.

Module CacheHL := HoareLogic CacheOperation.
Export CacheHL.

Definition cache_layer_lts := Build_LTS CacheHL.Lang.oracle CacheHL.Lang.state CacheHL.Lang.prog CacheHL.Lang.exec.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
