Require Import Primitives Simulation Layer.
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
  
  Inductive op : Type -> Type :=
  | Read : addr -> op (option value)
  | Write : addr -> value -> op unit
  | Ret : forall T, T -> op T
  | Bind : forall T T', op T -> (T -> op T') -> op T'.
   
  Inductive exec :
    forall T, oracle ->  state -> op T -> @Result state T -> Prop :=
  | ExecRead : 
      forall d a,
        exec [Cont] d (Read a) (Finished d (d a))
             
  | ExecWrite :
      forall d a v,
        exec [Cont] d (Write a v) (Finished (upd d a v) tt)

  | ExecCrash :
      forall T d (p: op T),
        exec [Crash] d p (Crashed d).

  Fixpoint oracle_ok T (p: op T) o (s: state) :=
      o = [Cont] \/ o = [Crash].

  Theorem exec_deterministic_wrt_oracle :
    forall o s T (p: op T) ret1 ret2,
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
    forall T (p: op T) o s r,
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
  Definition op := op.
  Definition exec := exec.
  Definition oracle_ok := oracle_ok.
  Definition exec_deterministic_wrt_oracle :=
    exec_deterministic_wrt_oracle.
  Definition exec_then_oracle_ok :=
    exec_then_oracle_ok.
End CacheOperation.

Module CacheHL := HoareLogic CacheOperation.
Export CacheHL.

Definition cache_layer_lts := Build_LTS CacheHL.L.oracle state CacheHL.L.prog CacheHL.L.exec.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
Hint Constructors exec.