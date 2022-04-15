Require Import Framework.
Import ListNotations.
Import Mem.

Set Implicit Arguments.

Section CacheLayer.
  
  Variable A : Type.
  Variable AEQ : EqDec A. 
  Variable V : Type.

  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' := @mem A AEQ V.
  
  Inductive cache_prog : Type -> Type :=
  | Read : A -> cache_prog (option V)
  | Write : A -> V -> cache_prog unit
  | Flush : cache_prog unit.
  
  Inductive exec' :
    forall T, user -> token' ->  state' -> cache_prog T -> @Result state' T -> Prop :=
  | ExecRead : 
      forall d a u,
        exec' u Cont d (Read a) (Finished d (d a))
             
  | ExecWrite :
      forall d a v u,
        exec' u Cont d (Write a v) (Finished (upd d a v) tt)

  | ExecFlush :
      forall d u,
        exec' u Cont d Flush (Finished empty_mem tt)
              
  | ExecCrash :
      forall T d (p: cache_prog T) u,
        exec' u Crash d p (Crashed d).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: cache_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
  Qed.
  
  Definition CacheOperation :=
    Build_Core
      cache_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition CacheLang := Build_Layer CacheOperation.

End CacheLayer.
