Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Section StorageLayer.

  Variable V : Type.
  
  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' := option V.
  
  Inductive storage_prog : Type -> Type :=
  | Get : storage_prog V
  | Put : V -> storage_prog unit
  | Delete : storage_prog unit.

  
  Inductive exec' :
    forall T, user -> token' ->  state' -> storage_prog T -> @Result state' T -> Prop :=
  | ExecGet : 
      forall d v u,
        d = Some v ->
        exec' u Cont d Get (Finished d v)
             
  | ExecPut :
      forall d v u,
        exec' u Cont d (Put v) (Finished (Some v) tt)

  | ExecDelete :
      forall d u,
        exec' u Cont d Delete (Finished None tt)
              
  | ExecCrash :
      forall T d (p: storage_prog T) u,
        exec' u Crash d p (Crashed d).

  Hint Constructors exec' : core.
  
  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: storage_prog T) ret1 ret2,
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
  
  Definition StorageOperation :=
    Build_Core
      storage_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition StorageLang := Build_Layer StorageOperation.
  
End StorageLayer.
