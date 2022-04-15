Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Section ListLayer.
  
  Variable V : Type.
  
  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' := list V.
  
  Inductive list_prog : Type -> Type :=
  | Get : list_prog (list V)
  | Put : V -> list_prog unit
  | Delete : list_prog unit.

  
  Inductive exec' :
    forall T, user -> token' ->  state' -> list_prog T -> @Result state' T -> Prop :=
  | ExecGet : 
      forall d u,
        exec' u Cont d Get (Finished d d)
             
  | ExecPut :
      forall d v u,
        exec' u Cont d (Put v) (Finished (v::d) tt)

  | ExecDelete :
      forall d u,
        exec' u Cont d Delete (Finished [] tt)
              
  | ExecCrash :
      forall T d (p: list_prog T) u,
        exec' u Crash d p (Crashed d).

  Hint Constructors exec' : core.
  
  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: list_prog T) ret1 ret2,
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
  
  Definition ListOperation :=
    Build_Core
      list_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition ListLang := Build_Layer ListOperation.
  
End ListLayer.
