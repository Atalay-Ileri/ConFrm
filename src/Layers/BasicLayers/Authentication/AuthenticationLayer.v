Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' := unit.
  
  Inductive authentication_prog : Type -> Type :=
  | Auth : user -> authentication_prog (option unit).
  
  Inductive exec' :
    forall T, user -> token' ->  state' -> authentication_prog T -> @Result state' T -> Prop :=
  | ExecAuthSuccess : 
      forall s u curr,
        u = curr ->
        exec' curr Cont s (Auth u) (Finished s (Some tt))
             
  | ExecAuthFail : 
      forall s u curr,
        u <> curr ->
        exec' curr Cont s (Auth u) (Finished s None)
              
  | ExecCrash :
      forall T curr d (p: authentication_prog T),
        exec' curr Crash d p (Crashed d).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: authentication_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto; congruence.
  Qed.
  
  Definition AuthenticationOperation :=
    Build_Core
      authentication_prog
      exec'
      exec_deterministic_wrt_token'.

  Definition AuthenticationLang := Build_Language AuthenticationOperation.
