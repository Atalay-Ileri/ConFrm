Require Import Framework TotalMem.
Import ListNotations.

Set Implicit Arguments.

Section DiskLayer.

  Variable A: Type.
  Variable AEQ: EqDec A.
  Variable V : Type.
  Variable in_domain: A -> Prop.

  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' :=  @total_mem A AEQ (V * list V).
  
  Inductive disk_prog : Type -> Type :=
  | Read : A -> disk_prog V
  | Write : A -> V -> disk_prog unit
  | Sync : disk_prog unit.
   
  Inductive exec' :
    forall T, token' ->  state' -> disk_prog T -> @Result state' T -> Prop :=
  | ExecRead : 
      forall d a,
        in_domain a ->
        exec' Cont d (Read a) (Finished d (fst (d a)))
             
  | ExecWrite :
      forall d a v,
        in_domain a ->
        exec' Cont d (Write a v) (Finished (upd d a (v, (fst (d a)::snd (d a)))) tt)

  | ExecSync :
      forall d,
        exec' Cont d Sync (Finished (sync d) tt)
 
  | ExecCrash :
      forall T d (p: disk_prog T),
        exec' Crash d p (Crashed d).

  Hint Constructors exec' : core.

  Theorem exec_deterministic_wrt_token' :
    forall o s T (p: disk_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto.
    
  Qed. 
  
  Definition DiskOperation :=
    Build_Core
      disk_prog
      exec'
      exec_deterministic_wrt_token'.
  
  Definition DiskLang := Build_Language DiskOperation.

Notation "| p |" := (Op DiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op DiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).

End DiskLayer.

Arguments Read {_ _}.
Arguments Sync {_ _}.
