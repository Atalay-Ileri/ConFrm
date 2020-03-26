Require Import Framework.
Import ListNotations.

Set Implicit Arguments.
  
  Inductive token :=
  | CrashBefore : token
  | CrashAfter : token
  | Cont : token.

  Definition token_dec : forall (t t': token), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle := list token.  

  Definition state := disk (set value).
  
  Inductive prog : Type -> Type :=
  | Read : addr -> prog value
  | Write : list addr -> list value -> prog unit.
   
  Inductive exec :
    forall T, oracle ->  state -> prog T -> @Result state T -> Prop :=
  | ExecRead : 
      forall d a v,
        read d a = Some v ->
        exec [Cont] d (Read a) (Finished d v)
             
  | ExecWrite :
      forall d la lv,
        exec [Cont] d (Write la lv) (Finished (write_all d la lv) tt)

  | ExecCrashRead :
      forall d a,
        exec [CrashBefore] d (Read a) (Crashed d)
  
  | ExecCrashWriteBefore :
      forall d la lv,
        exec [CrashBefore] d (Write la lv) (Crashed d)

  | ExecCrashWriteAfter :
      forall d la lv,
        exec [CrashAfter] d (Write la lv) (Crashed (write_all d la lv)).

  Hint Constructors exec.
  
  Fixpoint oracle_ok T (p: prog T) o (s: state) :=
    match p with
    |Read _ =>
     o = [Cont] \/ o = [CrashBefore]
    |Write _ _ =>
     o = [Cont] \/ o = [CrashBefore] \/ o = [CrashAfter]
    end.

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
  
Module LoggedDiskOperation <: Operation.
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
End LoggedDiskOperation.

Module LoggedDiskHL := HoareLogic LoggedDiskOperation.
Export LoggedDiskHL.

Definition logged_disk_lts := Build_LTS LoggedDiskHL.Lang.oracle LoggedDiskHL.Lang.state LoggedDiskHL.Lang.prog LoggedDiskHL.Lang.exec.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
