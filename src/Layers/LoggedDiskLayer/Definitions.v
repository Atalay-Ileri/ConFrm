Require Import Framework.
Import ListNotations.

Set Implicit Arguments.
  
  Inductive token' :=
  | CrashBefore : token'
  | CrashAfter : token'
  | Cont : token'.

  Definition token_dec' : forall (t t': token'), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle' := list token'.  

  Definition state' := disk (set value).
  
  Inductive prog' : Type -> Type :=
  | Read : addr -> prog' value
  | Write : list addr -> list value -> prog' unit.
   
  Inductive exec' :
    forall T, oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecRead : 
      forall d a v,
        read d a = Some v ->
        exec' [Cont] d (Read a) (Finished d v)
             
  | ExecWrite :
      forall d la lv,
        exec' [Cont] d (Write la lv) (Finished (write_all d la lv) tt)

  | ExecCrashRead :
      forall d a,
        exec' [CrashBefore] d (Read a) (Crashed d)
  
  | ExecCrashWriteBefore :
      forall d la lv,
        exec' [CrashBefore] d (Write la lv) (Crashed d)

  | ExecCrashWriteAfter :
      forall d la lv,
        exec' [CrashAfter] d (Write la lv) (Crashed (write_all d la lv)).

  Hint Constructors exec' : core.

   Definition weakest_precondition' T (p: prog' T) :=
   match p in prog' T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
       exists v,
         o = [Cont] /\
         read s a = Some v /\
         Q v s)
   | Write la lv =>
     (fun Q o s =>
       o = [Cont] /\
       Q tt (write_all s la lv))
   end.

  Definition weakest_crash_precondition' T (p: prog' T) :=
    match p in prog' T' return (state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
         o = [CrashBefore] /\
         Q s)
   | Write la lv =>
     (fun Q o s =>
       (o = [CrashBefore] /\
        Q s) \/
       (o = [CrashAfter] /\
        Q (write_all s la lv)))
   end.

  Theorem wp_complete':
    forall T (p: prog' T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;

    inversion H0; cleanup; eauto.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: prog' T) H C,
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
    forall o s T (p: prog' T) ret1 ret2,
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
  
  Definition LoggedDiskOperation :=
    Build_Operation
      (list_eq_dec token_dec')
      prog'
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      wp_complete'
      wcp_complete'
      exec_deterministic_wrt_oracle'.

  Definition LoggedDiskLang := Build_Language LoggedDiskOperation.
  Definition LoggedDiskHL := Build_HoareLogic LoggedDiskLang.

Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
