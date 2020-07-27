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

  Definition state' := disk value.
  
  Inductive logged_disk_prog : Type -> Type :=
  | Read : addr -> logged_disk_prog value
  | Write : list addr -> list value -> logged_disk_prog unit.
   
  Inductive exec' :
    forall T, oracle' ->  state' -> logged_disk_prog T -> @Result state' T -> Prop :=
  | ExecRead : 
      forall d a v,
        d a = Some v ->
        exec' [Cont] d (Read a) (Finished d v)
             
  | ExecWriteSuccess :
      forall d la lv,
        NoDup la ->
        length la = length lv ->
        (forall a, In a la -> d a <> None) ->
        exec' [Cont] d (Write la lv) (Finished (upd_batch d la lv) tt)

  | ExecWriteFail :
      forall d la lv,
        ~NoDup la \/ length la <> length lv \/
        (exists a, In a la /\ d a = None) ->
        exec' [Cont] d (Write la lv) (Finished d tt)

  | ExecCrashBefore :
      forall d T (p: logged_disk_prog T),
        exec' [CrashBefore] d p (Crashed d)

  | ExecCrashWriteAfter :
      forall d la lv,
        NoDup la ->
        length la = length lv ->
        (forall a, In a la -> d a <> None) ->
        exec' [CrashAfter] d (Write la lv) (Crashed (upd_batch d la lv)).

  Hint Constructors exec' : core.

   Definition weakest_precondition' T (p: logged_disk_prog T) :=
   match p in logged_disk_prog T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
       exists v,
         o = [Cont] /\
         s a = Some v /\
         Q v s)
   | Write la lv =>
     (fun Q o s =>
        (o = [Cont] /\
         NoDup la /\
         length la = length lv /\
         (forall a, In a la -> s a <> None) /\
         Q tt (upd_batch s la lv)) \/
        (o = [Cont] /\
        (~ NoDup la \/
         length la <> length lv \/
        (exists a, In a la /\ s a = None)) /\
        Q tt s))
   end.

  Definition weakest_crash_precondition' T (p: logged_disk_prog T) :=
    match p in logged_disk_prog T' return (state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
         o = [CrashBefore] /\
         Q s)
   | Write la lv =>
     (fun Q o s =>
       (o = [CrashBefore] /\
        Q s) \/
       (o = [CrashAfter] /\
        NoDup la /\
        length la = length lv /\
        (forall a, In a la -> s a <> None) /\
        Q (upd_batch s la lv)))
    end.

  Definition strongest_postcondition' T (p: logged_disk_prog T) :=
   match p in logged_disk_prog T' return (oracle' -> state' -> Prop) -> T' -> state' -> Prop with
   | Read a =>
     fun P t s' =>
       exists s v,
         P [Cont] s /\
         s a = Some v /\
         t = v /\
         s' = s
   | Write la lv =>
     fun P t s' =>
       exists s,
       P [Cont] s /\
       t = tt /\
       ((
         NoDup la /\
         length la = length lv /\
         (forall a, In a la -> s a <> None) /\
         s' = upd_batch s la lv
       ) \/
       (
         (~NoDup la \/
          length la <> length lv \/
          (exists a, In a la /\ s a = None)) /\
         s' = s
       ))
   end.

  Definition strongest_crash_postcondition' T (p: logged_disk_prog T) :=
    match p in logged_disk_prog T' return (oracle' -> state' -> Prop) -> state' -> Prop with
   | Read a =>
     fun P s' =>
       P [CrashBefore] s'
   | Write la lv =>
     fun P s' =>
       (P [CrashBefore] s') \/
       (exists s,
          P [CrashAfter] s /\
          NoDup la /\
          length la = length lv /\
          (forall a, In a la -> s a <> None) /\
          s' = upd_batch s la lv)
    end.
  
  Theorem sp_complete':
    forall T (p: logged_disk_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto;
    try solve [eexists; eauto].
    eexists; intuition eauto.
    split_ors; cleanup;
    intuition eauto.
  Qed.

  Theorem scp_complete':
    forall T (p: logged_disk_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    try split_ors; cleanup; eapply H; eauto.
    right; eexists; intuition eauto.
  Qed.

  Theorem wp_complete':
    forall T (p: logged_disk_prog T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
    left; eauto.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: logged_disk_prog T) H C,
      (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
      (forall o s, H o s -> (exists s', exec' o s p (Crashed s') /\ C s')).
  Proof.
    unfold weakest_crash_precondition';
    intros; destruct p; simpl; eauto;
    split; intros;
    specialize H0 with (1:= X);
    cleanup; eauto;
    inversion H0; cleanup; eauto.
    right; eauto.
  Qed.

  Theorem exec_deterministic_wrt_oracle' :
    forall o s T (p: logged_disk_prog T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *; cleanup;
    repeat
      match goal with
      | [H: exec' _ _ _ _ |- _] =>
        inversion H; clear H; cleanup
      end; eauto;
    split_ors; intuition;
    cleanup; exfalso; eauto.
  Qed.
  
  Definition LoggedDiskOperation :=
    Build_Operation
      (list_eq_dec token_dec')
      logged_disk_prog
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
      exec_deterministic_wrt_oracle'.

  Definition LoggedDiskLang := Build_Language LoggedDiskOperation.
  Definition LoggedDiskHL := Build_HoareLogic LoggedDiskLang.

Notation "| p |" := (Op LoggedDiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op LoggedDiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
