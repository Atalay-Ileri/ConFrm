Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Section DiskLayer.

  Variable A: Type.
  Variable AEQ: EqDec A.
  Variable V : Type.

  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition token_dec' : forall (t t': token'), {t=t'}+{t<>t'}.
    decide equality.
  Defined.

  Definition oracle' := list token'.

  Definition state' :=  @mem A AEQ (V * list V).

  Definition after_crash' (s1 s2: state') :=
    addrs_match_exactly s1 s2 /\
    forall a vs,
      s1 a = Some vs ->
      exists v,
        s2 a = Some (v, []) /\
        In v (fst vs::snd vs).
  
  Inductive disk_prog : Type -> Type :=
  | Read : A -> disk_prog V
  | Write : A -> V -> disk_prog unit
  | Sync : disk_prog unit.
   
  Inductive exec' :
    forall T, oracle' ->  state' -> disk_prog T -> @Result state' T -> Prop :=
  | ExecRead : 
      forall d a vs,
        d a = Some vs ->
        exec' [Cont] d (Read a) (Finished d (fst vs))
             
  | ExecWrite :
      forall d a v vs,
        d a = Some vs ->
        exec' [Cont] d (Write a v) (Finished (upd d a (v, (fst vs::snd vs))) tt)

  | ExecSync :
      forall d,
        exec' [Cont] d Sync (Finished (sync d) tt)
 
  | ExecCrash :
      forall T d (p: disk_prog T),
        exec' [Crash] d p (Crashed d).

  Hint Constructors exec' : core.

  Definition weakest_precondition' T (p: disk_prog T) :=
   match p in disk_prog T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   | Read a =>
     (fun Q o s =>
       exists vs,
         o = [Cont] /\
         s a = Some vs /\
         Q (fst vs) s)
   | Write a v =>
     (fun Q o s =>
       exists vs,
       o = [Cont] /\
       s a = Some vs /\
       Q tt (upd s a (v, (fst vs::snd vs))))
   | Sync =>
     fun Q o s =>
       o = [Cont] /\
       Q tt (sync s)
   end.

  Definition weakest_crash_precondition' T (p: disk_prog T) :=
    fun (Q: state' -> Prop) o (s: state') => o = [Crash] /\ Q s.

  Definition strongest_postcondition' T (p: disk_prog T) :=
   match p in disk_prog T' return (oracle' -> state' -> Prop) -> T' -> state' -> Prop with
   | Read a =>
     fun P t s' =>
       exists s vs,
         P [Cont] s /\
         s' = s /\
         s a = Some vs /\
         t = fst vs
   | Write a v =>
     fun P t s' =>
       exists s vs,
         P [Cont] s /\
         s' = upd s a (v, (fst vs::snd vs)) /\
         s a = Some vs /\
         t = tt
   | Sync =>
     fun P t s' =>
        exists s, 
       P [Cont] s /\
       s' =(sync s) /\
       t = tt
   end.

  Definition strongest_crash_postcondition' T (p: disk_prog T) :=
    fun (P: oracle' -> state' -> Prop) s' => P [Crash] s'.


  Theorem sp_complete':
    forall T (p: disk_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto;
    eexists; eauto.
  Qed.

  Theorem scp_complete':
    forall T (p: disk_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto.
  Qed.


  Theorem wp_complete':
    forall T (p: disk_prog T) H Q,
      (forall o s, H o s -> weakest_precondition' p Q o s) <->
      (forall o s, H o s -> (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try specialize H0 with (1:= X);
    cleanup; eauto;
    try inversion H0; cleanup; eauto.
    do 2 eexists; intuition eauto.
    constructor; eauto.
  Qed.
  
  Theorem wcp_complete':
    forall T (p: disk_prog T) H C,
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
    Build_Operation
      (list_eq_dec token_dec')
      after_crash'
      disk_prog
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
  
  Definition DiskLang := Build_Language DiskOperation.

Notation "| p |" := (Op DiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op DiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).

End DiskLayer.

Arguments Read {_ _}.
Arguments Sync {_ _}.
