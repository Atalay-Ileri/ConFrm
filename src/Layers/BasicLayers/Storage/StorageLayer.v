Require Import Framework.
Import ListNotations.

Set Implicit Arguments.

Section StorageLayer.

  Variable V : Type.
  
  Inductive token' :=
  | Crash : token'
  | Cont : token'.

  Definition state' := option V.

  Definition after_crash' (s1 s2: state') := s2 = None.
  
  Inductive storage_prog : Type -> Type :=
  | Get : storage_prog V
  | Put : V -> storage_prog unit
  | Delete : storage_prog unit.

  
  Inductive exec' :
    forall T, token' ->  state' -> storage_prog T -> @Result state' T -> Prop :=
  | ExecGet : 
      forall d v,
        d = Some v ->
        exec' Cont d Get (Finished d v)
             
  | ExecPut :
      forall d v,
        exec' Cont d (Put v) (Finished (Some v) tt)

  | ExecDelete :
      forall d,
        exec' Cont d Delete (Finished None tt)
              
  | ExecCrash :
      forall T d (p: storage_prog T),
        exec' Crash d p (Crashed d).

  Hint Constructors exec' : core.
  
  Definition weakest_precondition' T (p: storage_prog T) :=
   match p in storage_prog T' return (T' -> state' -> Prop) -> token' -> state' -> Prop with
   | Get =>
     fun Q o s =>
       exists v, 
        o = Cont /\
        s = Some v /\
        Q v s
   | Put v =>
     fun Q o s =>
        o = Cont /\
        Q tt (Some v)
   | Delete =>
     fun Q o s =>
        o = Cont /\
        Q tt None
   end.

  Definition weakest_crash_precondition' T (p: storage_prog T) :=
    fun (Q: state' -> Prop) o (s: state') => o = Crash /\ Q s.

  Definition strongest_postcondition' T (p: storage_prog T) :=
   match p in storage_prog T' return (token' -> state' -> Prop) -> T' -> state' -> Prop with
   | Get =>
     fun P t s' =>
       exists s v,
        P Cont s /\
        s = Some v /\
        t = v /\
        s' = s
   | Put v =>
     fun P t s' =>
       exists s,
         P Cont s /\
         t = tt /\
         s' = Some v
   | Delete  =>
     fun P t s' =>
       exists s,
         P Cont s /\
         t = tt /\
         s' = None
   end.

  Definition strongest_crash_postcondition' T (p: storage_prog T) :=
    fun (P: token' -> state' -> Prop) (s: state') => P Crash s.

  Theorem sp_complete':
    forall T (p: storage_prog T) P (Q: _ -> _ -> Prop),
      (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
      (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto;
    do 2 eexists; eauto.    
  Qed.

  Theorem scp_complete':
    forall T (p: storage_prog T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros;
    try inversion H1; cleanup;
    eapply H; eauto.
  Qed.
  
  Theorem wp_complete':
    forall T (p: storage_prog T) H Q,
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
    forall T (p: storage_prog T) H C,
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

  Theorem exec_deterministic_wrt_token' :
    forall o s T (p: storage_prog T) ret1 ret2,
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
  
  Definition StorageOperation :=
    Build_Core
      storage_prog
      exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete'
      wcp_complete'
      sp_complete'
      scp_complete'
      exec_deterministic_wrt_token'.

  Definition StorageLang := Build_Language StorageOperation.

  Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
  
End StorageLayer.
