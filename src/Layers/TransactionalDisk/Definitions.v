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

  Definition state' := ((disk value) * (disk (set value)))%type.
  
  Inductive prog' : Type -> Type :=
  | Start : prog' unit
  | Read : addr -> prog' value
  | Write : addr -> value -> prog' unit
  | Commit : prog' unit
  | Abort : prog' unit.
   
  Inductive exec' :
    forall T, oracle' ->  state' -> prog' T -> @Result state' T -> Prop :=
  | ExecStart : 
      forall s,
        let c := fst s in
        let d := snd s in
        exec' [Cont] s Start (Finished (empty_mem, d) tt)
              
  | ExecRead : 
      forall s a v,
        let c := fst s in
        let d := snd s in
        (c a = Some v \/
        (c a = None /\ read d a = Some v)) ->
        exec' [Cont] s (Read a) (Finished s v)
             
  | ExecWrite :
      forall s a v,
        let c := fst s in
        let d := snd s in
        exec' [Cont] s (Write a v) (Finished ((upd c a v), d) tt)

  | ExecCommit : 
      forall s,
        let c := fst s in
        let d := snd s in
        exec' [Cont] s Commit (Finished (empty_mem, merge c d) tt)

  | ExecAbort : 
      forall s,
        let c := fst s in
        let d := snd s in
        exec' [Cont] s Abort (Finished (empty_mem, d) tt)

  | ExecCrashBefore :
      forall d T (p: prog' T),
        exec' [CrashBefore] d p (Crashed d)

  | ExecCrashAfter :
      forall s s' T (p: prog' T),
        (exists v, exec' [Cont] s p (Finished s' v)) ->
        exec' [CrashAfter] s p (Crashed s').

  Hint Constructors exec' : core.

   Definition weakest_precondition' T (p: prog' T) :=
   match p in prog' T' return (T' -> state' -> Prop) -> oracle' -> state' -> Prop with
   | Start =>
     (fun Q o s =>
       let c := fst s in
       let d := snd s in
       o = [Cont] /\
       Q tt (empty_mem, d))
   | Read a =>
     (fun Q o s =>
        let c := fst s in
        let d := snd s in
        exists v,
         o = [Cont] /\
         (c a = Some v \/
         (c a = None /\ read d a = Some v)) /\
         Q v s)
   | Write a v =>
     (fun Q o s =>
       let c := fst s in
       let d := snd s in
       o = [Cont] /\
       Q tt ((upd c a v), d))
   | Commit =>
     (fun Q o s =>
       let c := fst s in
       let d := snd s in
       o = [Cont] /\
       Q tt (empty_mem, merge c d))
   | Abort =>
     (fun Q o s =>
       let c := fst s in
       let d := snd s in
       o = [Cont] /\
       Q tt (empty_mem, d))
   end.

  Definition weakest_crash_precondition' T (p: prog' T) :=
    match p in prog' T' return (state' -> Prop) -> oracle' -> state' -> Prop with
    | Start =>
      (fun Q o s =>
         let c := fst s in
         let d := snd s in
         (o = [CrashBefore] /\
          Q s) \/
         (o = [CrashAfter] /\
          Q (empty_mem, d)))
   | Read a =>
     (fun Q o s =>
          let c := fst s in
          let d := snd s in
         (o = [CrashBefore] /\
          Q s) \/
         (o = [CrashAfter] /\
          (exists v,
           c a = Some v \/
           (c a = None /\ read d a = Some v)) /\
          Q s))
   | Write a v =>
     (fun Q o s =>
        let c := fst s in
        let d := snd s in
         (o = [CrashBefore] /\
          Q s) \/
         (o = [CrashAfter] /\
          Q (upd c a v, d)))
   | Commit =>
     (fun Q o s =>
       let c := fst s in
       let d := snd s in
       (o = [CrashBefore] /\
        Q s) \/
       (o = [CrashAfter] /\
        Q (empty_mem, merge c d)))
   | Abort =>
      (fun Q o s =>
         let c := fst s in
         let d := snd s in
         (o = [CrashBefore] /\
          Q s) \/
         (o = [CrashAfter] /\
          Q (empty_mem, d)))
    end.

  Definition strongest_postcondition' T (p: prog' T) :=
    match p in prog' T' return (oracle' -> state' -> Prop) -> T' -> state' -> Prop with
    | Start =>
      fun P t s' =>
        exists s,
         let c := fst s in
         let d := snd s in
         P [Cont] s /\
         t = tt /\
         s' = (empty_mem, d)
   | Read a =>
     fun P t s' =>
       exists s v,
         let c := fst s in
         let d := snd s in
         P [Cont] s /\
         (c a = Some v \/
         (c a = None /\ read d a = Some v)) /\
         t = v /\
         s' = s
   | Write a v =>
     fun P t s' =>
       exists s,
       let c := fst s in
       let d := snd s in
       P [Cont] s /\
       t = tt /\
       s' = ((upd c a v), d)
   | Commit =>
      fun P t s' =>
        exists s,
         let c := fst s in
         let d := snd s in
         P [Cont] s /\
         t = tt /\
         s' = (empty_mem, merge c d)
   | Abort =>
      fun P t s' =>
        exists s,
         let c := fst s in
         let d := snd s in
         P [Cont] s /\
         t = tt /\
         s' = (empty_mem, d)
   end.

  Definition strongest_crash_postcondition' T (p: prog' T) :=
    match p in prog' T' return (oracle' -> state' -> Prop) -> state' -> Prop with
    | Start =>
      fun P s' =>
        exists s,
          let c := fst s in
          let d := snd s in
          (P [CrashBefore] s /\
           s' = s) \/
          (P [CrashAfter] s /\
           s' = (empty_mem, d))
    | Read a =>
     fun P s' =>
       exists s,
         let c := fst s in
         let d := snd s in
         (P [CrashBefore] s /\
          s' = s) \/
         (P [CrashAfter] s /\
          (exists v, c a = Some v \/
          (c a = None /\ read d a = Some v)) /\
          s' = s)
   | Write a v =>
     fun P s' =>
       exists s,
         let c := fst s in
         let d := snd s in
         (P [CrashBefore] s /\
          s' = s) \/
         (P [CrashAfter] s /\
          s' = (upd c a v, d))
   | Commit =>
      fun P s' =>
       exists s,
         let c := fst s in
         let d := snd s in
         (P [CrashBefore] s /\
          s' = s) \/
         (P [CrashAfter] s /\
          s' = (empty_mem, merge c d))
   | Abort =>
      fun P s' =>
        exists s,
          let c := fst s in
          let d := snd s in
          (P [CrashBefore] s /\
           s' = s) \/
          (P [CrashAfter] s /\
           s' = (empty_mem, d))
    end.
  
  Theorem sp_complete':
    forall T (p: prog' T) P (Q: _ -> _ -> Prop),
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
    forall T (p: prog' T) P (Q:  _ -> Prop),
      (forall s', strongest_crash_postcondition' p P s' -> Q s') <->
      (forall o s s', P o s -> exec' o s p (Crashed s') -> Q s').
  Proof.
    intros; destruct p; simpl; eauto;
    split; intros; cleanup;
    repeat (try split_ors; try inversion H1; clear H1; cleanup; eauto);
    try split_ors; cleanup; eapply H; eauto.
    eexists; right; eauto.
    eexists; right; intuition eauto.
  Qed.

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
    split; intros; cleanup;
    specialize H0 with (1:= X);
    try split_ors; cleanup; repeat (try inversion H0; try clear H0; cleanup; eauto).
    split_ors; cleanup; eauto;
    eexists; split; eauto; econstructor; eauto. 
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
    repeat split_ors; cleanup; eauto.
  Qed.
  
  Definition TransactionalDiskOperation :=
    Build_Operation
      (list_eq_dec token_dec')
      prog'
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

  Definition TransactionalDiskLang := Build_Language TransactionalDiskOperation.
  Definition TransactionalDiskHL := Build_HoareLogic TransactionalDiskLang.

Notation "| p |" := (Op TransactionalDiskOperation p)(at level 60).
Notation "x <-| p1 ; p2" := (Bind (Op TransactionalDiskOperation p1) (fun x => p2))(right associativity, at level 60). 
Notation "p >> s" := (p s) (right associativity, at level 60, only parsing).
