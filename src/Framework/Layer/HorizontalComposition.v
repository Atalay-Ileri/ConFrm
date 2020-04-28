Require Import Primitives Layer.Operation.
Require Language.
Import ListNotations.

Set Implicit Arguments.

Section HorizontalComposition.
  Variable O1 O2 : Operation.
  
  Inductive token' :=
  | Oracle1 : O1.(oracle) -> token'
  | Oracle2 : O2.(oracle) -> token'.

  Definition oracle' := list token'.

  Definition token_dec: forall (t t': token'), {t = t'}+{t <> t'}.
   decide equality.
   apply O1.(oracle_dec).
   apply O2.(oracle_dec).
  Defined.

  Definition oracle_dec' := list_eq_dec token_dec.
  Definition state' := (O1.(state) * O2.(state))%type.

  Inductive prog' : Type -> Type :=
  | P1 : forall T, O1.(prog) T -> prog' T
  | P2 : forall T, O2.(prog) T -> prog' T.


  Inductive exec': forall T, oracle' -> state' -> prog' T -> @Result state' T -> Prop :=
  | ExecP1:
      forall T (p1: O1.(prog) T) o1 s s1 r,
        O1.(exec) o1 (fst s) p1 (Finished s1 r) ->
        exec' [Oracle1 o1] s (P1 _ p1) (Finished (s1, snd s) r)
  | ExecP2:
      forall T (p2: O2.(prog) T) o2 s s2 r,
        O2.(exec) o2 (snd s) p2 (Finished s2 r) ->
        exec' [Oracle2 o2] s (P2 _ p2) (Finished (fst s, s2) r)
  | ExecP1Crash:
      forall T (p1: O1.(prog) T) o1 s s1,
        O1.(exec) o1 (fst s) p1 (Crashed s1) ->
        exec' [Oracle1 o1] s (P1 _ p1) (Crashed (s1, snd s))
  | ExecP2Crash:
      forall T (p2: O2.(prog) T) o2 s s2,
        O2.(exec) o2 (snd s) p2 (Crashed s2) ->
        exec' [Oracle2 o2] s (P2 _ p2) (Crashed (fst s, s2)).
  
  Definition weakest_precondition' T (p: prog' T) :=
    match p with
    | P1 _ p1 =>
      fun Q o s =>
      exists o1,
      o = [Oracle1 o1] /\ O1.(weakest_precondition) p1 (fun r s' => Q r (s', snd s)) o1 (fst s)
    | P2 _ p2 =>
      fun Q o s =>
      exists o2,
      o = [Oracle2 o2] /\ O2.(weakest_precondition) p2 (fun r s' => Q r (fst s, s')) o2 (snd s)
    end.

  Definition weakest_crash_precondition' T (p: prog' T) :=
    match p with
    | P1 _ p1 =>
      fun Q o s =>
      exists o1,
      o = [Oracle1 o1] /\ O1.(weakest_crash_precondition) p1 (fun s' => Q (s', snd s)) o1 (fst s)
    | P2 _ p2 =>
      fun Q o s =>
      exists o2,
      o = [Oracle2 o2] /\ O2.(weakest_crash_precondition) p2 (fun s' => Q (fst s, s')) o2 (snd s)
    end.

  Definition strongest_postcondition' T (p: prog' T) :=
    match p with
    | P1 _ p1 =>
      fun P t s' =>
      O1.(strongest_postcondition) p1 (fun o s => P [Oracle1 o] (s, snd s')) t (fst s')
    | P2 _ p2 =>
      fun P t s' =>
        O2.(strongest_postcondition) p2 (fun o s => P [Oracle2 o] (fst s', s)) t (snd s')
    end.

  Definition strongest_crash_postcondition' T (p: prog' T) :=
    match p with
    | P1 _ p1 =>
      fun P s' =>
      O1.(strongest_crash_postcondition) p1 (fun o s => P [Oracle1 o] (s, snd s')) (fst s')
    | P2 _ p2 =>
      fun P s' =>
        O2.(strongest_crash_postcondition) p2 (fun o s => P [Oracle2 o] (fst s', s)) (snd s')
    end.

   Theorem wp_complete':
      forall T (p: prog' T) H Q,
        (forall o s, H o s -> weakest_precondition' p Q o s) <->
        (forall o s, H o s ->
                (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
   Proof.
     intros; destruct p; simpl;
     split; intros;
       try solve [
         specialize H0 with (1:= X); cleanup;
         eapply wp_to_exec in H1; cleanup;
         do 2 eexists; split; eauto;
         econstructor; eauto ];
       try solve [
         specialize H0 with (1:= X); cleanup;
         inversion H0; cleanup;
         eexists; split; eauto;
         eapply exec_to_wp; eauto ].
   Qed.       
     
   Theorem wcp_complete':
     forall T (p: prog' T) H C,
       (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
       (forall o s, H o s ->
               (exists s', exec' o s p (Crashed s') /\ C s')).
   Proof.
     intros; destruct p; simpl;
     split; intros;
     try solve [
         specialize H0 with (1:= X); cleanup;
         eapply wcp_to_exec in H1; cleanup;
         eexists; split; eauto;
         econstructor; eauto ];
     try solve [
         specialize H0 with (1:= X); cleanup;
         inversion H0; cleanup;
         eexists; split; eauto;
         eapply exec_to_wcp; eauto ].
   Qed.

   Theorem sp_complete':
     forall T (p: prog' T) P (Q: T -> state' -> Prop),
       (forall t s', strongest_postcondition' p P t s' -> Q t s') <->
       (forall o s s' t, P o s -> exec' o s p (Finished s' t) -> Q t s').
   Proof.
     intros; destruct p; simpl;
     split; intros;
     try solve [
           inversion H1; cleanup;
           eapply H;
           eapply exec_to_sp; simpl; eauto;
           destruct s; simpl in *; eauto ];
     try solve [
           eapply sp_to_exec in H0; cleanup;
           eapply H; eauto;
           destruct s'; simpl in *; econstructor; eauto ].
   Qed.    

   Theorem scp_complete':
     forall T (p: prog' T) P (C: state' -> Prop),
       (forall s', strongest_crash_postcondition' p P s' -> C s') <->
       (forall o s s', P o s -> exec' o s p (Crashed s') ->  C s').
Proof.
     intros; destruct p; simpl;
     split; intros;
     try solve [
           inversion H1; cleanup;
           eapply H;
           eapply exec_to_scp; simpl; eauto;
           destruct s; simpl in *; eauto ];
     try solve [
           eapply scp_to_exec in H0; cleanup;
           eapply H; eauto;
           destruct s'; simpl in *; econstructor; eauto ].
Qed.
  
  Theorem exec_deterministic_wrt_oracle' :
    forall o s T (p: prog' T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *;
    inversion H; inversion H0;
    sigT_eq; clear H H0; cleanup;
    try solve [eapply exec_deterministic_wrt_oracle in H6;
               eauto; cleanup; eauto].
  Qed.

  Hint Constructors exec': core.

  Definition HorizontalComposition :=
    Build_Operation
      oracle_dec' prog' exec'
      weakest_precondition'
      weakest_crash_precondition'
      strongest_postcondition'
      strongest_crash_postcondition'
      wp_complete' wcp_complete'
      sp_complete' scp_complete'
      exec_deterministic_wrt_oracle'.

Import Language.

Fixpoint lift_L1 {L1: Language O1} {T} (p1 : L1.(prog) T) : prog' HorizontalComposition T :=
  match p1 with
  | Op _ o1 =>
    Op HorizontalComposition (P1 _ o1)
  | Ret v =>
    Ret v
  | Bind px py =>
    Bind (@lift_L1 L1 _ px) (fun x => @lift_L1 L1 _ (py x))
  end.

Fixpoint lift_L2 {L2: Language O2} {T} (p2 : L2.(prog) T) : prog' _ T :=
  match p2 with
  | Op _ o2 =>
    Op HorizontalComposition (P2 _ o2)
  | Ret v =>
    Ret v
  | Bind px py =>
    Bind (@lift_L2 L2 _ px) (fun x => @lift_L2 L2 _ (py x))
  end.

  
End HorizontalComposition.

Arguments P1 {O1 O2 T}.
Arguments P2 {O1 O2 T}.

Notation "'<1|'  p >" := (P1 p)(right associativity, at level 60).
Notation "'<2|'  p >" := (P2 p)(right associativity, at level 60).
