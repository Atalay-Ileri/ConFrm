Require Import Primitives Layer.Operation Layer.Language.
Import ListNotations.

Set Implicit Arguments.

Section HorizontalComposition.
  Variable O1 O2 : Operation.
  Variable L1 : Language O1.
  Variable L2 : Language O2.
  
  Inductive token' :=
  | Oracle1 : L1.(oracle) -> token'
  | Oracle2 : L2.(oracle) -> token'.

  Definition oracle' := list token'.

  Definition token_dec: forall (t t': token'), {t = t'}+{t <> t'}.
   decide equality.
   apply L1.(oracle_dec).
   apply L2.(oracle_dec).
  Defined.

  Definition oracle_dec' := list_eq_dec token_dec.
  Definition state' := (L1.(state) * L2.(state))%type.

  Inductive prog' : Type -> Type :=
  | P1 : forall T, L1.(prog) T -> prog' T
  | P2 : forall T, L2.(prog) T -> prog' T.


  Inductive exec': forall T, oracle' -> state' -> prog' T -> @Result state' T -> Prop :=
  | ExecP1:
      forall T (p1: L1.(prog) T) o1 s s1 r,
        L1.(exec) o1 (fst s) p1 (Finished s1 r) ->
        exec' [Oracle1 o1] s (P1 p1) (Finished (s1, snd s) r)
  | ExecP2:
      forall T (p2: L2.(prog) T) o2 s s2 r,
        L2.(exec) o2 (snd s) p2 (Finished s2 r) ->
        exec' [Oracle2 o2] s (P2 p2) (Finished (fst s, s2) r)
  | ExecP1Crash:
      forall T (p1: L1.(prog) T) o1 s s1,
        L1.(exec) o1 (fst s) p1 (Crashed s1) ->
        exec' [Oracle1 o1] s (P1 p1) (Crashed (s1, snd s))
  | ExecP2Crash:
      forall T (p2: L2.(prog) T) o2 s s2,
        L2.(exec) o2 (snd s) p2 (Crashed s2) ->
        exec' [Oracle2 o2] s (P2 p2) (Crashed (fst s, s2)).
  
  Definition weakest_precondition' T (p: prog' T) :=
    match p with
    | P1 p1 =>
      fun Q o s =>
      exists o1,
      o = [Oracle1 o1] /\ L1.(weakest_precondition) p1 (fun r s' => Q r (s', snd s)) o1 (fst s)
    | P2 p2 =>
      fun Q o s =>
      exists o2,
      o = [Oracle2 o2] /\ L2.(weakest_precondition) p2 (fun r s' => Q r (fst s, s')) o2 (snd s)
    end.

  Definition weakest_crash_precondition' T (p: prog' T) :=
    match p with
    | P1 p1 =>
      fun Q o s =>
      exists o1,
      o = [Oracle1 o1] /\ L1.(weakest_crash_precondition) p1 (fun s' => Q (s', snd s)) o1 (fst s)
    | P2 p2 =>
      fun Q o s =>
      exists o2,
      o = [Oracle2 o2] /\ L2.(weakest_crash_precondition) p2 (fun s' => Q (fst s, s')) o2 (snd s)
    end.

   Theorem wp_complete':
      forall T (p: prog' T) H Q,
        (forall o s, H o s -> weakest_precondition' p Q o s) <->
        (forall o s, H o s ->
                (exists s' v, exec' o s p (Finished s' v) /\ Q v s')).
   Proof.
     intros; destruct p; simpl.
     {(* L1 *)
       split; intros.
       - specialize H0 with (1:= X); cleanup.
         eapply wp_to_exec in H1; cleanup.
         do 2 eexists; split; eauto.
         econstructor; eauto.
       - specialize H0 with (1:= X); cleanup.
         inversion H0; cleanup.
         eexists; split; eauto.
         eapply exec_to_wp; eauto.
     }
     {(* L2 *)
       split; intros.
       - specialize H0 with (1:= X); cleanup.
         eapply wp_to_exec in H1; cleanup.
         do 2 eexists; split; eauto.
         econstructor; eauto.
       - specialize H0 with (1:= X); cleanup.
         inversion H0; cleanup.
         eexists; split; eauto.
         eapply exec_to_wp; eauto.
     }
   Qed.
       
     
   Theorem wcp_complete':
     forall T (p: prog' T) H C,
       (forall o s, H o s -> weakest_crash_precondition' p C o s) <->
       (forall o s, H o s ->
               (exists s', exec' o s p (Crashed s') /\ C s')).
   Proof.
     intros; destruct p; simpl.
     {(* L1 *)
       split; intros.
       - specialize H0 with (1:= X); cleanup.
         eapply wcp_to_exec in H1; cleanup.
         eexists; split; eauto.
         econstructor; eauto.
       - specialize H0 with (1:= X); cleanup.
         inversion H0; cleanup.
         eexists; split; eauto.
         eapply exec_to_wcp; eauto.
     }
     {(* L2 *)
       split; intros.
       - specialize H0 with (1:= X); cleanup.
         eapply wcp_to_exec in H1; cleanup.
         eexists; split; eauto.
         econstructor; eauto.
       - specialize H0 with (1:= X); cleanup.
         inversion H0; cleanup.
         eexists; split; eauto.
         eapply exec_to_wcp; eauto.
     }
   Qed.
   
  
  Definition exec_deterministic_wrt_oracle' :
    forall o s T (p: prog' T) ret1 ret2,
      exec' o s p ret1 ->
      exec' o s p ret2 ->
      ret1 = ret2.
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
      wp_complete' wcp_complete'
      exec_deterministic_wrt_oracle'.

End HorizontalComposition.

Arguments P1 {O1 O2 L1 L2 T}.
Arguments P2 {O1 O2 L1 L2 T}.
