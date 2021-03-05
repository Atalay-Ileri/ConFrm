Require Import Primitives Layer.Core.
Require Language.
Import ListNotations.

Set Implicit Arguments.

Section HorizontalComposition.
  Variable O1 O2 : Core.
  
  Inductive token' :=
  | Token1 : O1.(token) -> token'
  | Token2 : O2.(token) -> token'.
  
  Definition state' := (O1.(state) * O2.(state))%type.
  
  Inductive horizontal_composition_prog : Type -> Type :=
  | P1 : forall T, O1.(operation) T -> horizontal_composition_prog T
  | P2 : forall T, O2.(operation) T -> horizontal_composition_prog T.


  Inductive exec': forall T, user -> token' -> state' -> horizontal_composition_prog T -> @Result state' T -> Prop :=
  | ExecP1:
      forall T (p1: O1.(operation) T) u o1 s s1 r,
        O1.(exec) u o1 (fst s) p1 (Finished s1 r) ->
        exec' u (Token1 o1) s (P1 _ p1) (Finished (s1, snd s) r)
  | ExecP2:
      forall T (p2: O2.(operation) T) u o2 s s2 r,
        O2.(exec) u o2 (snd s) p2 (Finished s2 r) ->
        exec' u (Token2 o2) s (P2 _ p2) (Finished (fst s, s2) r)
  | ExecP1Crash:
      forall T (p1: O1.(operation) T) u o1 s s1,
        O1.(exec) u o1 (fst s) p1 (Crashed s1) ->
        exec' u (Token1 o1) s (P1 _ p1) (Crashed (s1, snd s))
  | ExecP2Crash:
      forall T (p2: O2.(operation) T) u o2 s s2,
        O2.(exec) u o2 (snd s) p2 (Crashed s2) ->
        exec' u (Token2 o2) s (P2 _ p2) (Crashed (fst s, s2)).
  
  Theorem exec_deterministic_wrt_token' :
    forall u o s T (p: horizontal_composition_prog T) ret1 ret2,
      exec' u o s p ret1 ->
      exec' u o s p ret2 ->
      ret1 = ret2.
  Proof.
    intros; destruct p; simpl in *;
    inversion H; inversion H0;
    sigT_eq; clear H H0; cleanup;
    try solve [inversion H11; subst;
               eapply exec_deterministic_wrt_token in H7;
               eauto; cleanup; eauto].
  Qed.

  Hint Constructors exec': core.
  
  Definition HorizontalComposition :=
    Build_Core
      horizontal_composition_prog exec'
      exec_deterministic_wrt_token'.

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

Fixpoint lift_L2 {L2: Language O2} {T} (p2 : L2.(prog) T) : prog' HorizontalComposition T :=
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
