Require Import List.

Record ParametricEquivalence (P: Type) (T: Type) :=
  {
    eq : P -> T -> T -> Prop;
    
    eq_refl: forall p t, eq p t t;
    eq_sym: forall p t t', eq p t t' -> eq p t' t;
    eq_trans: forall p t t' t'', eq p t t' -> eq p t' t'' -> eq p t t'';
  }.

Inductive Result {State T: Type} :=
| Finished : State -> T -> @Result State T
| Crashed : State -> @Result State T.

Definition extract_state {State T} (res: @Result State T) :=
  match res with
  | Finished s _ | Crashed s => s
  end.

Definition extract_ret {State T} def (res: @Result State T) :=
  match res with
  | Finished _ r => r
  | Crashed _ => def
  end.

Definition map_state {State1 State2 T} (f:State1 -> State2) (res: @Result State1 T) :=
  match res with
  | Finished s v => Finished (f s) v
  | Crashed s => Crashed (f s)
  end.

Lemma extract_state_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T),
    extract_state (map_state R r) = R (extract_state r).
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Lemma extract_ret_map_state_elim:
  forall ST1 ST2 T (R:ST1 -> ST2) (r : @Result ST1 T) def,
    extract_ret def (map_state R r) = extract_ret def r.
Proof.
  intros; destruct r; simpl; eauto.
Qed.

Definition result_same {State1 State2 T1 T2} (res1: @Result State1 T1) (res2: @Result State2 T2) :=
  match res1, res2 with
  | Finished _ _, Finished _ _ | Crashed _, Crashed _ => True
  | _, _ => False
  end.

Record Layer :=
  {
    State : Type;
    Valid : State -> Prop;
    Prog : Type -> Type;
    Exec : forall T, State -> Prog T -> @Result State T -> Prop;
    State_Equivalent : forall T, ParametricEquivalence T State;
    Result_Equivalent : forall T T', ParametricEquivalence T (@Result State T')
  }.