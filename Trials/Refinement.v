Record Equivalence (state: Type) :=
  {
    equivalent: state -> state -> Prop;
    equivalent_refl:
      forall s,
        equivalent s s;
    equivalent_sym:
      forall s s',
        equivalent s s' ->
        equivalent s' s;
    equivalent_trans:
      forall s s' s'',
        equivalent s s' ->
        equivalent s' s'' ->
        equivalent s s'';
  }.

Module Type Layer.
  Parameter state: Type.
  Parameter op: Type -> Type.
  Parameter exec_op: forall T, state -> op T -> state -> T -> Prop.
  Parameter equivalence: Equivalence state.
  
  Arguments exec_op {_}.
  
  Inductive prog : Type -> Type :=
  | Op : forall T, op T -> prog T
  | Ret : forall T, T -> prog T
  | Bind: forall T T', prog T  -> (T -> prog T') -> prog T'.
  
  Inductive exec : forall T, state -> prog T -> state -> T -> Prop :=
  | ExecOp : forall T s s' (o: op T) r,
      exec_op s o s' r ->
      exec T s (Op T o) s' r
             
  | ExecRet : forall T s (r: T),
      exec T s (Ret T r) s r
         
  | ExecBind : forall T T' (p1 : prog T) (p2: T -> prog T') s s' s'' v r,
      exec T s p1 s' v ->
      exec T' s' (p2 v) s'' r ->
      exec T' s (Bind T T' p1 p2) s'' r.
End Layer.

Module Refinement (low high: Layer).
  Parameter compile_op: forall T, high.op T -> low.prog T.
  Parameter R : low.state -> high.state -> Prop.
  
  Fixpoint compile {T} (ph: high.prog T):=
    match ph with
    | high.Op T o => compile_op T o
    | high.Ret T v => low.Ret T v
    | high.Bind T T' ph1 ph2 =>
      low.Bind T T' (compile ph1) (fun x => compile (ph2 x))
    end.

  Definition total_low := forall l, exists h, R l h.

  Definition total_high := forall h, exists l, R l h.

  
  Definition bisimulation :=
    (forall T (ph: high.prog T) l l' h r,
      low.exec T l (compile ph) l' r ->
      R l h ->
      exists h',
        high.exec T h ph h' r /\ R l' h') /\
    (forall T (ph: high.prog T) l h h' r,
      high.exec T h ph h' r ->
      R l h ->
      exists l',
        low.exec T l (compile ph) l' r /\ R l' h').
  
  Definition equivalence_preserving:=
    forall l1 l2 h1 h2,
      R l1 h1 ->
      R l2 h2 ->
      (equivalent low.state (low.equivalence)) l1 l2 <->
      (equivalent high.state (high.equivalence)) h1 h2.
  
   Definition low_independence:=
    forall T (ph: high.prog T) l1 l1' l2 r,
      low.exec T l1 (compile ph) l1' r ->
      (equivalent low.state (low.equivalence)) l1 l2 ->
      exists l2',
        low.exec T l2 (compile ph) l2' r /\
        (equivalent low.state (low.equivalence)) l1' l2'.
  
  Definition high_independence:=
    forall T (ph: high.prog T) h1 h1' h2 r,
      high.exec T h1 ph h1' r ->
      (equivalent high.state (high.equivalence)) h1 h2 ->
      exists h2',
        high.exec T h2 ph h2' r /\
        (equivalent high.state (high.equivalence)) h1' h2'.

  Theorem derive_high_independence :
    total_high ->
    weak_bisimulation ->
    equivalence_preserving ->
    low_independence ->
    high_independence.
  Proof.
    unfold total_high, weak_bisimulation,
    equivalence_preserving, low_independence,
    high_independence; intros.
    destruct H0.
    specialize (H h1) as Hx; destruct Hx.
    specialize (H h2) as Hx; destruct Hx.
    eapply H1 in H4; eauto.
    eapply H5 in H3; eauto.
    do 2 destruct H3.
    eapply H2 in H3; eauto.
    do 2 destruct H3.
    eapply H0 in H3; eauto.
    do 2 destruct H3.
    eapply H1 in H9; eauto.
  Qed.

  Theorem derive_low_independence :
    total_low ->
    weak_bisimulation ->
    equivalence_preserving ->
    high_independence ->
    low_independence.
  Proof.
    unfold total_low, weak_bisimulation,
    equivalence_preserving, low_independence,
    high_independence; intros.
    destruct H0.
    specialize (H l1) as Hx; destruct Hx.
    specialize (H l2) as Hx; destruct Hx.
    eapply H1 in H4; eauto.
    eapply H0 in H3; eauto.
    do 2 destruct H3.
    eapply H2 in H3; eauto.
    do 2 destruct H3.
    eapply H5 in H3; eauto.
    do 2 destruct H3.
    eapply H1 in H9; eauto.
  Qed.