Require Import Primitives Layer.Operation
        Layer.Language Layer.HorizontalComposition.

Local Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

  
Lemma bind_sep:
  forall O (L: Language O) T T' o d (p1: prog L T) (p2: T -> prog L T') ret,
    exec L o d (Bind p1 p2) ret ->
    match ret with
    | Finished d' r =>
    (exists o1 o2 d1 r1,
       exec L o1 d p1 (Finished d1 r1) /\
       exec L o2 d1 (p2 r1) ret /\
       o = o1++o2)
  | Crashed d' =>
    (exists o1 o2,
    o = o1++o2 /\    
    (exec L o1 d p1 (Crashed d') \/
     (exists d1 r1,
        exec L o1 d p1 (Finished d1 r1) /\
        exec L o2 d1 (p2 r1) ret)))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  do 2 eexists; split; eauto.
 Qed.

 Local Lemma lift1_invert_exec :
    forall O1 O2 (L1: Language O1) (Lc: Language (HorizontalComposition O1 O2))
      T (p1: L1.(prog) T) (o: Lc.(oracle)) s s' t,
      exec Lc o s (lift_L1 O2 p1) (Finished s' t) ->
      exists o1,
        o = map (fun o =>
                   match o with
                   |OpOracle _ o1 =>
                    OpOracle (HorizontalComposition O1 O2)
                             [Oracle1 O1 O2 o1]%list
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o1 /\
        snd s = snd s' /\
        exec L1 o1 (fst s) p1 (Finished (fst s') t).
  Proof.
    induction p1; simpl; intros.
    {      
      invert_exec'' H.
      invert_exec'' H5.      
      eexists; intuition eauto.
      simpl; eauto.
    }
    {
      invert_exec'' H.
      eexists; intuition eauto.
      2: econstructor.
      simpl; eauto.
    }
    {
      invert_exec'' H0.
      edestruct IHp1; eauto; cleanup.
      edestruct H; eauto; cleanup.
      
      eexists; intuition eauto.
      2: econstructor; eauto.
      rewrite map_app; eauto.
    }
  Qed.

    
Local Lemma lift2_invert_exec :
    forall O1 O2 (L2: Language O2) (Lc: Language (HorizontalComposition O1 O2))
      T (p2: L2.(prog) T) (o: Lc.(oracle)) s s' t,
      exec Lc o s (lift_L2 O1 p2) (Finished s' t) ->
      exists o2,
        o = map (fun o =>
                   match o with
                   |OpOracle _ o1 =>
                    OpOracle (HorizontalComposition O1 O2)
                             [Oracle2 O1 O2 o1]%list
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o2 /\
        fst s = fst s' /\
        exec L2 o2 (snd s) p2 (Finished (snd s') t).
  Proof.
    induction p2; simpl; intros.
    {
      invert_exec'' H.
      invert_exec'' H5.
      eexists; intuition eauto.
      simpl; eauto.
    }
    {
      invert_exec'' H.
      eexists; intuition eauto.
      2: econstructor.
      simpl; eauto.
    }
    {
      invert_exec'' H0.
      edestruct IHp2; eauto; cleanup.
      edestruct H; eauto; cleanup.
      
      eexists; intuition eauto.
      2: econstructor; eauto.
      rewrite map_app; eauto.
    }
  Qed.


  Local Ltac invert_exec' :=
    match goal with
    |[H : recovery_exec _ _ _ _ _ _ _ |- _ ] =>
     invert_exec'' H
    | [ H: exec _ _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => idtac
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: exec' _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => idtac
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: exec _ _ _ (lift_L1 _ _) (Finished _ _) |- _ ] =>
      eapply lift1_invert_exec in H; logic_clean
    | [ H: exec _ _ _ (lift_L2 _ _) (Finished _ _) |- _ ] =>
      eapply lift2_invert_exec in H; logic_clean
    | [ H: HorizontalComposition.exec' _ _ _ _ |- _ ] =>
      invert_exec'' H
    | [ H: Operation.exec _ _ _ _ _ |- _ ] =>
      invert_exec'' H
    end.

  Ltac invert_exec :=
  invert_exec' ||
  match goal with
  |[H : exec _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec' _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  end.
