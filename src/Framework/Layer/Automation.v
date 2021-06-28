Require Import Primitives Layer.Core
        Layer.Language Layer.HorizontalComposition.

Ltac invert_exec'' H :=
  inversion H; subst; clear H; repeat sigT_eq.

  
Lemma bind_sep:
  forall O (L: Language O) T T' u o d (p1: prog L T) (p2: T -> prog L T') ret,
    exec L u o d (Bind p1 p2) ret ->
    match ret with
    | Finished d' r =>
    (exists o1 o2 d1 r1,
       exec L u o1 d p1 (Finished d1 r1) /\
       exec L u o2 d1 (p2 r1) ret /\
       o = o1++o2)
  | Crashed d' =>
    (
    (exec L u o d p1 (Crashed d') \/
     (exists d1 r1 o1 o2,
     o = o1++o2 /\
        exec L u o1 d p1 (Finished d1 r1) /\
        exec L u o2 d1 (p2 r1) ret)))
    end.
Proof.
  intros.
  invert_exec'' H; eauto.
  destruct ret.
  do 2 eexists; eauto.
  right; do 4 eexists; intuition eauto.
 Qed.

Lemma lift1_invert_exec :
    forall O1 O2 (L1: Language O1) (Lc: Language (HorizontalComposition O1 O2))
      T (p1: L1.(prog) T) (o: Lc.(oracle)) u s s' t,
      exec Lc u o s (lift_L1 O2 p1) (Finished s' t) ->
      exists o1,
        o = map (fun o =>
                   match o with
                   |OpToken _ o1 =>
                    OpToken (HorizontalComposition O1 O2)
                             (Token1 O1 O2 o1)
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o1 /\
        snd s = snd s' /\
        exec L1 u o1 (fst s) p1 (Finished (fst s') t).
  Proof.
    induction p1; simpl; intros.
    {      
      invert_exec'' H.
      invert_exec'' H6.      
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

    
Lemma lift2_invert_exec :
    forall O1 O2 (L2: Language O2) (Lc: Language (HorizontalComposition O1 O2))
      T (p2: L2.(prog) T) (o: Lc.(oracle)) u s s' t,
      exec Lc u o s (lift_L2 O1 p2) (Finished s' t) ->
      exists o2,
        o = map (fun o =>
                   match o with
                   |OpToken _ o1 =>
                    OpToken (HorizontalComposition O1 O2)
                             (Token2 O1 O2 o1)
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o2 /\
        fst s = fst s' /\
        exec L2 u o2 (snd s) p2 (Finished (snd s') t).
  Proof.
    induction p2; simpl; intros.
    {
      invert_exec'' H.
      invert_exec'' H6.
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


  Lemma lift2_exec_step :
    forall O1 O2 (L2: Language O2) (Lc: Language (HorizontalComposition O1 O2))
      T (p2: L2.(prog) T) o u s s' t fs,
      exec L2 u o s p2 (Finished s' t) ->
      exec Lc u (map (fun o =>
      match o with
      |OpToken _ o1 =>
       OpToken (HorizontalComposition O1 O2)
                (Token2 O1 O2 o1)
      |Language.Cont _ =>
       Language.Cont _
      |Language.Crash _ =>
       Language.Crash _
      end) o) (fs, s) (lift_L2 O1 p2) (Finished (fs, s') t).
       
  Proof.
    induction p2; simpl; intros.
    {
      invert_exec'' H.
      simpl.
      repeat econstructor; eauto.
    }
    {
      invert_exec'' H; simpl.
      repeat econstructor; eauto.
    }
    {
      invert_exec'' H0.
      eapply IHp2 in H7.
      eapply H in H10.
      rewrite map_app; repeat econstructor; eauto.
    }
  Qed.


  Lemma lift2_exec_step_crashed :
  forall O1 O2 (L2: Language O2) (Lc: Language (HorizontalComposition O1 O2))
    T (p2: L2.(prog) T) o u s s' fs,
    exec L2 u o s p2 (Crashed s') ->
    exec Lc u (map (fun o =>
    match o with
    |OpToken _ o1 =>
     OpToken (HorizontalComposition O1 O2)
              (Token2 O1 O2 o1)
    |Language.Cont _ =>
     Language.Cont _
    |Language.Crash _ =>
     Language.Crash _
    end) o) (fs, s) (lift_L2 O1 p2) (Crashed (fs, s')).
     
Proof.
  induction p2; simpl; intros.
  {
    invert_exec'' H.
    simpl.
    repeat econstructor; eauto.
  }
  {
    invert_exec'' H; simpl.
    repeat econstructor; eauto.
  }
  {
    invert_exec'' H0.
    eapply lift2_exec_step in H7; eauto.
    eapply H in H10.
    rewrite map_app; repeat econstructor; eauto.
    eapply H7.

    eapply IHp2 in H6.
    eapply ExecBindCrash; repeat econstructor; eauto.
  }
  Unshelve.
  eauto.
Qed.


Lemma lift1_invert_exec_crashed :
    forall O1 O2 (L1: Language O1) (Lc: Language (HorizontalComposition O1 O2))
      T (p1: L1.(prog) T) (o: Lc.(oracle)) u s s',
      exec Lc u o s (lift_L1 O2 p1) (Crashed s') ->
      exists o1,
        o = map (fun o =>
                   match o with
                   |OpToken _ o1 =>
                    OpToken (HorizontalComposition O1 O2)
                             (Token1 O1 O2 o1)
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o1 /\
        snd s = snd s' /\
        exec L1 u o1 (fst s) p1 (Crashed (fst s')).
  Proof.
    induction p1; simpl; intros.
    {      
      invert_exec'' H.
      invert_exec'' H6.      
      do 2 eexists; intuition eauto.
      2: simpl; constructor; eauto.
      simpl; eauto.
    }
    {
      invert_exec'' H.
      do 2 eexists; intuition eauto.
      2: econstructor.
      simpl; eauto.
    }
    {
      invert_exec'' H0.
      eapply lift1_invert_exec in H7; cleanup.
      edestruct H; eauto; cleanup.
      
      eexists; split.
      2: split; eauto; econstructor; eauto.
      rewrite map_app; eauto.

      edestruct IHp1; eauto; cleanup.
      do 2 eexists; intuition eauto.
      solve [econstructor; eauto].
    }
    Unshelve.
    eauto.
  Qed.

    
Lemma lift2_invert_exec_crashed :
    forall O1 O2 (L2: Language O2) (Lc: Language (HorizontalComposition O1 O2))
      T (p2: L2.(prog) T) (o: Lc.(oracle)) u s s',
      exec Lc u o s (lift_L2 O1 p2) (Crashed s') ->
      exists o2,
        o = map (fun o =>
                   match o with
                   |OpToken _ o1 =>
                    OpToken (HorizontalComposition O1 O2)
                             (Token2 O1 O2 o1)
                   |Language.Cont _ =>
                    Language.Cont _
                   |Language.Crash _ =>
                    Language.Crash _
                   end) o2 /\
        fst s = fst s' /\
        exec L2 u o2 (snd s) p2 (Crashed (snd s')).
  Proof.
    induction p2; simpl; intros.
    {      
      invert_exec'' H.
      invert_exec'' H6.      
      do 2 eexists; intuition eauto.
      2: simpl; constructor; eauto.
      simpl; eauto.
    }
    {
      invert_exec'' H.
      do 2 eexists; intuition eauto.
      2: econstructor.
      simpl; eauto.
    }
    {
      invert_exec'' H0.
      eapply lift2_invert_exec in H7; cleanup.
      edestruct H; eauto; cleanup.
      
      eexists; split.
      2: split; eauto; econstructor; eauto.
      rewrite map_app; eauto.

      edestruct IHp2; eauto; cleanup.
      do 2 eexists; intuition eauto.
      solve [econstructor; eauto].
    }
    Unshelve.
    eauto.
  Qed.


  Ltac invert_exec' :=
    match goal with
    |[H : recovery_exec _ _ _ _ _ _ _ _ |- _ ] =>
     invert_exec'' H
    | [ H: exec _ _ _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => fail
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: exec' _ _ _ ?p _ |- _ ] =>
      match p with
      | Bind _ _ => fail
      | Op _ _ => invert_exec'' H
      | Ret _ => invert_exec'' H
      end
    | [ H: exec _ _ _ _ (lift_L1 _ _) (Finished _ _) |- _ ] =>
      eapply lift1_invert_exec in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L2 _ _) (Finished _ _) |- _ ] =>
      eapply lift2_invert_exec in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L1 _ _) (Crashed _) |- _ ] =>
      eapply lift1_invert_exec_crashed in H; logic_clean
    | [ H: exec _ _ _ _ (lift_L2 _ _) (Crashed _) |- _ ] =>
      eapply lift2_invert_exec_crashed in H; logic_clean
    | [ H: exec' _ _ _ (lift_L1 _ _) (Finished _ _) |- _ ] =>
      eapply lift1_invert_exec in H; logic_clean
    | [ H: exec' _ _ _ (lift_L2 _ _) (Finished _ _) |- _ ] =>
      eapply lift2_invert_exec in H; logic_clean
    | [ H: exec' _ _ _ (lift_L1 _ _) (Crashed _) |- _ ] =>
      eapply lift1_invert_exec_crashed in H; logic_clean
    | [ H: exec' _ _ _ (lift_L2 _ _) (Crashed _) |- _ ] =>
      eapply lift2_invert_exec_crashed in H; logic_clean
    | [H: exec' _ _ _ (Op _ (P1 _)) _ |- _ ]=>
        invert_exec'' H
    | [H: exec' _ _ _ (Op _ (P2 _)) _ |- _ ]=>
        invert_exec'' H
    | [ H: HorizontalComposition.exec' _ _ _ _ _ |- _ ] =>
      invert_exec'' H
    | [ H: Core.exec _ _ _ _ _ _ |- _ ] =>
      invert_exec'' H
    end.

  Ltac invert_exec :=
  invert_exec' +
  match goal with
  |[H : exec _ _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  |[H : exec' _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup
  end.

  Ltac invert_exec_no_match :=
  invert_exec' +
  match goal with
  |[H : exec _ _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup_no_match
  |[H : exec' _ _ _ (Bind _ _) _ |- _ ] =>
   apply bind_sep in H; repeat cleanup_no_match
  end.

  Ltac unify_execs :=
    match goal with
    |[H : recovery_exec ?u ?x ?y ?z ?a ?b ?c _,
      H0 : recovery_exec ?u ?x ?y ?z ?a ?b ?c _ |- _ ] =>
     eapply recovery_exec_deterministic_wrt_reboot_state in H; [| apply H0]
    | [ H: exec ?u ?x ?y ?z ?a _,
        H0: exec ?u ?x ?y ?z ?a _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec' ?u ?x ?y ?z _,
        H0: exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    | [ H: exec _ ?u ?x ?y ?z _,
        H0: Language.exec' ?u ?x ?y ?z _ |- _ ] =>
      eapply exec_deterministic_wrt_oracle in H; [| apply H0]
    end.

Lemma bind_reorder:
  forall O (L: Language O) T  
  (p1: prog L T) T' (p2: T -> prog L T') 
  T'' (p3: T' -> prog L T'') 
  u o s r,
      exec L u o s (Bind p1 (fun t => Bind (p2 t) p3)) r <->
      exec L u o s (Bind (Bind p1 p2) p3) r.
Proof.
  intros; split; intros.
  {
    repeat invert_exec.
    {
      rewrite app_assoc.
      repeat econstructor; eauto.
    }
    split_ors; cleanup; 
    repeat invert_exec.
    {
    repeat eapply ExecBindCrash; eauto.
    }
    split_ors; cleanup; 
    repeat invert_exec.
    {
      eapply ExecBindCrash.
      econstructor; eauto.
    }
    {
      rewrite app_assoc.
      repeat econstructor; eauto.
    }
  }
  {
    repeat invert_exec.
    {
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    }
    split_ors; cleanup; 
    repeat invert_exec.
    split_ors; cleanup; 
    repeat invert_exec.
    {
    repeat eapply ExecBindCrash; eauto.
    }
    {
      eapply ExecBind; eauto.
      eapply ExecBindCrash; eauto.
    }
    {
      rewrite <- app_assoc.
      repeat econstructor; eauto.
    }
  }
Qed.