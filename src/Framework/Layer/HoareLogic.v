Require Export String Datatypes.
Require Import Primitives SeparationLogic Layer.Language.

Set Implicit Arguments.

Create HintDb specs.

Instance addr_eq_dec: EqDec addr := addr_dec.

Module HoareLogic (Ops: Operation).
  Module Lang := Language Ops.
  Import Ops Lang.
  Export Lang.

Definition Marker {T} (s: string) (p: prog T) := True.

(** ** Hoare logic *)
Definition pre_condition := state -> Prop.
Definition post_condition {T: Type} := T -> state -> Prop.
Definition crash_condition := state -> Prop.
Definition oracle_pre_condition {T: Type} := oracle -> prog T -> state -> Prop.
Definition oracle_post_condition {T: Type} := oracle -> state -> T -> state -> Prop.
Definition oracle_crash_condition := oracle -> state -> state -> Prop.

Definition hoare_triple {T: Type}
           (opre: @oracle_pre_condition T)
           (pre: pre_condition)
           (p: prog T)
           (post: @post_condition T)
           (crash: crash_condition)
           (opost: oracle_post_condition)
           (ocrash: oracle_crash_condition):=
  fun o s =>
    opre o p s ->
    pre s ->
    (exists ret,
        exec o s p ret /\
        ((exists s' r,
             ret = Finished s' r
             /\ post r s' /\ opost o s r s') \/
         (exists s',
             ret = Crashed s' /\ crash s' /\ ocrash o s s')))%type.

Notation
  "<< o , s >> 'PRE:' pre 'PROG:' p << r , s' >> 'POST:' post 'CRASH:' crash 'OPRE:' opre 'OPOST:' opost 'OCRASH:' ocrash" :=
  (hoare_triple
          (fun o p' s => oracle_ok p' o s /\ opre)
          (fun s => pre)
          p
          (fun r s' => post)
          (fun s' => crash)
          (fun o s r s' => opost)
          (fun o s s' => ocrash)
          o s)      
    (at level 10, o at next level, s at next level, s' at next level, opre at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level, opost at next level, ocrash at next level,
     format "'[v' '[  ' '<<' o ','  s '>>' '//' '[' 'PRE:' '//' pre ']' '//' '[' 'PROG:' '//' p ']' ']' '//' '[  ' '<<' r ','  s' '>>' '//' '[' 'POST:' '//' post ']' '//' '[' 'CRASH:' '//' crash ']' '//' '[' 'OPRE:' '//' opre ']' '//' '[' 'OPOST:' '//' opost ']' '//' '[' 'OCRASH:' '//' ocrash ']' ']' ']'").

Notation
  "<< o , s >> 'PRE:' pre 'PROG:' p << r , s' >> 'POST:' post 'CRASH:' crash" :=
  (hoare_triple
          (fun o p' s => oracle_ok p' o s)
          (fun s => pre)
          p
          (fun r s' => post)%pred
          (fun s' => crash)%pred
          (fun o s r s' => True)
          (fun o s s' => True)
          o s)      
    (at level 10, o at next level, s at next level, s' at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o ','  s '>>' '//' '[' 'PRE:' '//' pre ']' '//' '[' 'PROG:' '//' p ']' ']' '//' '[  ' '<<' r ','  s' '>>' '//' '[' 'POST:' '//' post ']' '//' '[' 'CRASH:' '//' crash ']' ']' ']'").

Theorem crash_impl:
  forall T (p: prog T) opre pre post (crash1 crash2: crash_condition) opost ocrash o s,
    hoare_triple opre pre p post crash1 opost ocrash o s -> 
    (forall s',
      Marker "crash_impl implication for" p ->
      pre s ->
      crash1 s' ->
      crash2 s') ->
    hoare_triple opre pre p post crash2 opost ocrash o s.
Proof.
  unfold Marker, hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
Qed.


Theorem post_impl:
  forall T (p: prog T) opre pre (post1 post2: post_condition) crash opost ocrash o s,
    hoare_triple opre pre p post1 crash opost ocrash o s -> 
    (forall r s',
      Marker "post_impl implication for" p ->
      pre s ->
      post1 r s' ->
      post2 r s') ->
    hoare_triple opre pre p post2 crash opost ocrash o s.
Proof.
  unfold Marker, hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
Qed.

Theorem pre_impl:
  forall T (p: prog T) opre (pre1 pre2: pre_condition) post crash opost ocrash o s,
    hoare_triple opre pre1 p post crash opost ocrash o s -> 
    ( Marker "pre_impl implication for" p ->
      pre2 s ->
      pre1 s ) ->
    hoare_triple opre pre2 p post crash opost ocrash o s.
Proof.
  unfold Marker, hoare_triple; intros.
  edestruct H; eauto.
Qed.

Theorem remove_oracle_conditions:
  forall T (p: prog T) (opre: oracle_pre_condition) pre post crash (opost: oracle_post_condition) (ocrash: oracle_crash_condition) o s,
  hoare_triple opre pre p post crash (fun _ _ _ _ => True) (fun _ _ _ => True) o s -> 
  (forall r s',
     Marker "opost for" p ->
     opre o p s ->
     pre s ->
     exec o s p (Finished s' r) ->
     post r s' ->
     opost o s r s') ->
  (forall s',
      Marker "ocrash for" p ->
      opre o p s ->
      pre s ->
      exec o s p (Crashed s') ->
      crash s' ->
      ocrash o s s') ->
   hoare_triple opre pre p post crash opost ocrash o s.
Proof.
  unfold Marker, hoare_triple; intros.
  edestruct H; eauto; cleanup.
  
  split_ors; cleanup;
    eexists; split; intuition eauto.
    left; do 2 eexists; intuition eauto.
Qed.

(*
Theorem hoare_triple_equivalence :
  forall T (p p': prog T) o s pre post crash ap ac,
    hoare_triple pre p post crash ap ac o s ->
    prog_equiv p p' ->
    hoare_triple pre p' post crash ap ac o s.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  match goal with
  | [ H: _ ~= _ |- _ ] =>
    edestruct H; eauto
  end.
  unfold exec in *.
  eauto.
Qed.

Ltac monad_simpl_one :=
  match goal with
  | [ |- hoare_triple _ (Bind (Bind _ _) _) _ _ _ _ _ _ _] =>
    eapply hoare_triple_equivalence;
    [ | apply bind_assoc ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.
*)

Theorem ret_ok:
  forall P o s T (v: T),
    << o, s >>
    PRE:
     (P s)
    PROG:
     (Ret v)
    << r, s' >>
    POST:
     (P s' /\ r = v /\ s' = s)
    CRASH:
     (P s' /\ s' = s).
Proof.
  intros.
  unfold hoare_triple; intros.
  destruct_lift H; subst.
  split_ors; eexists;
  intuition (try econstructor; eauto).
  do 2 eexists; eauto.
Qed.

Theorem bind_ok:
  forall T T' (p1: prog T) (p2: T -> prog T') (opre opre1 opre2: oracle_pre_condition) (pre1 pre2: pre_condition) post1 post2 (crash1 crash2: crash_condition) (opost opost1 opost2: oracle_post_condition) (ocrash ocrash1 ocrash2 : oracle_crash_condition) o s, 
  (forall o1,
      Marker "bind_ok spec for" p1 ->
      (exists o2, o = o1++o2) ->
      hoare_triple opre1 pre1 p1 post1 crash1 opost1 ocrash1 o1 s) ->
  (forall r s',
     Marker "bind_ok post1 -> pre2 for" (Bind p1 p2) ->
     pre1 s ->
     post1 r s' ->
     pre2 s') ->
  (forall s',
     Marker "bind_ok crash1 -> crash2 for" (Bind p1 p2) ->
     pre1 s ->
     crash1 s' -> crash2 s') ->
  (forall o1 o2 r s',
     Marker "bind_ok after" p1 ->
      opre1 o1 p1 s ->
      pre1 s ->
      post1 r s'->
      o = o1 ++ o2 ->
      exec o1 s p1 (Finished s' r) ->
      hoare_triple opre2 pre2 (p2 r) post2 crash2 opost2 ocrash2 o2 s') ->
  (Marker "bind_ok opre -> opre1 /\ opre2 for" (Bind p1 p2) ->
      opre o (Bind p1 p2) s ->
      exists o1 o2,
      o = o1++o2 /\
      opre1 o1 p1 s /\
      (forall s' r,
          exec o1 s p1 (Finished s' r) ->
          opre2 o2 (p2 r) s')) ->
  (forall o1 o2 s1 s2 r1 r2,
      Marker "bind_ok opost1 /\ opost2 -> opost for" (Bind p1 p2) ->
      o = o1++o2 ->
      opre1 o1 p1 s ->
      opost1 o1 s r1 s1 ->
      opost2 o2 s1 r2 s2 ->
      opost o s r2 s2) ->
  (forall o1 o2 s1 s2 r1,
      Marker "bind_ok opost1 /\ ocrash2 -> ocrash for" (Bind p1 p2) ->
      o = o1++o2 ->
      opre1 o1 p1 s ->
      opost1 o1 s r1 s1 ->
      ocrash2 o2 s1 s2 ->
      ocrash o s s2) ->
  (forall o1 o2 s1,
      Marker "bind_ok ocrash1 -> ocrash for" (Bind p1 p2) ->
      o = o1++o2 ->
      opre1 o1 p1 s ->
      ocrash1 o1 s s1 ->
      ocrash o s s1) ->
  hoare_triple opre pre1 (Bind p1 p2) post2 crash2 opost ocrash o s.
Proof.
  unfold Marker, hoare_triple; intros.
  simpl in *; cleanup.
  edestruct H3; eauto; cleanup.
  (* rewrite H0 in H6. *)
  edestruct H; eauto.
  
  cleanup.
  split_ors; cleanup.
  - edestruct H2; eauto.
    cleanup.
    split_ors; cleanup;
      eexists; split; eauto.
    left; do 2 eexists; repeat split; eauto.
    right; eexists; repeat split; eauto.
    
  - 
    eexists; split; eauto.
    eapply ExecBindCrash; eauto.
    cleanup.
    right; eexists; intuition eauto.
Qed.

Global Opaque Marker.

Hint Extern 1 (hoare_triple _ _ (Ret _) _ _ _ _ _ _) => eapply ret_ok : specs.
Hint Extern 1 (hoare_triple _ _ (Bind _ _) _ _ _ _ _ _) => eapply bind_ok : specs.

Local Ltac ret_step :=
  eapply post_impl;
    [eapply crash_impl;
     [eauto with specs
     |]
    |].

Local Ltac bind_step :=
  eapply bind_ok;
  [ intros;
    eapply pre_impl;
    eauto with specs
  | | |
  | instantiate (1:= fun o p s => oracle_ok p o s); simpl; intros; eauto
  | instantiate (1:= fun _ _ _ _ => True); simpl; intros; eauto
  | instantiate (1:= fun _ _ _ => True); simpl; intros; eauto
  | try solve [simpl ; intros; eauto] ].

Ltac step :=
  intros;
  match goal with
  | [ |- hoare_triple _ _ ?p _ _ _ _ _ _ ] => 
    simpl p
  end;
  match goal with
  | [ |- hoare_triple _ _ (Ret _) _ _ _ _ _ _ ] => 
    ret_step
  | [ |- hoare_triple _ _ (Bind _ _) _ _ (fun _ _ _ _ => True) (fun _ _ _ => True) _ _ ] => 
    bind_step
  | [ |- hoare_triple _ _ (Bind _ _) _ _ _ _ _ _ ] => 
    eapply remove_oracle_conditions;
    [intros; bind_step
    | try solve [ simpl; intros; eauto ]
    | try solve [ simpl; intros; eauto ] ]
  end.

End HoareLogic.
