Require Import BaseTypes Mem Pred Disk CommonAutomation SepAuto.

Set Implicit Arguments.

Module Type Layer.
  Parameter oracle : Type.
  Parameter data : Type.
  Parameter prog : Type -> Type.
  Parameter exec: forall T, oracle -> disk data -> prog T -> @Result (disk data) T -> Prop.
  Parameter oracle_ok : forall T, prog T -> oracle -> disk data -> Prop.
End Layer.

Module HoareLogic (l: Layer).
  Import l.
(** ** Hoare logic *)
Definition precond := oracle -> @pred addr addr_dec data.
Definition postcond {T: Type} := T -> @pred addr addr_dec data.
Definition crashcond := @pred addr addr_dec data.
Definition augpostcond {T: Type} := oracle -> disk data -> T -> @pred addr addr_dec data.
Definition augcrashcond := oracle -> disk data -> @pred addr addr_dec data.

Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond) (augpost: augpostcond) (augcrash: augcrashcond):=
  fun o d =>
    pre o d ->
    (exists ret,
        exec o d p ret /\
        ((exists d' r,
             ret = Finished d' r
             /\ post r d' /\ augpost o d r d') \/
         (exists d',
             ret = Crashed d' /\ crash d' /\ augcrash o d d')))%type.


  
Notation
  "<< o , d >> pre p << r >> post crash" :=
  (forall F, hoare_triple
          (fun o d => (F * pre * [[ oracle_ok p o d ]]) d)%pred
          p%pred
          (fun r => F * post)%pred
          (F * crash)%pred
          (fun _ _ _ => any)
          (fun _ _ => any)
          o d)      
    (at level 10, o at next level, d at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o ','  d '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Notation
  "<< o , d >> pre p << r >> post crash augpost augcrash" :=
  (forall F, hoare_triple
          (fun o d => (F * pre * [[ oracle_ok p o d ]]) d)%pred
          p%pred
          (fun r => F * post)%pred
          (F * crash)%pred
          (fun o d r => F * augpost)%pred
          (fun o d => F * augcrash)%pred
          o d)      
    (at level 10, o at next level, d at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level, augpost at next level, augcrash at next level,
     format "'[v' '[  ' '<<' o ','  d '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r '>>' '//' '[' post ']' '//' '[' crash ']' '//' '[' augpost ']' '//' '[' augcrash ']' ']' ']'").

(*
Notation
  "{{ e1 }} << o >> pre p << r >> post crash" :=
   (exists e1, (forall F, hoare_triple
          (fun o => F * pre)%pred
          p
          (fun r => F * post)%pred
          (F * crash)%pred))
    (at level 10, o at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '{{' e1 '}}' '//' '[  ' '<<' o '>>' '//' pre '//' p ']' '//' '[  ' '<<' r '>>' '//' post '//' crash ']' ']'").
*)

Theorem remember_oracle_ok :
  forall T (p: prog T) o d pre post crash ap ac,
    (oracle_ok p o d ->
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d)) ->
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d).
Proof.
  unfold hoare_triple; intros.
  eapply H; eauto.
  destruct_lift  H0; eauto.
Qed.


Theorem crash_weaken:
  forall T (p: prog T) pre post crash1 crash2 o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash1 ->
  (crash1 =p=> crash2) ->
  << o, d >>
     pre
     p
  << r >>
     (post r)
     crash2.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  right; eexists; intuition eauto.
  clear H5; pred_apply; cancel; eauto.
Qed.


Theorem post_weaken:
  forall T (p: prog T) pre post1 post2 crash o d,
  << o, d >>
   pre
   p
  << r >>
   (post1 r)
   crash  ->
  (forall r, post1 r =p=> post2 r) ->
  << o, d >>
     pre
     p
  << r >>
     (post2 r)
     crash.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  cleanup.
  split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  clear H5; pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen:
  forall T (p: prog T) pre1 pre2 post crash o d,
  << o, d >>
   pre1
   p
  << r >>
   (post r)
   crash ->
  (pre2 =p=> pre1) ->
  << o, d >>
     pre2
     p
  << r >>
     (post r)
     crash.
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen_aug:
  forall T (p: prog T) pre1 pre2 post crash ap ac o d,
  << o, d >>
   pre1
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d) ->
  (pre2 =p=> pre1) ->
  << o, d >>
     pre2
     p
  << r >>
     (post r)
     crash
     (ap o d r)
     (ac o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.


Theorem add_frame:
  forall T (p: prog T) pre post crash F o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash  ->
  << o, d >>
     (F * pre)
     p
  << r >>
     (F * post r)
     (F * crash).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply' H0; cancel; eauto.
  cleanup; split_ors; cleanup;
    eexists; intuition eauto.
  left; do 2 eexists; intuition eauto.
  clear H4; pred_apply; cancel; eauto.
  right; eexists; intuition eauto.
  clear H4; pred_apply; cancel; eauto.
Qed.

Theorem extract_exists:
  forall T V (p: prog T) pre post crash o d,
    (forall (v:V),
  << o, d >>
   (pre v)
   p
  << r >>
   (post r)
   crash) ->
  << o, d >>
     (exists v, pre v)
     p
  << r >>
     (post r)
     crash.
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem extract_exists_aug:
  forall T V (p: prog T) pre post crash ap ac o d,
    (forall (v:V),
  << o, d >>
   (pre v)
   p
  << r >>
   (post r)
   crash
   (ap o d r)
   (ac o d)) ->
  << o, d >>
     (exists v, pre v)
     p
  << r >>
     (post r)
     crash
     (ap o d r)
     (ac o d).
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem remove_augcons:
  forall T (p: prog T) pre post crash (augpost: augpostcond) (augcrash: augcrashcond) o d,
  << o, d >>
   pre
   p
  << r >>
   (post r)
   crash ->
  (forall F d' r,
      (F * pre)%pred d ->
      exec o d p (Finished d' r) ->
      (F * post r)%pred d' ->
      (F * augpost o d r)%pred d') ->
  (forall F d',
      (F * pre)%pred d ->
      exec o d p (Crashed d') ->
      (F * crash)%pred d' ->
      (F * augcrash o d)%pred d') ->
  << o, d >>
     pre
     p
  << r >>
     (post r)
     crash
     (augpost o d r)
     (augcrash o d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto; cleanup.
  
  split_ors; cleanup.
  - 
    eexists; split; intuition eauto.
    left; do 2 eexists; intuition eauto.
    eapply H0; eauto.
    pred_apply; cancel.
    
  - 
    eexists; split; intuition eauto.
    right; eexists; intuition eauto.
    eapply H1; eauto.
    pred_apply; cancel.
Qed.

End HoareLogic.