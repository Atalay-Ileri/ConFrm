Require Import BaseTypes Mem Pred Disk CommonAutomation SepAuto.

Set Implicit Arguments.

Module Type Layer.
  Parameter oracle : Type.
  Parameter data : Type.
  Parameter aux_state : Type.
  Definition state := (aux_state * disk data)%type.
  Parameter prog : Type -> Type.
  Parameter exec: forall T, oracle -> state -> prog T -> @Result state T -> Prop.
  Parameter oracle_ok : forall T, prog T -> oracle -> state -> Prop.
End Layer.

Instance addr_eq_dec: EqDec addr := addr_dec.

Module HoareLogic (l: Layer).
  Import l.
(** ** Hoare logic *)
Definition precond := oracle -> aux_state -> @pred addr addr_dec data.
Definition postcond {T: Type} := T -> aux_state -> @pred addr addr_dec data.
Definition crashcond := aux_state -> @pred addr addr_dec data.
Definition augpostcond {T: Type} := oracle -> aux_state -> disk data -> T -> @pred addr addr_dec data.
Definition augcrashcond := oracle -> aux_state -> disk data -> @pred addr addr_dec data.

Definition hoare_triple {T: Type} (pre: precond) (p: prog T) (post: @postcond T) (crash: crashcond) (augpost: augpostcond) (augcrash: augcrashcond):=
  fun o d xs =>
    pre o xs d ->
    (exists ret,
        exec o (xs, d) p ret /\
        ((exists d' r,
             ret = Finished d' r
             /\ post r (fst d') (snd d') /\ augpost o xs d r (snd d')) \/
         (exists d',
             ret = Crashed d' /\ crash (fst d') (snd d') /\ augcrash o xs d (snd d'))))%type.
  
Notation
  "<< o , d , xs >> pre p << r , xsr >> post crash" :=
  (forall F, hoare_triple
          (fun o xs d => (F * pre * [[ oracle_ok p o (xs, d) ]]) d)%pred
          p%pred
          (fun r xsr => F * post)%pred
          (fun xsr => F * crash)%pred
          (fun _ _ _ _ => any)
          (fun _ _ _ => any)
          o d xs)      
    (at level 10, o at next level, d at next level, xs at next level, xsr at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level,
     format "'[v' '[  ' '<<' o ','  d ','  xs '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r ','  xsr '>>' '//' '[' post ']' '//' '[' crash ']' ']' ']'").

Notation
  "<< o , d , xs >> pre p << r , xsr >> post crash augpost augcrash" :=
  (forall F, hoare_triple
          (fun o xs d => (F * pre * [[ oracle_ok p o (xs, d) ]]) d)%pred
          p%pred
          (fun r xsr => F * post)%pred
          (fun xsr => F * crash)%pred
          (fun o xs d r  => F * augpost)%pred
          (fun o xs d => F * augcrash)%pred
          o d xs)      
    (at level 10, o at next level, d at next level, xs at next level, xsr at next level, pre at next level, p at next level, r at next level, post at next level, crash at next level, augpost at next level, augcrash at next level,
     format "'[v' '[  ' '<<' o ','  d ','  xs '>>' '//' '[' pre ']' '//' '[' p ']' ']' '//' '[  ' '<<' r ','  xsr '>>' '//' '[' post ']' '//' '[' crash ']' '//' '[' augpost ']' '//' '[' augcrash ']' ']' ']'").

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
  forall T (p: prog T) o d a pre post crash (ap: augpostcond) ac,
 (oracle_ok p o (a, d) ->
  << o, d, a >>
   (pre o a)
   p
  << r, ar >>
   (post r ar)
   (crash ar)
   (ap o a d r)
   (ac o a d)) ->
  << o, d, a >>
   (pre o a)
   p
  << r, ar >>
   (post r ar)
   (crash ar)
   (ap o a d r)
   (ac o a d).
Proof.
  unfold hoare_triple; intros.
  eapply H; eauto.
  destruct_lift  H0; eauto.
Qed.


Theorem crash_weaken:
  forall T (p: prog T) pre post crash1 crash2 o d a,
  << o, d, a >>
   (pre a)
   p
  << r, ar >>
   (post r ar)
   (crash1 ar) ->
  (forall ar, crash1 ar =*=> crash2 ar) ->
  << o, d, a >>
     (pre a)
     p
  << r, ar >>
     (post r ar)
     (crash2 ar).
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
  forall T (p: prog T) pre post1 post2 crash o d a,
  << o, d, a >>
   (pre a)
   p
  << r, ar >>
   (post1 r ar)
   (crash ar)  ->
  (forall r ar, post1 r ar =*=> post2 r ar) ->
  << o, d, a >>
     (pre a)
     p
  << r, ar >>
     (post2 r ar)
     (crash ar).
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
  forall T (p: prog T) pre1 pre2 post crash o d a,
  << o, d, a >>
   (pre1 a)
   p
  << r, ar >>
   (post r ar)
   (crash ar) ->
  (pre2 a =*=> pre1 a) ->
  << o, d, a >>
     (pre2 a)
     p
  << r, ar >>
     (post r ar)
     (crash ar).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.

Theorem pre_strengthen_aug:
  forall T (p: prog T) pre1 pre2 post crash ap ac o d a,
  << o, d, a >>
   (pre1 a)
   p
  << r, ar >>
   (post r ar)
   (crash ar)
   (ap o a d r)
   (ac o a d) ->
  (pre2 a =*=> pre1 a ) ->
  << o, d, a >>
     (pre2 a)
     p
  << r, ar >>
     (post r ar)
     (crash ar)
     (ap o a d r)
     (ac o a d).
Proof.
  unfold hoare_triple; intros.
  edestruct H; eauto.
  pred_apply; cancel; eauto.
Qed.


Theorem add_frame:
  forall T (p: prog T) pre post crash F o d a,
  << o, d, a >>
   (pre a)
   p
  << r, ar >>
   (post r ar)
   (crash ar)  ->
  << o, d, a >>
     (F * pre a)
     p
  << r, ar >>
     (F * post r ar)
     (F * crash ar).
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
  forall T V (p: prog T) pre post crash o d a,
    (forall (v:V),
  << o, d, a >>
   (pre a v)
   p
  << r, ar >>
   (post r ar)
   (crash ar)) ->
  << o, d, a >>
     (exists* v, pre a v)
     p
  << r, ar >>
     (post r ar)
     (crash ar).
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem extract_exists_aug:
  forall T V (p: prog T) pre post crash ap ac o d a,
    (forall (v:V),
  << o, d, a >>
   (pre a v)
   p
  << r, ar >>
   (post r ar)
   (crash ar)
   (ap o a d r)
   (ac o a d)) ->
  << o, d, a >>
     (exists* v, pre a v)
     p
  << r, ar >>
     (post r ar)
     (crash ar)
     (ap o a d r)
     (ac o a d).
Proof.
  unfold hoare_triple; intros.
  destruct_lifts.
  eapply H; eauto.
  pred_apply' H0; cancel; eauto.
Qed.

Theorem remove_augcons:
  forall T (p: prog T) pre post crash (augpost: augpostcond) (augcrash: augcrashcond) o d a,
  << o, d, a >>
   (pre a)
   p
  << r, ar >>
   (post r ar)
   (crash ar) ->
  (forall F d' r,
      (F * pre a)%pred d ->
      exec o (a, d) p (Finished d' r) ->
      (F * post r (fst d'))%pred (snd d') ->
      (F * augpost o a d r)%pred (snd d')) ->
  (forall F d',
      (F * pre a)%pred d ->
      exec o (a, d) p (Crashed d') ->
      (F * crash (fst d'))%pred (snd d') ->
      (F * augcrash o a d)%pred (snd d')) ->
  << o, d, a >>
     (pre a)
     p
  << r, ar >>
     (post r ar)
     (crash ar)
     (augpost o a d r)
     (augcrash o a d).
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