Require Import Primitives.
Import ListNotations.

Set Implicit Arguments.

Record Operation :=
  {
    oracle : Type;
    oracle_dec: forall (o o': oracle), {o = o'}+{o <> o'};
    state : Type;
    after_crash: state -> state -> Prop;
    prog : Type -> Type;
    exec: forall T, oracle -> state -> prog T -> @Result state T -> Prop;
    weakest_precondition: forall T, prog T -> (T -> state -> Prop) -> (oracle -> state -> Prop);
    weakest_crash_precondition: forall T, prog T -> (state -> Prop) -> (oracle -> state -> Prop);
    strongest_postcondition: forall T, prog T -> (oracle -> state -> Prop) -> (T -> state -> Prop);
    strongest_crash_postcondition: forall T, prog T -> (oracle -> state -> Prop) -> (state -> Prop);

    wp_complete:
      forall T (p: prog T) P Q,
        (forall o s, P o s -> weakest_precondition p Q o s) <->
        (forall o s, P o s -> exists s' v, exec o s p (Finished s' v) /\ Q v s');
    wcp_complete:
      forall T (p: prog T) P C,
        (forall o s, P o s -> weakest_crash_precondition p C o s) <->
        (forall o s, P o s -> exists s', exec o s p (Crashed s') /\ C s');

    sp_complete:
      forall T (p: prog T) P (Q: T -> state -> Prop),
        (forall t s', strongest_postcondition p P t s' -> Q t s') <->
        (forall o s s' t, P o s -> exec o s p (Finished s' t) -> Q t s');

    scp_complete:
      forall T (p: prog T) P (C: state -> Prop),
        (forall s', strongest_crash_postcondition p P s' -> C s') <->
        (forall o s s', P o s -> exec o s p (Crashed s') ->  C s');
    
    exec_deterministic_wrt_oracle :
      forall o s T (p: prog T) ret1 ret2,
        exec o s p ret1 ->
        exec o s p ret2 ->
        ret1 = ret2;
  }.

Arguments exec _ {T}.
Arguments weakest_precondition _ {T}.
Arguments weakest_crash_precondition _ {T}.
Arguments strongest_postcondition _ {T}.
Arguments strongest_crash_postcondition _ {T}.



Lemma wp_to_exec:
  forall O T (p: @prog O T) Q o s,
    weakest_precondition _ p Q o s -> (exists s' v, exec _ o s p (Finished s' v) /\ Q v s').
Proof.
  intros. eapply wp_complete; eauto.
Qed.

Lemma exec_to_wp:
  forall O T (p: @prog O T) (Q: T -> state _ -> Prop) o s s' v,
    exec _ o s p (Finished s' v) ->
    Q v s' ->
    weakest_precondition _ p Q o s.
Proof.
  intros.
  eapply wp_complete; intros.
  apply X.
  simpl; eauto.
Qed.

Lemma wcp_to_exec:
  forall O T (p: O.(@prog) T) Q o s,
    weakest_crash_precondition _ p Q o s -> (exists s', exec _ o s p (Crashed s') /\ Q s').
Proof.
  intros. eapply wcp_complete; eauto.
Qed.
  
Lemma exec_to_wcp:
  forall O T (p: O.(@prog) T) (Q: state _ -> Prop) o s s',
    exec _ o s p (Crashed s') ->
    Q s' ->
    weakest_crash_precondition _ p Q o s.
Proof.
  intros.
  eapply wcp_complete; intros.
  apply X.
  simpl; eauto.
Qed.


Lemma sp_to_exec:
  forall O T (p: @prog O T) P t s',
    strongest_postcondition _ p P t s' -> (exists o s, exec _ o s p (Finished s' t) /\ P o s).
Proof.
  intros. edestruct sp_complete; eauto.
  instantiate (1:= fun t s' => exists (o : oracle O) (s : state O), exec O o s p (Finished s' t) /\ P o s) in H1;
  simpl in *.
  eapply H1; intros; eauto.
Qed.

Lemma exec_to_sp:
  forall O T (p: @prog O T) (P: _ -> _ -> Prop) o s t s',
    P o s ->
    exec _ o s p (Finished s' t) ->
    strongest_postcondition _ p P t s'.
Proof.
  intros. edestruct sp_complete; eauto.
  eapply H2; eauto.
Qed.

Lemma scp_to_exec:
  forall O T (p: @prog O T) P s',
    strongest_crash_postcondition _ p P s' -> (exists o s, exec _ o s p (Crashed s') /\ P o s).
Proof.
  intros. edestruct scp_complete; eauto.
  instantiate (1:= fun s' => exists (o : oracle O) (s : state O), exec O o s p (Crashed s') /\ P o s) in H1;
  simpl in *.
  eapply H1; intros; eauto.
Qed.

Lemma exec_to_scp:
  forall O T (p: @prog O T) (P: _ -> _ -> Prop) o s s',
    P o s ->
    exec _ o s p (Crashed s') ->
    strongest_crash_postcondition _ p P s'.
Proof.
  intros. edestruct scp_complete; eauto.
  eapply H2; eauto.
Qed.



Lemma sp_post:
  forall O T (p: @prog O T) (P: oracle _ -> state _ -> Prop) o s s' t,
    P o s ->
    exec _ o s p (Finished s' t) ->
    strongest_postcondition _ p P t s'.
Proof.
  intros.
  edestruct sp_complete.
  eapply H1; eauto.
Qed.

Lemma sp_strongest:
  forall O T (p: @prog O T) (P: oracle _ -> state _ -> Prop) (Q: T -> state _ -> Prop),
    (forall o s s' t,
       P o s -> 
       exec _ o s p (Finished s' t) ->
       Q t s') ->
    (forall t s', strongest_postcondition _ p P t s' -> Q t s').
Proof.
  intros.
  edestruct sp_complete.
  eapply H2; eauto.  
Qed.
